#!/usr/bin/env python3
"""Pin inputs, compile serially twice, and inspect ARM objects without execution.

Only Python's standard library is used, inside reproduce.sh's no-pip venv.
All generated files live in the isolated unit environment. A nonzero compiler,
linker, inspection, or comparison result fails the run and is recorded verbatim.
"""
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import shlex
import struct
import subprocess
import sys
import tarfile

FIXTURE = Path(__file__).resolve().parent
INPUTS = json.loads((FIXTURE / "inputs.json").read_text())
ENV = Path(sys.argv[1]).resolve()
if ENV.parent != Path("/home/charles/code/friends/.toolchains") or not ENV.name.startswith("e04-freertos-build"):
    raise SystemExit("Refusing to write outside the isolated e04 environment")
if sys.prefix == sys.base_prefix:
    raise SystemExit("Run reproduce.sh to use the isolated venv")
resource.setrlimit(resource.RLIMIT_AS, (8_000_000_000, 8_000_000_000))
os.environ.update(LC_ALL="C", TZ="UTC", SOURCE_DATE_EPOCH="1715904000")
# Avoid caller include/library variables changing the pinned build.
for key in ("CPATH", "C_INCLUDE_PATH", "CPLUS_INCLUDE_PATH", "LIBRARY_PATH", "GCC_EXEC_PREFIX", "COMPILER_PATH"):
    os.environ.pop(key, None)
DOWNLOADS = ENV / "downloads"
DOWNLOADS.mkdir(exist_ok=True)
LOGS = ENV / "logs"
LOGS.mkdir(exist_ok=True)
run_name = sys.argv[2] if len(sys.argv) == 3 else "build"
if not run_name.replace("-", "").replace("_", "").isalnum():
    raise SystemExit("Invalid run name")
LOG = LOGS / (run_name + ".log")
COMMANDS = LOGS / (run_name + "-commands.jsonl")
if LOG.exists() or COMMANDS.exists():
    raise SystemExit("Refusing to overwrite existing run logs; use a new run name")
LOG.write_text("")
COMMANDS.write_text("")


def run(args, cwd=ENV):
    args = [str(a) for a in args]
    command = shlex.join(args)
    print("+ " + command, flush=True)
    p = subprocess.run(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    output = p.stdout.decode("utf-8", errors="replace")
    with LOG.open("a") as f:
        f.write(f"cwd: {cwd}\n$ {command}\n{output}\nexit: {p.returncode}\n\n")
    with COMMANDS.open("a") as f:
        f.write(json.dumps(dict(cwd=str(cwd), argv=args, exit=p.returncode)) + "\n")
    if p.returncode:
        print(output, file=sys.stderr)
        raise SystemExit(p.returncode)
    return output


def digest(path):
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def obtain(spec):
    path = DOWNLOADS / spec["archive"]
    if not path.exists():
        temp = path.with_suffix(path.suffix + ".part")
        run(["curl", "--fail", "--location", "--retry", "2", "--max-time", "600",
             spec["url"], "-o", temp])
        if digest(temp) != spec["sha256"]:
            raise SystemExit(f"Checksum mismatch: {temp}")
        temp.rename(path)
    if digest(path) != spec["sha256"]:
        raise SystemExit(f"Checksum mismatch: {path}")
    run(["sha256sum", path])
    return path


def extract(archive, destination):
    destination.mkdir(parents=True, exist_ok=True)
    # These are checksummed official archives; reject traversal regardless.
    with tarfile.open(archive) as tar:
        for member in tar.getmembers():
            target = (destination / member.name).resolve()
            if not target.is_relative_to(destination.resolve()):
                raise SystemExit("Unsafe archive path")
        # The pinned compiler contains relative symlinks. Extraction is local.
        tar.extractall(destination)


def save_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def build(label, source_archive, toolchain):
    work = ENV / label
    if work.exists():
        raise SystemExit(f"Refusing to overwrite {work}; use a new run name")
    work.mkdir()
    source_parent = work / "source"
    extract(source_archive, source_parent)
    kernel = source_parent / INPUTS["kernel"]["directory"]
    out = work / "out"
    out.mkdir()
    prefix = toolchain / "bin" / "arm-none-eabi-"

    def tool(name):
        return str(prefix) + name

    flags = ["-mcpu=cortex-m0", "-mthumb", "-mfloat-abi=soft", "-std=c11", "-O1",
             "-g3", "-gdwarf-4", "-gno-record-gcc-switches", "-ffreestanding",
             "-fno-builtin", "-fno-common", "-fno-lto", "-fno-inline",
             "-fno-ipa-cp", "-fno-ipa-sra", "-fno-optimize-sibling-calls",
             "-fkeep-static-functions", "-ffunction-sections", "-fdata-sections",
             "-Wall", "-Wextra", "-Werror",
             f"-ffile-prefix-map={ENV}=/e04",
             f"-ffile-prefix-map={FIXTURE}=/fixture",
             f"-ffile-prefix-map={kernel}=/kernel",
             f"-ffile-prefix-map={out}=/build",
             "-I" + str(FIXTURE), "-I" + str(kernel / "include"),
             "-I" + str(kernel / "portable/GCC/ARM_CM0")]
    sources = [kernel / n for n in ("list.c", "tasks.c", "queue.c", "event_groups.c",
                                   "stream_buffer.c", "timers.c",
                                   "portable/GCC/ARM_CM0/port.c",
                                   "portable/GCC/ARM_CM0/portasm.c")]
    sources.append(FIXTURE / "platform.c")
    (out / "config-macros.txt").write_text(run(
        [tool("gcc"), *flags, "-dM", "-E", "-include", "FreeRTOS.h", "-x", "c", "/dev/null"], cwd=out))
    objects = []
    origins = {}
    for source in sources:
        obj = out / (source.stem + ".o")
        run([tool("gcc"), *flags, "-c", source, "-o", obj], cwd=out)
        objects.append(obj)
        origin = str(source.relative_to(kernel)) if source.is_relative_to(kernel) else "platform.c"
        for line in run([tool("readelf"), "-sW", obj]).splitlines():
            fields = line.split()
            if len(fields) == 8 and fields[3] in ("FUNC", "OBJECT") and fields[6] != "UND":
                origins.setdefault(fields[7], []).append(origin)
    elf = out / "FreeRTOS-Cortex-M0.elf"
    run([tool("gcc"), "-mcpu=cortex-m0", "-mthumb", "-mfloat-abi=soft",
         "-nostartfiles", "-nostdlib", "-Wl,--build-id=none", "-Wl,--fatal-warnings",
         "-T", FIXTURE / "fixture.ld", "-Wl,-Map=" + str(out / "firmware.map"),
         *objects, "-Wl,--start-group", "-lc", "-lgcc", "-Wl,--end-group", "-o", elf], cwd=out)

    # Raw tables contain only compiler-evaluated sizeof/offsetof constants.
    layout = {}
    for unit in ("tasks", "queue", "event_groups", "stream_buffer", "timers"):
        obj = out / (unit + "-layout.o")
        raw = out / (unit + "-layout.raw")
        run([tool("gcc"), *flags, "-I" + str(kernel), "-DPROBE_" + unit,
             "-c", FIXTURE / "layout-probe.c", "-o", obj], cwd=out)
        run([tool("objcopy"), "-O", "binary", "--only-section=.picinae_layout", obj, raw])
        data = raw.read_bytes()
        assert data and len(data) % 84 == 0
        for offset in range(0, len(data), 84):
            name, value = struct.unpack_from("<80sI", data, offset)
            name = name.split(b"\0")[0].decode("ascii")
            assert name not in layout
            layout[name] = value
    for private, public in (("TCB_t", "StaticTask_t"), ("Queue_t", "StaticQueue_t"),
                            ("EventGroup_t", "StaticEventGroup_t"),
                            ("StreamBuffer_t", "StaticStreamBuffer_t"), ("Timer_t", "StaticTimer_t")):
        assert layout[private + ".sizeof"] == layout[public + ".sizeof"]
    save_json(out / "layout.json", layout)

    for name, args in {
        "elf-header.txt": ["readelf", "-hW", elf],
        "attributes.txt": ["readelf", "-AW", elf],
        "sections.txt": ["readelf", "-SW", elf],
        "symbols.txt": ["readelf", "-sW", elf],
        "program-headers.txt": ["readelf", "-lW", elf],
        "disassembly.txt": ["objdump", "-d", "-w", elf],
        "nm.txt": ["nm", "-nS", "--defined-only", elf],
        "size.txt": ["size", "-A", elf],
    }.items():
        (out / name).write_text(run([tool(args[0]), *args[1:]]))
    assert not run([tool("nm"), "--undefined-only", elf]).strip(), "Unresolved ELF symbols"
    header = (out / "elf-header.txt").read_text()
    attributes = (out / "attributes.txt").read_text()
    assert "Machine:                           ARM" in header
    assert "little endian" in header and "ELF32" in header
    assert "Tag_CPU_arch: v6S-M" in attributes
    assert "Tag_THUMB_ISA_use: Thumb-1" in attributes
    assert "Tag_CPU_arch_profile: Microcontroller" in attributes
    assert "Tag_ARM_ISA_use: Yes" not in attributes
    disassembly = (out / "disassembly.txt").read_text()
    assert "<unknown>" not in disassembly and "undefined" not in disassembly
    # Respect objdump's ARM mapping symbols: literal pools are data, not instructions.
    wide = {}
    instruction_count = 0
    for line in disassembly.splitlines():
        match = re.match(r"\s*[0-9a-f]+:\s+([0-9a-f]{4}(?: [0-9a-f]{4})?)\s+([^\s]+)", line)
        if not match or match[2].startswith("."):
            continue
        instruction_count += 1
        if " " in match[1]:
            mnemonic = match[2]
            assert mnemonic in {"bl", "mrs", "msr", "dmb", "dsb", "isb"}, (line, mnemonic)
            wide[mnemonic] = wide.get(mnemonic, 0) + 1
    assert instruction_count > 0
    mapping_symbols = (out / "symbols.txt").read_text()
    assert not re.search(r"\s\$a(?:\.|\s|$)", mapping_symbols), "ARM-state mapping symbol"
    run([tool("objcopy"), "-O", "binary", elf, out / "firmware.bin"])
    # .text includes read-only data and literal pools; .data includes initializers.
    for section in (".text", ".data", ".isr_vector"):
        run([tool("objcopy"), "-O", "binary", "--only-section=" + section,
             elf, out / (section[1:] + ".raw")])

    symbols = []
    for line in (out / "symbols.txt").read_text().splitlines():
        fields = line.split()
        if len(fields) == 8 and fields[3] in ("FUNC", "OBJECT") and fields[6] != "UND":
            value = int(fields[1], 16)
            symbols.append(dict(name=fields[7], value=f"0x{value:08x}",
                                address=f"0x{value & ~1 if fields[3] == 'FUNC' else value:08x}",
                                size=int(fields[2]), kind=fields[3], binding=fields[4], section=fields[6],
                                source=origins.get(fields[7], ["toolchain runtime (see firmware.map)"])))
            if fields[3] == "FUNC":
                assert value & 1, f"Non-Thumb function: {line}"
    save_json(out / "symbols.json", symbols)
    save_json(out / "isa-audit.json", dict(
        elf_machine="ARM", elf_class="ELF32", endian="little", cpu_arch="v6S-M",
        cpu_profile="Microcontroller", thumb_isa="Thumb-1", arm_state_mapping_symbols=0,
        all_function_entries_have_thumb_bit=True, decoded_instructions=instruction_count,
        wide_instruction_counts=wide, unknown_instructions=0,
        evidence="readelf attributes + mapping symbols + objdump; no execution or correctness proof"))

    vectors = struct.unpack("<16I", (out / "isr_vector.raw").read_bytes())
    function_values = {s["name"]: int(s["value"], 16) for s in symbols if s["kind"] == "FUNC"}
    assert vectors[0] == 0x20010000
    for index, name in ((1, "Reset_Handler"), (11, "SVC_Handler"),
                        (14, "PendSV_Handler"), (15, "SysTick_Handler")):
        assert vectors[index] == function_values[name]
    names = {s["name"] for s in symbols if s["kind"] == "FUNC" and s["size"] > 0}
    planned = (FIXTURE / "planned-symbols.txt").read_text().splitlines()
    availability = {}
    for line in planned:
        if not line or line.startswith("#"):
            continue
        unit, *candidates = line.split()
        availability[unit] = {name: name in names for name in candidates}
        assert any(name in names for name in candidates), f"Missing planned function: {line}"
    save_json(out / "planned-availability.json", availability)
    gated = {}
    for line in (FIXTURE / "gated-symbols.txt").read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        name, reason = line.split(maxsplit=1)
        gated[name] = dict(present=name in names, reason=reason)
        assert name not in names, f"Unexpected config-gated entry: {name}"
    save_json(out / "gated-availability.json", gated)

    libraries = [Path(run([tool("gcc"), "-mcpu=cortex-m0", "-mthumb", "-print-file-name=" + n]).strip()).resolve()
                 for n in ("libc.a", "libgcc.a")]
    binaries = [toolchain / "bin" / ("arm-none-eabi-" + n) for n in ("gcc", "as", "ld", "objcopy", "objdump", "readelf", "nm")]
    binaries.append(Path(run([tool("gcc"), "-print-prog-name=cc1"]).strip()))
    manifest = dict(
        inputs=INPUTS, compiler_version=run([tool("gcc"), "--version"]),
        multilib=run([tool("gcc"), "-mcpu=cortex-m0", "-mthumb", "-print-multi-directory"]).strip(),
        linker_version=run([tool("ld"), "--version"]),
        licenses={"kernel/LICENSE.md": digest(kernel / "LICENSE.md"),
                  "toolchain/license.txt": digest(toolchain / "license.txt")},
        tools={str(p.relative_to(toolchain)): digest(p) for p in binaries + libraries},
        artifacts={p.name: digest(p) for p in sorted(out.iterdir()) if p.is_file()},
        source_files={str(p.relative_to(kernel)): digest(p) for p in sorted(kernel.rglob("*")) if p.is_file()},
        fixture_files={p.name: digest(p) for p in sorted(FIXTURE.iterdir()) if p.is_file()},
        assumptions="N/A: binary-only engineering fixture; no theorem or lift produced",
        target_execution="none")
    save_json(out / "manifest.json", manifest)
    return out


source_archive = obtain(INPUTS["kernel"])
compiler_archive = obtain(INPUTS["toolchain"])
toolchain = ENV / INPUTS["toolchain"]["directory"]
if not toolchain.exists():
    extract(compiler_archive, ENV)

a = build(run_name + "-a", source_archive, toolchain)
b = build(run_name + "-b", source_archive, toolchain)
comparison = {}
for name in ("FreeRTOS-Cortex-M0.elf", "firmware.bin", "text.raw", "data.raw", "isr_vector.raw",
             "layout.json", "symbols.json", "planned-availability.json", "gated-availability.json", "isa-audit.json"):
    run(["cmp", a / name, b / name])
    comparison[name] = {"sha256": digest(a / name), "identical": True}
save_json(ENV / (run_name + "-comparison.json"), comparison)
print(json.dumps(comparison, indent=2))
print("PASS: two serial builds; ELF, flash image, code/rodata, data, vectors, layouts, symbols identical")
