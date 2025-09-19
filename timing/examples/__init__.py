from matplotlib import pyplot as plt
from sympy import symbols, sympify

def plot_comparison(title, xlabel, ylabel, ranges, lines, savepath="./comparison_plot.png"):
    plt.figure(figsize=(12, 6))
    for label, color, min, max in ranges:
        plt.fill_between(range(len(min)), min, max, color=color, label=label)
    for label, y in lines:
        plt.plot(range(len(y)), y, label=label)
    plt.xlabel(xlabel)
    plt.ylabel(ylabel)
    plt.title(title)
    plt.legend()
    plt.grid(True)
    plt.tight_layout()
    plt.savefig(savepath)

def compile_equation(equation_path, cpu, syms):
    with open(equation_path, 'r') as file:
        expr_str = file.read().strip()
    syms += ["T_inst_latency", "T_data_latency"]
    syms = [symbols(s) for s in syms]
    try:
        parsed_expr = sympify(expr_str)
        def equation(args, mode):
            if mode == "min":
                inst = cpu.min_inst_lat
                data = cpu.min_data_lat
            elif mode == "max":
                inst = cpu.max_inst_lat
                data = cpu.max_data_lat
            args += [inst, data]
            return int(parsed_expr.subs([(syms[i], args[i]) for i in range(len(syms))]).evalf())
        return equation
    except Exception as e:
        print(f"Failed to parse equation: {e}")
        return None

def variance(data, sample=False):
    if not data:
        return 0.0
    min = [i[0] for i in data]
    max = [i[1] for i in data]
    out = []
    for data in [min, max]:
        mean = sum(data) / len(data)
        squared_diffs = [(x - mean) ** 2 for x in data]
        divisor = len(data) - 1 if sample and len(data) > 1 else len(data)
        out.append(sum(squared_diffs) / divisor)
    return out
