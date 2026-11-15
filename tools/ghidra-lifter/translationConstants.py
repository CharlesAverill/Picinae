import ghidra.program.model.pcode.PcodeOp as PcodeOp

i386_PicRegs = {
  'V_MEM32',
  'R_AF', 'R_CF', 'R_DF', 'R_OF', 'R_PF', 'R_SF', 'R_ZF',
  'R_CS', 'R_DS', 'R_ES', 'R_FS', 'R_GS', 'R_SS',
  'R_FPU_CONTROL',
  'R_ST0', 'R_ST1', 'R_ST2', 'R_ST3', 'R_ST4', 'R_ST5', 'R_ST6', 'R_ST7',
  'R_EAX', 'R_EBX', 'R_ECX', 'R_EDX', 'R_EDI', 'R_ESI',
  'R_EIP',
  'R_ESP', 'R_EBP',
  'R_FS_BASE', 'R_GS_BASE',
  'R_LDTR', 'R_GDTR',
  'R_MXCSR',
  'R_YMM0', 'R_YMM1', 'R_YMM2',  'R_YMM3',  'R_YMM4',  'R_YMM5',  'R_YMM6',  'R_YMM7',
  'R_YMM8', 'R_YMM9', 'R_YMM10', 'R_YMM11', 'R_YMM12', 'R_YMM13', 'R_YMM14', 'R_YMM15',
  'A_READ', 'A_WRITE',
  'V_TEMP',
}

i386_BitRegs = {'R_AF', 'R_CF', 'R_DF', 'R_OF', 'R_PF', 'R_SF', 'R_ZF'}

# Register bitwidths from Picinae's typctx definitions. Memory, page permission
# variables, and temporaries with type None are omitted, as in amd64typctx.
i386typctx = {
  'R_AF': 1, 'R_CF': 1, 'R_DF': 1, 'R_OF': 1, 'R_PF': 1, 'R_SF': 1, 'R_ZF': 1,
  'R_CS': 16, 'R_DS': 16, 'R_ES': 16, 'R_FS': 16, 'R_GS': 16, 'R_SS': 16, 'R_FPU_CONTROL': 16,
  'R_ST0': 80, 'R_ST1': 80, 'R_ST2': 80, 'R_ST3': 80, 'R_ST4': 80, 'R_ST5': 80, 'R_ST6': 80, 'R_ST7': 80,
  'R_EAX': 32, 'R_EBX': 32, 'R_ECX': 32, 'R_EDX': 32, 'R_EDI': 32, 'R_ESI': 32,
  'R_EIP': 32, 'R_ESP': 32, 'R_EBP': 32,
  'R_FS_BASE': 32, 'R_GS_BASE': 32,
  'R_LDTR': 32, 'R_GDTR': 32, 'R_MXCSR': 32,
  'R_YMM0': 256, 'R_YMM1': 256, 'R_YMM2': 256, 'R_YMM3': 256,
  'R_YMM4': 256, 'R_YMM5': 256, 'R_YMM6': 256, 'R_YMM7': 256,
  'R_YMM8': 256, 'R_YMM9': 256, 'R_YMM10': 256, 'R_YMM11': 256,
  'R_YMM12': 256, 'R_YMM13': 256, 'R_YMM14': 256, 'R_YMM15': 256,
}

amd64_PicRegs = {
  'V_MEM64',
  'R_AF', 'R_CF', 'R_DF', 'R_OF', 'R_PF', 'R_SF', 'R_ZF',
  'R_CS', 'R_DS', 'R_ES', 'R_FS', 'R_GS', 'R_SS',
  'R_FPU_CONTROL',
  'R_ST0', 'R_ST1', 'R_ST2', 'R_ST3', 'R_ST4', 'R_ST5', 'R_ST6', 'R_ST7',
  'R_RAX', 'R_RBX', 'R_RCX', 'R_RDX', 'R_RDI', 'R_RSI',
  'R_RSP', 'R_RBP',
  'R_R8', 'R_R9', 'R_R10', 'R_R11', 'R_R12', 'R_R13', 'R_R14', 'R_R15',
  'R_FS_BASE', 'R_GS_BASE',
  'R_LDTR', 'R_GDTR',
  'R_MXCSR',
  'R_YMM0', 'R_YMM1', 'R_YMM2' , 'R_YMM3' , 'R_YMM4' , 'R_YMM5' , 'R_YMM6' , 'R_YMM7'
  'R_YMM8', 'R_YMM9', 'R_YMM10', 'R_YMM11', 'R_YMM12', 'R_YMM13', 'R_YMM14', 'R_YMM15',
  'A_READ', 'A_WRITE',
  'V_TEMP',
  'R_AH', 'R_BH', 'R_CH', 'R_DH',
  'R_AL', 'R_BL', 'R_CL', 'R_DL',
  'R_EAX', 'R_EBX', 'R_ECX', 'R_EDX', 'R_EDI', 'R_ESI', 'R_EBP', 'R_ESP',
  'R_RIP',
  'R_AX', 'R_BX', 'R_CX', 'R_DX', 'R_DI', 'R_SI', 'R_BP', 'R_SP',
  'R_R8B',  'R_R9B',  'R_R10B',  'R_R11B',  'R_R12B',  'R_R13B',  'R_R14B',  'R_R15B',
  'R_R8W',  'R_R9W',  'R_R10W',  'R_R11W',  'R_R12W',  'R_R13W',  'R_R14W',  'R_R15W',
  'R_R8D',  'R_R9D',  'R_R10D',  'R_R11D',  'R_R12D',  'R_R13D',  'R_R14D',  'R_R15D',
  'R_R8',  'R_R9',  'R_R10',  'R_R11',  'R_R12',  'R_R13',  'R_R14',  'R_R15',
}

amd64_BitRegs = {'R_AF', 'R_CF', 'R_DF', 'R_OF', 'R_PF', 'R_SF', 'R_ZF'}

amd64typctx = {
  'R_AF': 1, 'R_CF': 1, 'R_DF': 1, 'R_OF': 1, 'R_PF': 1, 'R_SF': 1, 'R_ZF': 1,
  'R_CS': 16, 'R_DS': 16, 'R_ES': 16, 'R_FS': 16, 'R_GS': 16, 'R_SS': 16, 'R_FPU_CONTROL': 16,
  'R_ST0': 80, 'R_ST1': 80, 'R_ST2': 80, 'R_ST3': 80, 'R_ST4': 80, 'R_ST5': 80, 'R_ST6': 80, 'R_ST7': 80,
  'R_RAX': 64, 'R_RBX': 64, 'R_RCX': 64, 'R_RDX': 64, 'R_RDI': 64, 'R_RSI': 64,
  'R_RSP': 64, 'R_RBP': 64, 'R_R8': 64,
  'R_R9': 64, 'R_R10': 64, 'R_R11': 64, 'R_R12': 64, 'R_R13': 64, 'R_R14': 64, 'R_R15': 64,
  'R_FS_BASE': 64, 'R_GS_BASE': 64,
  'R_LDTR': 64, 'R_GDTR': 64, 'R_MXCSR': 64,
  'R_YMM0': 256, 'R_YMM1': 256, 'R_YMM2': 256, 'R_YMM3': 256, 'R_YMM4': 256, 'R_YMM5': 256, 'R_YMM6': 256, 'R_YMM7': 256, 'R_YMM8': 256, 'R_YMM9': 256, 'R_YMM10': 256, 'R_YMM11': 256, 'R_YMM12': 256, 'R_YMM13': 256, 'R_YMM14': 256, 'R_YMM15': 256,
}


# translate to picinae binop
simpBinopTrans : dict = {
    PcodeOp.INT_ADD: 'OP_PLUS',
    PcodeOp.INT_SUB: 'OP_MINUS',
    PcodeOp.INT_MULT: 'OP_TIMES',
    PcodeOp.INT_DIV: 'OP_DIVIDE',
    PcodeOp.INT_SDIV: 'OP_SDIVIDE',
    PcodeOp.INT_REM: 'OP_MOD',
    PcodeOp.INT_SREM: 'OP_SMOD',
    PcodeOp.INT_LEFT: 'OP_LSHIFT',
    PcodeOp.INT_RIGHT: 'OP_RSHIFT',
    PcodeOp.INT_SRIGHT: 'OP_ARSHIFT',
    PcodeOp.INT_AND: 'OP_AND',
    PcodeOp.INT_OR: 'OP_OR',
    PcodeOp.INT_XOR: 'OP_XOR',
    PcodeOp.BOOL_AND: 'OP_AND',
    PcodeOp.BOOL_OR: 'OP_OR',
    PcodeOp.BOOL_XOR: 'OP_XOR'
}


# picinae outputs 1bit for these ops
# must zero-widen to represent pcode's 1byte outputs
bitBinopTrans : dict = {
    PcodeOp.INT_EQUAL: 'OP_EQ',
    PcodeOp.INT_NOTEQUAL: 'OP_NEQ',
    PcodeOp.INT_LESS: 'OP_LT',
    PcodeOp.INT_LESSEQUAL: 'OP_LE',
    PcodeOp.INT_SLESS: 'OP_SLT',
    PcodeOp.INT_SLESSEQUAL: 'OP_SLE'
}


# register whitelists
arm7_PicRegs = {
  'V_MEM32', 'V_MEM64',
  'R_R0', 'R_R1', 'R_R2', 'R_R3', 'R_R4', 'R_R5', 'R_R6', 'R_R7',
  'R_R8', 'R_R9', 'R_R10', 'R_R11', 'R_R12',
  'R_SP', 'R_LR', 'R_PC',
  'R_M', 'R_T', 'R_F', 'R_I', 'R_A', 'R_E', 'R_IT', 'R_GE', 'R_DNM',
  'R_JF', 'R_QF', 'R_VF', 'R_CF', 'R_ZF', 'R_NF',
  'A_READ', 'A_WRITE',
  'V_TEMP',

}

arm7typctx = {
  'R_R0': 32, 'R_R1': 32, 'R_R2': 32, 'R_R3': 32,
  'R_R4': 32, 'R_R5': 32, 'R_R6': 32, 'R_R7': 32,
  'R_R8': 32, 'R_R9': 32, 'R_R10': 32, 'R_R11': 32, 'R_R12': 32,
  'R_SP': 32, 'R_LR': 32, 'R_PC': 32,
  'R_M': 5,
  'R_T': 1, 'R_F': 1, 'R_I': 1, 'R_A': 1, 'R_E': 1,
  'R_IT': 8, 'R_GE': 4, 'R_DNM': 4,
  'R_JF': 1, 'R_QF': 1, 'R_VF': 1, 'R_CF': 1, 'R_ZF': 1, 'R_NF': 1,
}

arm8_PicRegs = {
    'V_MEM32', 'V_MEM64',
    'R_X0', 'R_X1', 'R_X2', 'R_X3', 'R_X4', 'R_X5', 'R_X6', 'R_X7', 'R_X8', 'R_X9', 'R_X10',
    'R_X11', 'R_X12', 'R_X13', 'R_X14', 'R_X15', 'R_X16', 'R_X17', 'R_X18', 'R_X19', 'R_X20',
    'R_X21', 'R_X22', 'R_X23', 'R_X24', 'R_X25', 'R_X26', 'R_X27', 'R_X28', 'R_X29', 'R_X30',
    'R_SP', 'R_LR', 'R_PC',
    'R_NG', 'R_ZR', 'R_CY', 'R_OV',
    'R_TMPNG', 'R_TMPZR', 'R_TMPCY', 'R_TMPOV',
    'R_XZR',
    'R_Z0', 'R_Z1', 'R_Z2', 'R_Z3', 'R_Z4', 'R_Z5', 'R_Z6', 'R_Z7', 'R_Z8', 'R_Z9', 'R_Z10',
    'R_Z11', 'R_Z12', 'R_Z13', 'R_Z14', 'R_Z15', 'R_Z16', 'R_Z17', 'R_Z18', 'R_Z19', 'R_Z20',
    'R_Z21', 'R_Z22', 'R_Z23', 'R_Z24', 'R_Z25', 'R_Z26', 'R_Z27', 'R_Z28', 'R_Z29', 'R_Z30', 'R_Z31',
    'R_TMPZ0', 'R_TMPZ1', 'R_TMPZ2', 'R_TMPZ3', 'R_TMPZ4', 'R_TMPZ5', 'R_TMPZ6', 'R_TMP_LDXN',
    'R_B0', 'R_B1', 'R_B2', 'R_B3', 'R_B4', 'R_B5', 'R_B6', 'R_B7', 'R_B8', 'R_B9',
    'R_B10', 'R_B11', 'R_B12', 'R_B13', 'R_B14', 'R_B15', 'R_B16', 'R_B17', 'R_B18', 'R_B19',
    'R_B20', 'R_B21', 'R_B22', 'R_B23', 'R_B24', 'R_B25', 'R_B26', 'R_B27', 'R_B28', 'R_B29',
    'R_B30', 'R_B31',
    'A_READ', 'A_WRITE',
    'V_TEMP',
}

arm8typctx = {
  'R_X0': 64, 'R_X1': 64, 'R_X2': 64, 'R_X3': 64,
  'R_X4': 64, 'R_X5': 64, 'R_X6': 64, 'R_X7': 64,
  'R_X8': 64, 'R_X9': 64, 'R_X10': 64, 'R_X11': 64,
  'R_X12': 64, 'R_X13': 64, 'R_X14': 64, 'R_X15': 64,
  'R_X16': 64, 'R_X17': 64, 'R_X18': 64, 'R_X19': 64,
  'R_X20': 64, 'R_X21': 64, 'R_X22': 64, 'R_X23': 64,
  'R_X24': 64, 'R_X25': 64, 'R_X26': 64, 'R_X27': 64,
  'R_X28': 64, 'R_X29': 64, 'R_X30': 64,
  'R_XZR': 64, 'R_SP': 64, 'R_LR': 64, 'R_PC': 64,
  'R_NG': 8, 'R_ZR': 8, 'R_CY': 8, 'R_OV': 8,
  'R_TMPNG': 8, 'R_TMPZR': 8, 'R_TMPCY': 8, 'R_TMPOV': 8,
  'R_Z0': 256, 'R_Z1': 256, 'R_Z2': 256, 'R_Z3': 256,
  'R_Z4': 256, 'R_Z5': 256, 'R_Z6': 256, 'R_Z7': 256,
  'R_Z8': 256, 'R_Z9': 256, 'R_Z10': 256, 'R_Z11': 256,
  'R_Z12': 256, 'R_Z13': 256, 'R_Z14': 256, 'R_Z15': 256,
  'R_Z16': 256, 'R_Z17': 256, 'R_Z18': 256, 'R_Z19': 256,
  'R_Z20': 256, 'R_Z21': 256, 'R_Z22': 256, 'R_Z23': 256,
  'R_Z24': 256, 'R_Z25': 256, 'R_Z26': 256, 'R_Z27': 256,
  'R_Z28': 256, 'R_Z29': 256, 'R_Z30': 256, 'R_Z31': 256,
  'R_TMPZ0': 256, 'R_TMPZ1': 256, 'R_TMPZ2': 256, 'R_TMPZ3': 256,
  'R_TMPZ4': 256, 'R_TMPZ5': 256, 'R_TMPZ6': 256,
  'R_TMP_LDXN': 64,
}

# These registers are used by Ghidra for 1-bit flags, but Ghidra doesn't support registers smaller
# than 8-bits, so we have to zero-widen the 1-bit operations going into these registers to typecheck.
arm8_BytRegs = {
    'R_NG', 'R_ZR', 'R_CY', 'R_OV', 'R_TMPNG', 'R_TMPZR', 'R_TMPCY', 'R_TMPOV'
}

s390x_PicRegs = {
    'V_MEM64',
    'R_GR0', 'R_GR1', 'R_GR2', 'R_GR3', 'R_GR4', 'R_GR5', 'R_GR6', 'R_GR7',
    'R_GR8', 'R_GR9', 'R_GR10', 'R_GR11', 'R_GR12', 'R_GR13', 'R_GR14', 'R_GR15',
    'R_AR0', 'R_AR1', 'R_AR2', 'R_AR3', 'R_AR4', 'R_AR5', 'R_AR6', 'R_AR7',
    'R_AR8', 'R_AR9', 'R_AR10', 'R_AR11', 'R_AR12', 'R_AR13', 'R_AR14', 'R_AR15',
    'R_C0', 'R_C1', 'R_C2', 'R_C3', 'R_C4', 'R_C5', 'R_C6', 'R_C7',
    'R_C8', 'R_C9', 'R_C10', 'R_C11', 'R_C12', 'R_C13', 'R_C14', 'R_C15',
    'R_FP0', 'R_FP1', 'R_FP2', 'R_FP3', 'R_FP4', 'R_FP5', 'R_FP6', 'R_FP7',
    'R_FP8', 'R_FP9', 'R_FP10', 'R_FP11', 'R_FP12', 'R_FP13', 'R_FP14', 'R_FP15',
    'R_XFP0', 'R_XFP1', 'R_XFP2', 'R_XFP3', 'R_XFP4', 'R_XFP5', 'R_XFP6', 'R_XFP7',
    'R_XFP8', 'R_XFP9', 'R_XFP10', 'R_XFP11', 'R_XFP12', 'R_XFP13', 'R_XFP14', 'R_XFP15',
    'R_PC', 'R_CC', 'R_FPC',
    'A_READ', 'A_WRITE',
    'V_TEMP',
}

s390xtypctx = {
    'R_GR0': 64, 'R_GR1': 64, 'R_GR2': 64, 'R_GR3': 64,
    'R_GR4': 64, 'R_GR5': 64, 'R_GR6': 64, 'R_GR7': 64,
    'R_GR8': 64, 'R_GR9': 64, 'R_GR10': 64, 'R_GR11': 64,
    'R_GR12': 64, 'R_GR13': 64, 'R_GR14': 64, 'R_GR15': 64,
    'R_AR0': 32, 'R_AR1': 32, 'R_AR2': 32, 'R_AR3': 32,
    'R_AR4': 32, 'R_AR5': 32, 'R_AR6': 32, 'R_AR7': 32,
    'R_AR8': 32, 'R_AR9': 32, 'R_AR10': 32, 'R_AR11': 32,
    'R_AR12': 32, 'R_AR13': 32, 'R_AR14': 32, 'R_AR15': 32,
    'R_C0': 64, 'R_C1': 64, 'R_C2': 64, 'R_C3': 64,
    'R_C4': 64, 'R_C5': 64, 'R_C6': 64, 'R_C7': 64,
    'R_C8': 64, 'R_C9': 64, 'R_C10': 64, 'R_C11': 64,
    'R_C12': 64, 'R_C13': 64, 'R_C14': 64, 'R_C15': 64,
    'R_FP0': 64, 'R_FP1': 64, 'R_FP2': 64, 'R_FP3': 64,
    'R_FP4': 64, 'R_FP5': 64, 'R_FP6': 64, 'R_FP7': 64,
    'R_FP8': 64, 'R_FP9': 64, 'R_FP10': 64, 'R_FP11': 64,
    'R_FP12': 64, 'R_FP13': 64, 'R_FP14': 64, 'R_FP15': 64,
    'R_XFP0': 128, 'R_XFP1': 128, 'R_XFP2': 128, 'R_XFP3': 128,
    'R_XFP4': 128, 'R_XFP5': 128, 'R_XFP6': 128, 'R_XFP7': 128,
    'R_XFP8': 128, 'R_XFP9': 128, 'R_XFP10': 128, 'R_XFP11': 128,
    'R_XFP12': 128, 'R_XFP13': 128, 'R_XFP14': 128, 'R_XFP15': 128,
    'R_PC': 64, 'R_CC': 8, 'R_FPC': 32,
}

s390x_BytRegs = {'R_CC'}

arm7_32_PicRegs = {
   'V_MEM32',  'V_MEM64',
   'R_R0',  'R_R1',  'R_R2',  'R_R3',  'R_R4',  'R_R5',  'R_R6',  'R_R7',
   'R_R8',  'R_R9',  'R_R10',  'R_R11',  'R_R12',
   'R_SP',  'R_LR',  'R_PC',
   'R_M', 'R_T', 'R_F', 'R_I', 'R_A', 'R_E',
   'R_IT', 'R_GE', 'R_DNM',
   'R_JF', 'R_QF', 'R_VF', 'R_CF', 'R_ZF', 'R_NF',
   'A_READ',  'A_WRITE',
   'V_TEMP'
}

ebpf_PicRegs = {
    'R_R0', 'R_R1', 'R_R2', 'R_R3', 'R_R4', 'R_R6', 'R_R7', 'R_R8', 'R_R9', 'R_R10',
}

riscv_PicRegs ={
  'V_MEM32',
  'R_RA', 'R_SP', 'R_GP', 'R_TP',
  'R_T0', 'R_T1', 'R_T2', 'R_T3', 'R_T4', 'R_T5', 'R_T6',
  'R_A0', 'R_A1', 'R_A2', 'R_A3', 'R_A4', 'R_A5', 'R_A6', 'R_A7',
  'R_S0', 'R_S1', 'R_S2', 'R_S3', 'R_S4', 'R_S5', 'R_S6',
  'R_S7', 'R_S8', 'R_S9', 'R_S10', 'R_S11',
  'A_READ', 'A_WRITE', 'A_EXEC'
}

riscv_BytRegs = {}

riscvtypctx = {
  'R_RA': 32, 'R_SP': 32, 'R_GP': 32, 'R_TP': 32,
  'R_T0': 32, 'R_T1': 32, 'R_T2': 32, 'R_T3': 32, 'R_T4': 32, 'R_T5': 32, 'R_T6': 32,
  'R_A0': 32, 'R_A1': 32, 'R_A2': 32, 'R_A3': 32,
  'R_A4': 32, 'R_A5': 32, 'R_A6': 32, 'R_A7': 32,
  'R_S0': 32, 'R_S1': 32, 'R_S2': 32, 'R_S3': 32, 'R_S4': 32, 'R_S5': 32,
  'R_S6': 32, 'R_S7': 32, 'R_S8': 32, 'R_S9': 32, 'R_S10': 32, 'R_S11': 32,
}

cheriot_PicRegs = {
  'V_MEM32', 'V_CTAGRAM', 'V_CREVOCATION', 'V_CSR',
  'R_CNULL', 'R_CRA', 'R_CSP', 'R_CGP', 'R_CTP', 'R_CT0', 'R_CT1', 'R_CT2',
  'R_CS0', 'R_CS1', 'R_CA0', 'R_CA1', 'R_CA2', 'R_CA3', 'R_CA4', 'R_CA5',
  'R_CTAG0', 'R_CTAG1', 'R_CTAG2', 'R_CTAG3', 'R_CTAG4', 'R_CTAG5', 'R_CTAG6', 'R_CTAG7',
  'R_CTAG8', 'R_CTAG9', 'R_CTAG10', 'R_CTAG11', 'R_CTAG12', 'R_CTAG13', 'R_CTAG14', 'R_CTAG15',
  'R_PCC', 'R_MTCC', 'R_MTDC', 'R_MSCRATCHC', 'R_MEPCC',
  'R_PCC_TAG', 'R_MTCC_TAG', 'R_MTDC_TAG', 'R_MSCRATCHC_TAG', 'R_MEPCC_TAG',
  'R_RESERVE_ADDRESS', 'R_RESERVE', 'R_RESERVE_LENGTH',
  'A_READ', 'A_WRITE', 'A_EXEC', 'V_TEMP',
}

cheriottypctx = {
  'R_CNULL': 64, 'R_CRA': 64, 'R_CSP': 64, 'R_CGP': 64,
  'R_CTP': 64, 'R_CT0': 64, 'R_CT1': 64, 'R_CT2': 64,
  'R_CS0': 64, 'R_CS1': 64, 'R_CA0': 64, 'R_CA1': 64,
  'R_CA2': 64, 'R_CA3': 64, 'R_CA4': 64, 'R_CA5': 64,
  'R_CTAG0': 8, 'R_CTAG1': 8, 'R_CTAG2': 8, 'R_CTAG3': 8,
  'R_CTAG4': 8, 'R_CTAG5': 8, 'R_CTAG6': 8, 'R_CTAG7': 8,
  'R_CTAG8': 8, 'R_CTAG9': 8, 'R_CTAG10': 8, 'R_CTAG11': 8,
  'R_CTAG12': 8, 'R_CTAG13': 8, 'R_CTAG14': 8, 'R_CTAG15': 8,
  'R_PCC': 64, 'R_MTCC': 64, 'R_MTDC': 64, 'R_MSCRATCHC': 64, 'R_MEPCC': 64,
  'R_PCC_TAG': 8, 'R_MTCC_TAG': 8, 'R_MTDC_TAG': 8,
  'R_MSCRATCHC_TAG': 8, 'R_MEPCC_TAG': 8,
  'R_RESERVE_ADDRESS': 32, 'R_RESERVE': 8, 'R_RESERVE_LENGTH': 8,
}

cheriot_BytRegs = {
  'R_CTAG0', 'R_CTAG1', 'R_CTAG2', 'R_CTAG3', 'R_CTAG4', 'R_CTAG5', 'R_CTAG6', 'R_CTAG7',
  'R_CTAG8', 'R_CTAG9', 'R_CTAG10', 'R_CTAG11', 'R_CTAG12', 'R_CTAG13', 'R_CTAG14', 'R_CTAG15',
  'R_PCC_TAG', 'R_MTCC_TAG', 'R_MTDC_TAG', 'R_MSCRATCHC_TAG', 'R_MEPCC_TAG',
  'R_RESERVE', 'R_RESERVE_LENGTH',
}

sh2_PicRegs = {
  'V_MEM32',
  'R_R0', 'R_R1', 'R_R2', 'R_R3', 'R_R4', 'R_R5', 'R_R6', 'R_R7',
  'R_R8', 'R_R9', 'R_R10', 'R_R11', 'R_R12', 'R_R13', 'R_R14', 'R_R15',
  'R_SR', 'R_GBR', 'R_VBR', 'R_MACH', 'R_MACL', 'R_PR', 'R_PC',
  'A_READ', 'A_WRITE', 'A_EXEC', 'V_TEMP',
}

sh2typctx = {
  'R_R0': 32, 'R_R1': 32, 'R_R2': 32, 'R_R3': 32,
  'R_R4': 32, 'R_R5': 32, 'R_R6': 32, 'R_R7': 32,
  'R_R8': 32, 'R_R9': 32, 'R_R10': 32, 'R_R11': 32,
  'R_R12': 32, 'R_R13': 32, 'R_R14': 32, 'R_R15': 32,
  'R_SR': 32, 'R_GBR': 32, 'R_VBR': 32, 'R_MACH': 32,
  'R_MACL': 32, 'R_PR': 32, 'R_PC': 32,
}

oki66k_PicRegs = {
  'V_ROM32', 'V_RAM16',
  'R_SSP', 'R_LRB', 'R_PSW', 'R_ACC', 'R_PC', 'R_X1', 'R_X2', 'R_DP', 'R_USP',
  'R_CSR', 'R_TSR', 'R_DSR', 'R_ROMWIN',
  'R_C', 'R_Z', 'R_HC', 'R_S', 'R_OV',
  'A_READ', 'A_WRITE', 'A_EXEC', 'V_TEMP',
}

oki66ktypctx = {
  'R_SSP': 16, 'R_LRB': 16, 'R_PSW': 16, 'R_ACC': 16,
  'R_PC': 16, 'R_X1': 16, 'R_X2': 16, 'R_DP': 16, 'R_USP': 16,
  'R_CSR': 8, 'R_TSR': 8, 'R_DSR': 8, 'R_ROMWIN': 8,
  'R_C': 8, 'R_Z': 8, 'R_HC': 8, 'R_S': 8, 'R_OV': 8,
}

oki66k_BytRegs = {'R_C', 'R_Z', 'R_HC', 'R_S', 'R_OV'}
