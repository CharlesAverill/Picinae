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
