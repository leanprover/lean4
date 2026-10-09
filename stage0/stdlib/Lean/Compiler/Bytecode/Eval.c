// Lean compiler output
// Module: Lean.Compiler.Bytecode.Eval
// Imports: public import Lean.Compiler.LCNF.Basic public import Lean.Compiler.Bytecode.Instruction
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t l_Lean_getIRPhases(lean_object*, lean_object*);
uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_bytecode_decl(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
uint32_t l_Lean_Compiler_Bytecode_Instruction_skipIfCached(uint32_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint32_t l_Lean_Compiler_Bytecode_Instruction_storeCache(uint32_t);
uint32_t l_Lean_Compiler_Bytecode_Instruction_ret(uint32_t);
lean_object* l_Lean_Compiler_Bytecode_assemble(lean_object*);
lean_object* lean_bytecode_mk_initial_cache(lean_object*);
lean_object* lean_eval_bytecode_decl(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t l_Lean_Compiler_Bytecode_Instruction_pap(uint32_t, uint32_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Expr_isVoid(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(lean_object*);
uint32_t l_Lean_Compiler_Bytecode_Instruction_inc(uint32_t, uint32_t);
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxSmall(uint32_t, uint32_t);
lean_object* l_Lean_Compiler_LCNF_mkBoxedName(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_impureSigExt;
lean_object* l_Lean_Compiler_LCNF_getSigCore_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_Compiler_Bytecode_Instruction_loadConst(uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxFloat32(uint32_t, uint32_t);
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxFloat(uint32_t, uint32_t);
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUSize(uint32_t, uint32_t);
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUInt64(uint32_t, uint32_t);
uint32_t l_Lean_Compiler_Bytecode_Instruction_boxUInt32(uint32_t, uint32_t);
lean_object* lean_runtime_mark_persistent(lean_object*);
lean_object* lean_bytecode_store_init_value(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Cannot evaluate constant `"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__1 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "` as it is neither marked nor imported as `meta`"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__2 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__2_value;
LEAN_EXPORT lean_object* lean_eval_check_meta(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__2;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2;
static const lean_array_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__3 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___boxed(lean_object*, lean_object*);
static const lean_string_object l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__4(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Compiler.Bytecode.Eval"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "_private.Lean.Compiler.Bytecode.Eval.0.Lean.Compiler.Bytecode.evalConstCoreImpl"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 276, .m_capacity = 276, .m_length = 272, .m_data = "assertion violation: sig.params.all (!·.borrow) && !sig.type.isScalar && sig.params.all (!·.type.isScalar)\n      && sig.params.all (!·.type.isVoid) && sig.params.size <= 16\n    -- there are parameters but no boxed version\n    -- so the declaration is `pap` compatible\n    "};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__3;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__6 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__6_value;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__7;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "cannot evaluate code because '"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__8 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "' uses 'sorry' and/or contains errors"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__9 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__9_value;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__13 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__13_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__14 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__15 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__15_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__16 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__16_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__17 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__17_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__18 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__18_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__19 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__19_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__20 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__20_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__21 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__21_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__22 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__22_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lcVoid"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__23 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__23_value;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__24;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(interpreter) unknown declaration "};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "Could not find declaration to be initialized: `"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_run_init(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_result_show_error(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_showError___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IO"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__1 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__2 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUInt32(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUInt32___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString___closed__1 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString___boxed(lean_object*);
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Invalid type for `main`: "};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 14, 67, 68, 149, 142, 182, 10)}};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Could not find `main`"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__2_value)}};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__3 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__3_value;
LEAN_EXPORT uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t lean_eval_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_eval_check_meta(lean_object* v_env_5_, lean_object* v_declName_6_){
_start:
{
uint8_t v___x_7_; uint8_t v___x_8_; uint8_t v___x_9_; 
lean_inc(v_declName_6_);
v___x_7_ = l_Lean_getIRPhases(v_env_5_, v_declName_6_);
v___x_8_ = 0;
v___x_9_ = l_Lean_instBEqIRPhases_beq(v___x_7_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; 
lean_dec(v_declName_6_);
v___x_10_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__0));
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__1));
v___x_12_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_6_, v___x_9_);
v___x_13_ = lean_string_append(v___x_11_, v___x_12_);
lean_dec_ref(v___x_12_);
v___x_14_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalCheckMeta___closed__2));
v___x_15_ = lean_string_append(v___x_13_, v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__0(void){
_start:
{
uint32_t v___x_17_; uint32_t v___x_18_; 
v___x_17_ = 0;
v___x_18_ = l_Lean_Compiler_Bytecode_Instruction_storeCache(v___x_17_);
return v___x_18_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__1(void){
_start:
{
uint32_t v___x_19_; uint32_t v___x_20_; 
v___x_19_ = 0;
v___x_20_ = l_Lean_Compiler_Bytecode_Instruction_ret(v___x_19_);
return v___x_20_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__1, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__1_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__1);
v___x_22_ = lean_box_uint32(v___x_21_);
return v___x_22_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__2(void){
_start:
{
uint32_t v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__0, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__0_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__0);
v___x_24_ = lean_box_uint32(v___x_23_);
return v___x_24_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_25_ = lean_unsigned_to_nat(2u);
v___x_26_ = lean_mk_empty_array_with_capacity(v___x_25_);
v___x_27_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__2;
v___x_28_ = lean_array_push(v___x_26_, v___x_27_);
v___x_29_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__1;
v___x_30_ = lean_array_push(v___x_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl(lean_object* v_code_33_, lean_object* v_symbols_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; uint32_t v___x_39_; uint32_t v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_35_ = lean_box(0);
v___x_36_ = lean_array_get_size(v_code_33_);
v___x_37_ = lean_unsigned_to_nat(1u);
v___x_38_ = lean_nat_add(v___x_36_, v___x_37_);
v___x_39_ = lean_uint32_of_nat(v___x_38_);
lean_dec(v___x_38_);
v___x_40_ = l_Lean_Compiler_Bytecode_Instruction_skipIfCached(v___x_39_);
v___x_41_ = lean_mk_empty_array_with_capacity(v___x_37_);
v___x_42_ = lean_box_uint32(v___x_40_);
v___x_43_ = lean_array_push(v___x_41_, v___x_42_);
v___x_44_ = l_Array_append___redArg(v___x_43_, v_code_33_);
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2);
v___x_47_ = l_Array_append___redArg(v___x_44_, v___x_46_);
v___x_48_ = l_Lean_Compiler_Bytecode_assemble(v___x_47_);
lean_dec_ref(v___x_47_);
v___x_49_ = lean_bytecode_mk_initial_cache(v_symbols_34_);
v___x_50_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__3));
v___x_51_ = lean_box(0);
v___x_52_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_52_, 0, v___x_35_);
lean_ctor_set(v___x_52_, 1, v___x_48_);
lean_ctor_set(v___x_52_, 2, v___x_37_);
lean_ctor_set(v___x_52_, 3, v___x_45_);
lean_ctor_set(v___x_52_, 4, v_symbols_34_);
lean_ctor_set(v___x_52_, 5, v___x_49_);
lean_ctor_set(v___x_52_, 6, v___x_45_);
lean_ctor_set(v___x_52_, 7, v___x_50_);
lean_ctor_set(v___x_52_, 8, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___boxed(lean_object* v_code_53_, lean_object* v_symbols_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl(v_code_53_, v_symbols_54_);
lean_dec_ref(v_code_53_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__0(lean_object* v_msg_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__0___closed__0));
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
v___x_60_ = lean_panic_fn_borrowed(v___x_59_, v_msg_57_);
lean_dec_ref_known(v___x_59_, 1);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__4(lean_object* v_msg_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__0___closed__0));
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
v___x_64_ = lean_panic_fn_borrowed(v___x_63_, v_msg_61_);
lean_dec_ref_known(v___x_63_, 1);
return v___x_64_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__2(lean_object* v___x_65_, uint8_t v___y_66_, lean_object* v_as_67_, size_t v_i_68_, size_t v_stop_69_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = lean_usize_dec_eq(v_i_68_, v_stop_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; lean_object* v_type_72_; uint8_t v___x_73_; uint8_t v___y_75_; uint8_t v___x_79_; 
v___x_71_ = lean_array_uget_borrowed(v_as_67_, v_i_68_);
v_type_72_ = lean_ctor_get(v___x_71_, 2);
v___x_73_ = 1;
v___x_79_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v_type_72_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_nat_dec_eq(v___x_65_, v___x_80_);
v___y_75_ = v___x_81_;
goto v___jp_74_;
}
else
{
v___y_75_ = v___y_66_;
goto v___jp_74_;
}
v___jp_74_:
{
if (v___y_75_ == 0)
{
size_t v___x_76_; size_t v___x_77_; 
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_add(v_i_68_, v___x_76_);
v_i_68_ = v___x_77_;
goto _start;
}
else
{
return v___x_73_;
}
}
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_65_ = stack[0].m_obj;
uint8_t v___y_66_ = stack[1].m_num;
lean_object* v_as_67_ = stack[2].m_obj;
size_t v_i_68_ = stack[3].m_num;
size_t v_stop_69_ = stack[4].m_num;
uint8_t v_res_83_;
v_res_83_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__2(v___x_65_, v___y_66_, v_as_67_, v_i_68_, v_stop_69_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__2___boxed(lean_object* v___x_84_, lean_object* v___y_85_, lean_object* v_as_86_, lean_object* v_i_87_, lean_object* v_stop_88_){
_start:
{
uint8_t v___y_2941__boxed_89_; size_t v_i_boxed_90_; size_t v_stop_boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v___y_2941__boxed_89_ = lean_unbox(v___y_85_);
v_i_boxed_90_ = lean_unbox_usize(v_i_87_);
lean_dec(v_i_87_);
v_stop_boxed_91_ = lean_unbox_usize(v_stop_88_);
lean_dec(v_stop_88_);
v_res_92_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__2(v___x_84_, v___y_2941__boxed_89_, v_as_86_, v_i_boxed_90_, v_stop_boxed_91_);
lean_dec_ref(v_as_86_);
lean_dec(v___x_84_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3(lean_object* v___x_94_, lean_object* v_as_95_, size_t v_i_96_, size_t v_stop_97_){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = lean_usize_dec_eq(v_i_96_, v_stop_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; uint8_t v_borrow_100_; uint8_t v___x_101_; 
v___x_99_ = lean_array_uget_borrowed(v_as_95_, v_i_96_);
v_borrow_100_ = lean_ctor_get_uint8(v___x_99_, sizeof(void*)*3);
v___x_101_ = 1;
if (v_borrow_100_ == 0)
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_nat_dec_eq(v___x_94_, v___x_102_);
if (v___x_103_ == 0)
{
size_t v___x_104_; size_t v___x_105_; 
v___x_104_ = ((size_t)1ULL);
v___x_105_ = lean_usize_add(v_i_96_, v___x_104_);
v_i_96_ = v___x_105_;
goto _start;
}
else
{
return v___x_101_;
}
}
else
{
return v___x_101_;
}
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_94_ = stack[0].m_obj;
lean_object* v_as_95_ = stack[1].m_obj;
size_t v_i_96_ = stack[2].m_num;
size_t v_stop_97_ = stack[3].m_num;
uint8_t v_res_108_;
v_res_108_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3(v___x_94_, v_as_95_, v_i_96_, v_stop_97_);
stack->m_num = v_res_108_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3___boxed(lean_object* v___x_109_, lean_object* v_as_110_, lean_object* v_i_111_, lean_object* v_stop_112_){
_start:
{
size_t v_i_boxed_113_; size_t v_stop_boxed_114_; uint8_t v_res_115_; lean_object* v_r_116_; 
v_i_boxed_113_ = lean_unbox_usize(v_i_111_);
lean_dec(v_i_111_);
v_stop_boxed_114_ = lean_unbox_usize(v_stop_112_);
lean_dec(v_stop_112_);
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3(v___x_109_, v_as_110_, v_i_boxed_113_, v_stop_boxed_114_);
lean_dec_ref(v_as_110_);
lean_dec(v___x_109_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1(lean_object* v___x_117_, uint8_t v___y_118_, lean_object* v_as_119_, size_t v_i_120_, size_t v_stop_121_){
_start:
{
uint8_t v___x_122_; 
v___x_122_ = lean_usize_dec_eq(v_i_120_, v_stop_121_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; lean_object* v_type_124_; uint8_t v___x_125_; uint8_t v___y_127_; uint8_t v___x_131_; 
v___x_123_ = lean_array_uget_borrowed(v_as_119_, v_i_120_);
v_type_124_ = lean_ctor_get(v___x_123_, 2);
v___x_125_ = 1;
v___x_131_ = l_Lean_Expr_isVoid(v_type_124_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(0u);
v___x_133_ = lean_nat_dec_eq(v___x_117_, v___x_132_);
v___y_127_ = v___x_133_;
goto v___jp_126_;
}
else
{
v___y_127_ = v___y_118_;
goto v___jp_126_;
}
v___jp_126_:
{
if (v___y_127_ == 0)
{
size_t v___x_128_; size_t v___x_129_; 
v___x_128_ = ((size_t)1ULL);
v___x_129_ = lean_usize_add(v_i_120_, v___x_128_);
v_i_120_ = v___x_129_;
goto _start;
}
else
{
return v___x_125_;
}
}
}
else
{
uint8_t v___x_134_; 
v___x_134_ = 0;
return v___x_134_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_117_ = stack[0].m_obj;
uint8_t v___y_118_ = stack[1].m_num;
lean_object* v_as_119_ = stack[2].m_obj;
size_t v_i_120_ = stack[3].m_num;
size_t v_stop_121_ = stack[4].m_num;
uint8_t v_res_135_;
v_res_135_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1(v___x_117_, v___y_118_, v_as_119_, v_i_120_, v_stop_121_);
stack->m_num = v_res_135_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1___boxed(lean_object* v___x_136_, lean_object* v___y_137_, lean_object* v_as_138_, lean_object* v_i_139_, lean_object* v_stop_140_){
_start:
{
uint8_t v___y_3019__boxed_141_; size_t v_i_boxed_142_; size_t v_stop_boxed_143_; uint8_t v_res_144_; lean_object* v_r_145_; 
v___y_3019__boxed_141_ = lean_unbox(v___y_137_);
v_i_boxed_142_ = lean_unbox_usize(v_i_139_);
lean_dec(v_i_139_);
v_stop_boxed_143_ = lean_unbox_usize(v_stop_140_);
lean_dec(v_stop_140_);
v_res_144_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1(v___x_136_, v___y_3019__boxed_141_, v_as_138_, v_i_boxed_142_, v_stop_boxed_143_);
lean_dec_ref(v_as_138_);
lean_dec(v___x_136_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__3(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_149_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__2));
v___x_150_ = lean_unsigned_to_nat(4u);
v___x_151_ = lean_unsigned_to_nat(72u);
v___x_152_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__1));
v___x_153_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__0));
v___x_154_ = l_mkPanicMessageWithDecl(v___x_153_, v___x_152_, v___x_151_, v___x_150_, v___x_149_);
return v___x_154_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__4(void){
_start:
{
uint32_t v___x_155_; uint32_t v___x_156_; 
v___x_155_ = 0;
v___x_156_ = l_Lean_Compiler_Bytecode_Instruction_pap(v___x_155_, v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__4, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__4_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__4);
v___x_158_ = lean_box_uint32(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v_code_162_; 
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = lean_mk_empty_array_with_capacity(v___x_159_);
v___x_161_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5___boxed__const__1;
v_code_162_ = lean_array_push(v___x_160_, v___x_161_);
return v_code_162_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__7(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_164_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__6));
v___x_165_ = lean_unsigned_to_nat(11u);
v___x_166_ = lean_unsigned_to_nat(70u);
v___x_167_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__1));
v___x_168_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__0));
v___x_169_ = l_mkPanicMessageWithDecl(v___x_168_, v___x_167_, v___x_166_, v___x_165_, v___x_164_);
return v___x_169_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10(void){
_start:
{
uint32_t v___x_172_; uint32_t v___x_173_; 
v___x_172_ = 0;
v___x_173_ = l_Lean_Compiler_Bytecode_Instruction_loadConst(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11___boxed__const__1(void){
_start:
{
uint32_t v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10);
v___x_175_ = lean_box_uint32(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_code_179_; 
v___x_176_ = lean_unsigned_to_nat(1u);
v___x_177_ = lean_mk_empty_array_with_capacity(v___x_176_);
v___x_178_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11___boxed__const__1;
v_code_179_ = lean_array_push(v___x_177_, v___x_178_);
return v_code_179_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__24(void){
_start:
{
uint32_t v___x_192_; uint32_t v___x_193_; 
v___x_192_ = 0;
v___x_193_ = l_Lean_Compiler_Bytecode_Instruction_boxFloat32(v___x_192_, v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25___boxed__const__1(void){
_start:
{
uint32_t v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__24, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__24_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__24);
v___x_195_ = lean_box_uint32(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25(void){
_start:
{
lean_object* v_code_196_; lean_object* v___x_197_; lean_object* v_code_198_; 
v_code_196_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11);
v___x_197_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25___boxed__const__1;
v_code_198_ = lean_array_push(v_code_196_, v___x_197_);
return v_code_198_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26(void){
_start:
{
uint32_t v___x_199_; uint32_t v___x_200_; 
v___x_199_ = 0;
v___x_200_ = l_Lean_Compiler_Bytecode_Instruction_boxFloat(v___x_199_, v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27___boxed__const__1(void){
_start:
{
uint32_t v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26);
v___x_202_ = lean_box_uint32(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27(void){
_start:
{
lean_object* v_code_203_; lean_object* v___x_204_; lean_object* v_code_205_; 
v_code_203_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11);
v___x_204_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27___boxed__const__1;
v_code_205_ = lean_array_push(v_code_203_, v___x_204_);
return v_code_205_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28(void){
_start:
{
uint32_t v___x_206_; uint32_t v___x_207_; 
v___x_206_ = 0;
v___x_207_ = l_Lean_Compiler_Bytecode_Instruction_boxUSize(v___x_206_, v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29___boxed__const__1(void){
_start:
{
uint32_t v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28);
v___x_209_ = lean_box_uint32(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29(void){
_start:
{
lean_object* v_code_210_; lean_object* v___x_211_; lean_object* v_code_212_; 
v_code_210_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11);
v___x_211_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29___boxed__const__1;
v_code_212_ = lean_array_push(v_code_210_, v___x_211_);
return v_code_212_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30(void){
_start:
{
uint32_t v___x_213_; uint32_t v___x_214_; 
v___x_213_ = 0;
v___x_214_ = l_Lean_Compiler_Bytecode_Instruction_boxUInt64(v___x_213_, v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31___boxed__const__1(void){
_start:
{
uint32_t v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30);
v___x_216_ = lean_box_uint32(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31(void){
_start:
{
lean_object* v_code_217_; lean_object* v___x_218_; lean_object* v_code_219_; 
v_code_217_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11);
v___x_218_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31___boxed__const__1;
v_code_219_ = lean_array_push(v_code_217_, v___x_218_);
return v_code_219_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32(void){
_start:
{
uint32_t v___x_220_; uint32_t v___x_221_; 
v___x_220_ = 0;
v___x_221_ = l_Lean_Compiler_Bytecode_Instruction_boxUInt32(v___x_220_, v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33___boxed__const__1(void){
_start:
{
uint32_t v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32);
v___x_223_ = lean_box_uint32(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33(void){
_start:
{
lean_object* v_code_224_; lean_object* v___x_225_; lean_object* v_code_226_; 
v_code_224_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11);
v___x_225_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33___boxed__const__1;
v_code_226_ = lean_array_push(v_code_224_, v___x_225_);
return v_code_226_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(lean_object* v_env_228_, lean_object* v_constName_229_){
_start:
{
lean_object* v_code_231_; lean_object* v___y_242_; lean_object* v___y_248_; uint8_t v___y_249_; lean_object* v___y_251_; lean_object* v___y_252_; lean_object* v___y_253_; uint8_t v___y_254_; uint8_t v___y_255_; lean_object* v___y_261_; lean_object* v___y_262_; lean_object* v___y_263_; uint8_t v___y_264_; uint8_t v___y_265_; lean_object* v___y_267_; lean_object* v___y_268_; lean_object* v___y_269_; uint8_t v___y_270_; uint8_t v___y_271_; lean_object* v___y_277_; lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; uint8_t v___y_281_; uint8_t v___y_282_; uint32_t v___y_285_; lean_object* v___y_286_; uint32_t v___y_292_; lean_object* v___y_293_; lean_object* v___y_298_; lean_object* v_boxedName_309_; lean_object* v___x_318_; lean_object* v___x_319_; 
lean_inc(v_constName_229_);
v_boxedName_309_ = l_Lean_Compiler_LCNF_mkBoxedName(v_constName_229_);
v___x_318_ = l_Lean_Compiler_LCNF_impureSigExt;
lean_inc(v_boxedName_309_);
lean_inc_ref(v_env_228_);
v___x_319_ = l_Lean_Compiler_LCNF_getSigCore_x3f___redArg(v_env_228_, v___x_318_, v_boxedName_309_);
if (lean_obj_tag(v___x_319_) == 1)
{
lean_object* v___x_320_; 
lean_dec_ref_known(v___x_319_, 1);
lean_dec(v_constName_229_);
lean_inc(v_boxedName_309_);
lean_inc_ref(v_env_228_);
v___x_320_ = lean_find_bytecode_decl(v_env_228_, v_boxedName_309_);
if (lean_obj_tag(v___x_320_) == 1)
{
lean_object* v_val_321_; lean_object* v_sorryDep_x3f_322_; 
v_val_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_val_321_);
lean_dec_ref_known(v___x_320_, 1);
v_sorryDep_x3f_322_ = lean_ctor_get(v_val_321_, 8);
lean_inc(v_sorryDep_x3f_322_);
lean_dec(v_val_321_);
if (lean_obj_tag(v_sorryDep_x3f_322_) == 1)
{
lean_object* v_val_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_336_; 
lean_dec(v_boxedName_309_);
lean_dec_ref(v_env_228_);
v_val_323_ = lean_ctor_get(v_sorryDep_x3f_322_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_sorryDep_x3f_322_);
if (v_isSharedCheck_336_ == 0)
{
v___x_325_ = v_sorryDep_x3f_322_;
v_isShared_326_ = v_isSharedCheck_336_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_val_323_);
lean_dec(v_sorryDep_x3f_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_336_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v___x_327_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__8));
v___x_328_ = 1;
v___x_329_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_323_, v___x_328_);
v___x_330_ = lean_string_append(v___x_327_, v___x_329_);
lean_dec_ref(v___x_329_);
v___x_331_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__9));
v___x_332_ = lean_string_append(v___x_330_, v___x_331_);
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 0);
lean_ctor_set(v___x_325_, 0, v___x_332_);
v___x_334_ = v___x_325_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v___x_332_);
v___x_334_ = v_reuseFailAlloc_335_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
return v___x_334_;
}
}
}
else
{
lean_dec(v_sorryDep_x3f_322_);
goto v___jp_310_;
}
}
else
{
lean_dec(v___x_320_);
goto v___jp_310_;
}
}
else
{
lean_object* v___x_337_; 
lean_dec(v___x_319_);
lean_dec(v_boxedName_309_);
lean_inc(v_constName_229_);
lean_inc_ref(v_env_228_);
v___x_337_ = l_Lean_Compiler_LCNF_getSigCore_x3f___redArg(v_env_228_, v___x_318_, v_constName_229_);
if (lean_obj_tag(v___x_337_) == 1)
{
lean_object* v_val_338_; lean_object* v___x_385_; 
v_val_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_val_338_);
lean_dec_ref_known(v___x_337_, 1);
lean_inc(v_constName_229_);
lean_inc_ref(v_env_228_);
v___x_385_ = lean_find_bytecode_decl(v_env_228_, v_constName_229_);
if (lean_obj_tag(v___x_385_) == 1)
{
lean_object* v_val_386_; lean_object* v_sorryDep_x3f_387_; 
v_val_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_386_);
lean_dec_ref_known(v___x_385_, 1);
v_sorryDep_x3f_387_ = lean_ctor_get(v_val_386_, 8);
lean_inc(v_sorryDep_x3f_387_);
lean_dec(v_val_386_);
if (lean_obj_tag(v_sorryDep_x3f_387_) == 1)
{
lean_object* v_val_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_val_338_);
lean_dec(v_constName_229_);
lean_dec_ref(v_env_228_);
v_val_388_ = lean_ctor_get(v_sorryDep_x3f_387_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v_sorryDep_x3f_387_);
if (v_isSharedCheck_401_ == 0)
{
v___x_390_ = v_sorryDep_x3f_387_;
v_isShared_391_ = v_isSharedCheck_401_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_val_388_);
lean_dec(v_sorryDep_x3f_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_401_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_399_; 
v___x_392_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__8));
v___x_393_ = 1;
v___x_394_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_388_, v___x_393_);
v___x_395_ = lean_string_append(v___x_392_, v___x_394_);
lean_dec_ref(v___x_394_);
v___x_396_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__9));
v___x_397_ = lean_string_append(v___x_395_, v___x_396_);
if (v_isShared_391_ == 0)
{
lean_ctor_set_tag(v___x_390_, 0);
lean_ctor_set(v___x_390_, 0, v___x_397_);
v___x_399_ = v___x_390_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v___x_397_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
else
{
lean_dec(v_sorryDep_x3f_387_);
goto v___jp_339_;
}
}
else
{
lean_dec(v___x_385_);
goto v___jp_339_;
}
v___jp_339_:
{
lean_object* v_type_340_; lean_object* v_params_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v_type_340_ = lean_ctor_get(v_val_338_, 2);
lean_inc_ref(v_type_340_);
v_params_341_ = lean_ctor_get(v_val_338_, 3);
lean_inc_ref(v_params_341_);
lean_dec(v_val_338_);
v___x_342_ = lean_array_get_size(v_params_341_);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_nat_dec_eq(v___x_342_, v___x_343_);
if (v___x_344_ == 0)
{
uint8_t v___x_345_; 
v___x_345_ = lean_nat_dec_lt(v___x_343_, v___x_342_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = 1;
v___y_277_ = v___x_343_;
v___y_278_ = v___x_342_;
v___y_279_ = v_type_340_;
v___y_280_ = v_params_341_;
v___y_281_ = v___x_344_;
v___y_282_ = v___x_346_;
goto v___jp_276_;
}
else
{
if (v___x_345_ == 0)
{
v___y_277_ = v___x_343_;
v___y_278_ = v___x_342_;
v___y_279_ = v_type_340_;
v___y_280_ = v_params_341_;
v___y_281_ = v___x_344_;
v___y_282_ = v___x_345_;
goto v___jp_276_;
}
else
{
size_t v___x_347_; size_t v___x_348_; uint8_t v___x_349_; 
v___x_347_ = ((size_t)0ULL);
v___x_348_ = lean_usize_of_nat(v___x_342_);
v___x_349_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3(v___x_342_, v_params_341_, v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
v___y_277_ = v___x_343_;
v___y_278_ = v___x_342_;
v___y_279_ = v_type_340_;
v___y_280_ = v_params_341_;
v___y_281_ = v___x_344_;
v___y_282_ = v___x_345_;
goto v___jp_276_;
}
else
{
lean_dec_ref(v_params_341_);
lean_dec_ref(v_type_340_);
lean_dec(v_constName_229_);
lean_dec_ref(v_env_228_);
goto v___jp_238_;
}
}
}
}
else
{
uint32_t v___x_350_; lean_object* v_code_351_; 
lean_dec_ref(v_params_341_);
v___x_350_ = 0;
v_code_351_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11);
if (lean_obj_tag(v_type_340_) == 4)
{
lean_object* v_declName_352_; 
v_declName_352_ = lean_ctor_get(v_type_340_, 0);
lean_inc(v_declName_352_);
if (lean_obj_tag(v_declName_352_) == 1)
{
lean_object* v_pre_353_; 
v_pre_353_ = lean_ctor_get(v_declName_352_, 0);
if (lean_obj_tag(v_pre_353_) == 0)
{
lean_object* v_us_354_; lean_object* v_str_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_us_354_ = lean_ctor_get(v_type_340_, 1);
lean_inc(v_us_354_);
lean_dec_ref_known(v_type_340_, 2);
v_str_355_ = lean_ctor_get(v_declName_352_, 1);
lean_inc_ref(v_str_355_);
lean_dec_ref_known(v_declName_352_, 2);
v___x_356_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12));
v___x_357_ = lean_string_dec_eq(v_str_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__13));
v___x_359_ = lean_string_dec_eq(v_str_355_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_360_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__14));
v___x_361_ = lean_string_dec_eq(v_str_355_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; uint8_t v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__15));
v___x_363_ = lean_string_dec_eq(v_str_355_, v___x_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_364_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__16));
v___x_365_ = lean_string_dec_eq(v_str_355_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; uint8_t v___x_367_; 
v___x_366_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__17));
v___x_367_ = lean_string_dec_eq(v_str_355_, v___x_366_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__18));
v___x_369_ = lean_string_dec_eq(v_str_355_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__19));
v___x_371_ = lean_string_dec_eq(v_str_355_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__20));
v___x_373_ = lean_string_dec_eq(v_str_355_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__21));
v___x_375_ = lean_string_dec_eq(v_str_355_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__22));
v___x_377_ = lean_string_dec_eq(v_str_355_, v___x_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_378_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__23));
v___x_379_ = lean_string_dec_eq(v_str_355_, v___x_378_);
lean_dec_ref(v_str_355_);
if (v___x_379_ == 0)
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
else
{
if (lean_obj_tag(v_us_354_) == 0)
{
v_code_231_ = v_code_351_;
goto v___jp_230_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
v_code_231_ = v_code_351_;
goto v___jp_230_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
v_code_231_ = v_code_351_;
goto v___jp_230_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
v___y_285_ = v___x_350_;
v___y_286_ = v_code_351_;
goto v___jp_284_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
v___y_285_ = v___x_350_;
v___y_286_ = v_code_351_;
goto v___jp_284_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
lean_object* v_code_380_; 
v_code_380_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25);
v_code_231_ = v_code_380_;
goto v___jp_230_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
lean_object* v_code_381_; 
v_code_381_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27);
v_code_231_ = v_code_381_;
goto v___jp_230_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
lean_object* v_code_382_; 
v_code_382_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29);
v_code_231_ = v_code_382_;
goto v___jp_230_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
lean_object* v_code_383_; 
v_code_383_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31);
v_code_231_ = v_code_383_;
goto v___jp_230_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
lean_object* v_code_384_; 
v_code_384_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33);
v_code_231_ = v_code_384_;
goto v___jp_230_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
v___y_292_ = v___x_350_;
v___y_293_ = v_code_351_;
goto v___jp_291_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref(v_str_355_);
if (lean_obj_tag(v_us_354_) == 0)
{
v___y_292_ = v___x_350_;
v___y_293_ = v_code_351_;
goto v___jp_291_;
}
else
{
lean_dec(v_us_354_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
else
{
lean_dec_ref_known(v_declName_352_, 2);
lean_dec_ref_known(v_type_340_, 2);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
else
{
lean_dec(v_declName_352_);
lean_dec_ref_known(v_type_340_, 2);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
else
{
lean_dec_ref(v_type_340_);
v___y_298_ = v_code_351_;
goto v___jp_297_;
}
}
}
}
else
{
lean_object* v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v___x_337_);
lean_dec_ref(v_env_228_);
v___x_402_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34));
v___x_403_ = 1;
v___x_404_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_229_, v___x_403_);
v___x_405_ = lean_string_append(v___x_402_, v___x_404_);
lean_dec_ref(v___x_404_);
v___x_406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
}
v___jp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_runtimeDecl_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_mk_empty_array_with_capacity(v___x_232_);
v___x_234_ = lean_array_push(v___x_233_, v_constName_229_);
v_runtimeDecl_235_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl(v_code_231_, v___x_234_);
lean_dec_ref(v_code_231_);
v___x_236_ = lean_eval_bytecode_decl(v_env_228_, v_runtimeDecl_235_);
lean_dec_ref(v_runtimeDecl_235_);
lean_dec_ref(v_env_228_);
v___x_237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
v___jp_238_:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__3, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__3_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__3);
v___x_240_ = l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__0(v___x_239_);
return v___x_240_;
}
v___jp_241_:
{
lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_243_ = lean_array_get_size(v___y_242_);
lean_dec_ref(v___y_242_);
v___x_244_ = lean_unsigned_to_nat(16u);
v___x_245_ = lean_nat_dec_le(v___x_243_, v___x_244_);
if (v___x_245_ == 0)
{
lean_dec(v_constName_229_);
lean_dec_ref(v_env_228_);
goto v___jp_238_;
}
else
{
lean_object* v_code_246_; 
v_code_246_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5);
v_code_231_ = v_code_246_;
goto v___jp_230_;
}
}
v___jp_247_:
{
if (v___y_249_ == 0)
{
lean_dec_ref(v___y_248_);
lean_dec(v_constName_229_);
lean_dec_ref(v_env_228_);
goto v___jp_238_;
}
else
{
v___y_242_ = v___y_248_;
goto v___jp_241_;
}
}
v___jp_250_:
{
uint8_t v___x_256_; 
v___x_256_ = lean_nat_dec_lt(v___y_252_, v___y_251_);
if (v___x_256_ == 0)
{
lean_dec(v___y_251_);
v___y_242_ = v___y_253_;
goto v___jp_241_;
}
else
{
if (v___x_256_ == 0)
{
lean_dec(v___y_251_);
v___y_242_ = v___y_253_;
goto v___jp_241_;
}
else
{
size_t v___x_257_; size_t v___x_258_; uint8_t v___x_259_; 
v___x_257_ = ((size_t)0ULL);
v___x_258_ = lean_usize_of_nat(v___y_251_);
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1(v___y_251_, v___y_255_, v___y_253_, v___x_257_, v___x_258_);
lean_dec(v___y_251_);
if (v___x_259_ == 0)
{
v___y_242_ = v___y_253_;
goto v___jp_241_;
}
else
{
v___y_248_ = v___y_253_;
v___y_249_ = v___y_254_;
goto v___jp_247_;
}
}
}
}
v___jp_260_:
{
if (v___y_265_ == 0)
{
lean_dec(v___y_262_);
v___y_248_ = v___y_263_;
v___y_249_ = v___y_264_;
goto v___jp_247_;
}
else
{
v___y_251_ = v___y_262_;
v___y_252_ = v___y_261_;
v___y_253_ = v___y_263_;
v___y_254_ = v___y_264_;
v___y_255_ = v___y_265_;
goto v___jp_250_;
}
}
v___jp_266_:
{
if (v___y_271_ == 0)
{
v___y_261_ = v___y_268_;
v___y_262_ = v___y_267_;
v___y_263_ = v___y_269_;
v___y_264_ = v___y_270_;
v___y_265_ = v___y_270_;
goto v___jp_260_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = lean_nat_dec_lt(v___y_268_, v___y_267_);
if (v___x_272_ == 0)
{
v___y_251_ = v___y_267_;
v___y_252_ = v___y_268_;
v___y_253_ = v___y_269_;
v___y_254_ = v___y_270_;
v___y_255_ = v___y_271_;
goto v___jp_250_;
}
else
{
if (v___x_272_ == 0)
{
v___y_251_ = v___y_267_;
v___y_252_ = v___y_268_;
v___y_253_ = v___y_269_;
v___y_254_ = v___y_270_;
v___y_255_ = v___y_271_;
goto v___jp_250_;
}
else
{
size_t v___x_273_; size_t v___x_274_; uint8_t v___x_275_; 
v___x_273_ = ((size_t)0ULL);
v___x_274_ = lean_usize_of_nat(v___y_267_);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__2(v___y_267_, v___y_271_, v___y_269_, v___x_273_, v___x_274_);
if (v___x_275_ == 0)
{
v___y_251_ = v___y_267_;
v___y_252_ = v___y_268_;
v___y_253_ = v___y_269_;
v___y_254_ = v___y_270_;
v___y_255_ = v___x_272_;
goto v___jp_250_;
}
else
{
v___y_261_ = v___y_268_;
v___y_262_ = v___y_267_;
v___y_263_ = v___y_269_;
v___y_264_ = v___y_270_;
v___y_265_ = v___y_270_;
goto v___jp_260_;
}
}
}
}
}
v___jp_276_:
{
uint8_t v___x_283_; 
v___x_283_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v___y_279_);
lean_dec_ref(v___y_279_);
if (v___x_283_ == 0)
{
v___y_267_ = v___y_278_;
v___y_268_ = v___y_277_;
v___y_269_ = v___y_280_;
v___y_270_ = v___y_281_;
v___y_271_ = v___y_282_;
goto v___jp_266_;
}
else
{
v___y_267_ = v___y_278_;
v___y_268_ = v___y_277_;
v___y_269_ = v___y_280_;
v___y_270_ = v___y_281_;
v___y_271_ = v___y_281_;
goto v___jp_266_;
}
}
v___jp_284_:
{
uint32_t v___x_287_; uint32_t v___x_288_; lean_object* v___x_289_; lean_object* v_code_290_; 
v___x_287_ = 1;
v___x_288_ = l_Lean_Compiler_Bytecode_Instruction_inc(v___y_285_, v___x_287_);
v___x_289_ = lean_box_uint32(v___x_288_);
v_code_290_ = lean_array_push(v___y_286_, v___x_289_);
v_code_231_ = v_code_290_;
goto v___jp_230_;
}
v___jp_291_:
{
uint32_t v___x_294_; lean_object* v___x_295_; lean_object* v_code_296_; 
v___x_294_ = l_Lean_Compiler_Bytecode_Instruction_boxSmall(v___y_292_, v___y_292_);
v___x_295_ = lean_box_uint32(v___x_294_);
v_code_296_ = lean_array_push(v___y_293_, v___x_295_);
v_code_231_ = v_code_296_;
goto v___jp_230_;
}
v___jp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__7, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__7_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__7);
v___x_300_ = l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__4(v___x_299_);
if (lean_obj_tag(v___x_300_) == 0)
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec_ref(v___y_298_);
lean_dec(v_constName_229_);
lean_dec_ref(v_env_228_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
else
{
lean_dec_ref_known(v___x_300_, 1);
v_code_231_ = v___y_298_;
goto v___jp_230_;
}
}
v___jp_310_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_runtimeDecl_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_mk_empty_array_with_capacity(v___x_311_);
v___x_313_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5);
v___x_314_ = lean_array_push(v___x_312_, v_boxedName_309_);
v_runtimeDecl_315_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl(v___x_313_, v___x_314_);
v___x_316_ = lean_eval_bytecode_decl(v_env_228_, v_runtimeDecl_315_);
lean_dec_ref(v_runtimeDecl_315_);
lean_dec_ref(v_env_228_);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* lean_eval_const(lean_object* v_env_407_, lean_object* v___opts_408_, lean_object* v_constName_409_){
_start:
{
lean_object* v___x_410_; 
lean_dec_ref(v___opts_408_);
v___x_410_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_407_, v_constName_409_);
return v___x_410_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(lean_object* v_e_411_){
_start:
{
if (lean_obj_tag(v_e_411_) == 0)
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_421_; 
v_a_413_ = lean_ctor_get(v_e_411_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_e_411_);
if (v_isSharedCheck_421_ == 0)
{
v___x_415_ = v_e_411_;
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v_e_411_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_421_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_mk_io_user_error(v_a_413_);
if (v_isShared_416_ == 0)
{
lean_ctor_set_tag(v___x_415_, 1);
lean_ctor_set(v___x_415_, 0, v___x_417_);
v___x_419_ = v___x_415_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
v_a_422_ = lean_ctor_get(v_e_411_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v_e_411_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v_e_411_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v_e_411_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 0);
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_411_ = stack[0].m_obj;
lean_object* v_res_430_;
v_res_430_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v_e_411_);
stack->m_obj
 = v_res_430_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg___boxed(lean_object* v_e_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v_e_431_);
return v_res_433_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0(lean_object* v_00_u03b1_434_, lean_object* v_e_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v_e_435_);
return v___x_437_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_435_ = stack[1].m_obj;
lean_object* v_res_438_;
v_res_438_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0(lean_box(0), v_e_435_);
stack->m_obj
 = v_res_438_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___boxed(lean_object* v_00_u03b1_439_, lean_object* v_e_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0(v_00_u03b1_439_, v_e_440_);
return v_res_442_;
}
}
lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg(lean_object* v_env_445_, lean_object* v_decl_446_, lean_object* v_initDecl_447_){
_start:
{
lean_object* v___x_449_; 
lean_inc(v_decl_446_);
lean_inc_ref(v_env_445_);
v___x_449_ = lean_find_bytecode_decl(v_env_445_, v_decl_446_);
if (lean_obj_tag(v___x_449_) == 1)
{
lean_object* v_val_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v_decl_446_);
v_val_450_ = lean_ctor_get(v___x_449_, 0);
lean_inc(v_val_450_);
lean_dec_ref_known(v___x_449_, 1);
v___x_451_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_445_, v_initDecl_447_);
v___x_452_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v___x_451_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; lean_object* v___x_454_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v___x_454_ = lean_apply_1(v_a_453_, lean_box(0));
if (lean_obj_tag(v___x_454_) == 0)
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_464_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_464_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_459_ = lean_runtime_mark_persistent(v_a_455_);
v___x_460_ = lean_bytecode_store_init_value(v_val_450_, v___x_459_);
lean_dec(v_val_450_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 0, v___x_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
lean_dec(v_val_450_);
v_a_465_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_454_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_454_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
else
{
lean_object* v_a_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_480_; 
lean_dec(v_val_450_);
v_a_473_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_480_ == 0)
{
v___x_475_ = v___x_452_;
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_a_473_);
lean_dec(v___x_452_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_480_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_478_; 
if (v_isShared_476_ == 0)
{
v___x_478_ = v___x_475_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_a_473_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
}
}
else
{
lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec(v___x_449_);
lean_dec(v_initDecl_447_);
lean_dec_ref(v_env_445_);
v___x_481_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___closed__0));
v___x_482_ = 1;
v___x_483_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_446_, v___x_482_);
v___x_484_ = lean_string_append(v___x_481_, v___x_483_);
lean_dec_ref(v___x_483_);
v___x_485_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___closed__1));
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
v___x_487_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
v___x_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_445_ = stack[0].m_obj;
lean_object* v_decl_446_ = stack[1].m_obj;
lean_object* v_initDecl_447_ = stack[2].m_obj;
lean_object* v_res_489_;
v_res_489_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg(v_env_445_, v_decl_446_, v_initDecl_447_);
stack->m_obj
 = v_res_489_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___boxed(lean_object* v_env_490_, lean_object* v_decl_491_, lean_object* v_initDecl_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg(v_env_490_, v_decl_491_, v_initDecl_492_);
return v_res_494_;
}
}
lean_object* lean_run_init(lean_object* v_env_495_, lean_object* v_opts_496_, lean_object* v_decl_497_, lean_object* v_initDecl_498_){
_start:
{
lean_object* v___x_500_; 
lean_dec_ref(v_opts_496_);
v___x_500_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg(v_env_495_, v_decl_497_, v_initDecl_498_);
return v___x_500_;
}
}
LEAN_EXPORT void lean_run_init_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_495_ = stack[0].m_obj;
lean_object* v_opts_496_ = stack[1].m_obj;
lean_object* v_decl_497_ = stack[2].m_obj;
lean_object* v_initDecl_498_ = stack[3].m_obj;
lean_object* v_res_501_;
v_res_501_ = lean_run_init(v_env_495_, v_opts_496_, v_decl_497_, v_initDecl_498_);
stack->m_obj
 = v_res_501_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___boxed(lean_object* v_env_502_, lean_object* v_opts_503_, lean_object* v_decl_504_, lean_object* v_initDecl_505_, lean_object* v_a_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = lean_run_init(v_env_502_, v_opts_503_, v_decl_504_, v_initDecl_505_);
return v_res_507_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_showError_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_509_ = stack[1].m_obj;
lean_object* v_res_511_;
v_res_511_ = lean_io_result_show_error(v_e_509_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_showError___boxed(lean_object* v_00_u03b1_512_, lean_object* v_e_513_, lean_object* v_a_00___x40___internal___hyg_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = lean_io_result_show_error(v_e_513_);
lean_dec_ref(v_e_513_);
return v_res_515_;
}
}
uint8_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit(lean_object* v_e_519_){
_start:
{
if (lean_obj_tag(v_e_519_) == 5)
{
lean_object* v_fn_520_; 
v_fn_520_ = lean_ctor_get(v_e_519_, 0);
if (lean_obj_tag(v_fn_520_) == 4)
{
lean_object* v_declName_521_; 
v_declName_521_ = lean_ctor_get(v_fn_520_, 0);
if (lean_obj_tag(v_declName_521_) == 1)
{
lean_object* v_pre_522_; 
v_pre_522_ = lean_ctor_get(v_declName_521_, 0);
if (lean_obj_tag(v_pre_522_) == 0)
{
lean_object* v_arg_523_; lean_object* v_str_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_arg_523_ = lean_ctor_get(v_e_519_, 1);
v_str_524_ = lean_ctor_get(v_declName_521_, 1);
v___x_525_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__0));
v___x_526_ = lean_string_dec_eq(v_str_524_, v___x_525_);
if (v___x_526_ == 0)
{
return v___x_526_;
}
else
{
if (lean_obj_tag(v_arg_523_) == 4)
{
lean_object* v_declName_527_; 
v_declName_527_ = lean_ctor_get(v_arg_523_, 0);
if (lean_obj_tag(v_declName_527_) == 1)
{
lean_object* v_pre_528_; 
v_pre_528_ = lean_ctor_get(v_declName_527_, 0);
if (lean_obj_tag(v_pre_528_) == 0)
{
lean_object* v_str_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_str_529_ = lean_ctor_get(v_declName_527_, 1);
v___x_530_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__1));
v___x_531_ = lean_string_dec_eq(v_str_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; uint8_t v___x_533_; 
v___x_532_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__2));
v___x_533_ = lean_string_dec_eq(v_str_529_, v___x_532_);
return v___x_533_;
}
else
{
return v___x_531_;
}
}
else
{
uint8_t v___x_534_; 
v___x_534_ = 0;
return v___x_534_;
}
}
else
{
uint8_t v___x_535_; 
v___x_535_ = 0;
return v___x_535_;
}
}
else
{
uint8_t v___x_536_; 
v___x_536_ = 0;
return v___x_536_;
}
}
}
else
{
uint8_t v___x_537_; 
v___x_537_ = 0;
return v___x_537_;
}
}
else
{
uint8_t v___x_538_; 
v___x_538_ = 0;
return v___x_538_;
}
}
else
{
uint8_t v___x_539_; 
v___x_539_ = 0;
return v___x_539_;
}
}
else
{
uint8_t v___x_540_; 
v___x_540_ = 0;
return v___x_540_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_519_ = stack[0].m_obj;
uint8_t v_res_541_;
v_res_541_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit(v_e_519_);
stack->m_num = v_res_541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___boxed(lean_object* v_e_542_){
_start:
{
uint8_t v_res_543_; lean_object* v_r_544_; 
v_res_543_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit(v_e_542_);
lean_dec_ref(v_e_542_);
v_r_544_ = lean_box(v_res_543_);
return v_r_544_;
}
}
uint8_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUInt32(lean_object* v_e_545_){
_start:
{
if (lean_obj_tag(v_e_545_) == 5)
{
lean_object* v_fn_546_; 
v_fn_546_ = lean_ctor_get(v_e_545_, 0);
if (lean_obj_tag(v_fn_546_) == 4)
{
lean_object* v_declName_547_; 
v_declName_547_ = lean_ctor_get(v_fn_546_, 0);
if (lean_obj_tag(v_declName_547_) == 1)
{
lean_object* v_pre_548_; 
v_pre_548_ = lean_ctor_get(v_declName_547_, 0);
if (lean_obj_tag(v_pre_548_) == 0)
{
lean_object* v_arg_549_; lean_object* v_str_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v_arg_549_ = lean_ctor_get(v_e_545_, 1);
v_str_550_ = lean_ctor_get(v_declName_547_, 1);
v___x_551_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit___closed__0));
v___x_552_ = lean_string_dec_eq(v_str_550_, v___x_551_);
if (v___x_552_ == 0)
{
return v___x_552_;
}
else
{
if (lean_obj_tag(v_arg_549_) == 4)
{
lean_object* v_declName_553_; 
v_declName_553_ = lean_ctor_get(v_arg_549_, 0);
if (lean_obj_tag(v_declName_553_) == 1)
{
lean_object* v_pre_554_; 
v_pre_554_ = lean_ctor_get(v_declName_553_, 0);
if (lean_obj_tag(v_pre_554_) == 0)
{
lean_object* v_str_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_str_555_ = lean_ctor_get(v_declName_553_, 1);
v___x_556_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__14));
v___x_557_ = lean_string_dec_eq(v_str_555_, v___x_556_);
return v___x_557_;
}
else
{
uint8_t v___x_558_; 
v___x_558_ = 0;
return v___x_558_;
}
}
else
{
uint8_t v___x_559_; 
v___x_559_ = 0;
return v___x_559_;
}
}
else
{
uint8_t v___x_560_; 
v___x_560_ = 0;
return v___x_560_;
}
}
}
else
{
uint8_t v___x_561_; 
v___x_561_ = 0;
return v___x_561_;
}
}
else
{
uint8_t v___x_562_; 
v___x_562_ = 0;
return v___x_562_;
}
}
else
{
uint8_t v___x_563_; 
v___x_563_ = 0;
return v___x_563_;
}
}
else
{
uint8_t v___x_564_; 
v___x_564_ = 0;
return v___x_564_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUInt32_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_545_ = stack[0].m_obj;
uint8_t v_res_565_;
v_res_565_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUInt32(v_e_545_);
stack->m_num = v_res_565_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUInt32___boxed(lean_object* v_e_566_){
_start:
{
uint8_t v_res_567_; lean_object* v_r_568_; 
v_res_567_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUInt32(v_e_566_);
lean_dec_ref(v_e_566_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
uint8_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString(lean_object* v_e_571_){
_start:
{
if (lean_obj_tag(v_e_571_) == 5)
{
lean_object* v_fn_572_; 
v_fn_572_ = lean_ctor_get(v_e_571_, 0);
if (lean_obj_tag(v_fn_572_) == 4)
{
lean_object* v_declName_573_; 
v_declName_573_ = lean_ctor_get(v_fn_572_, 0);
if (lean_obj_tag(v_declName_573_) == 1)
{
lean_object* v_pre_574_; 
v_pre_574_ = lean_ctor_get(v_declName_573_, 0);
if (lean_obj_tag(v_pre_574_) == 0)
{
lean_object* v_arg_575_; lean_object* v_str_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v_arg_575_ = lean_ctor_get(v_e_571_, 1);
v_str_576_ = lean_ctor_get(v_declName_573_, 1);
v___x_577_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString___closed__0));
v___x_578_ = lean_string_dec_eq(v_str_576_, v___x_577_);
if (v___x_578_ == 0)
{
return v___x_578_;
}
else
{
if (lean_obj_tag(v_arg_575_) == 4)
{
lean_object* v_declName_579_; 
v_declName_579_ = lean_ctor_get(v_arg_575_, 0);
if (lean_obj_tag(v_declName_579_) == 1)
{
lean_object* v_pre_580_; 
v_pre_580_ = lean_ctor_get(v_declName_579_, 0);
if (lean_obj_tag(v_pre_580_) == 0)
{
lean_object* v_str_581_; lean_object* v___x_582_; uint8_t v___x_583_; 
v_str_581_ = lean_ctor_get(v_declName_579_, 1);
v___x_582_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString___closed__1));
v___x_583_ = lean_string_dec_eq(v_str_581_, v___x_582_);
return v___x_583_;
}
else
{
uint8_t v___x_584_; 
v___x_584_ = 0;
return v___x_584_;
}
}
else
{
uint8_t v___x_585_; 
v___x_585_ = 0;
return v___x_585_;
}
}
else
{
uint8_t v___x_586_; 
v___x_586_ = 0;
return v___x_586_;
}
}
}
else
{
uint8_t v___x_587_; 
v___x_587_ = 0;
return v___x_587_;
}
}
else
{
uint8_t v___x_588_; 
v___x_588_ = 0;
return v___x_588_;
}
}
else
{
uint8_t v___x_589_; 
v___x_589_ = 0;
return v___x_589_;
}
}
else
{
uint8_t v___x_590_; 
v___x_590_ = 0;
return v___x_590_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_571_ = stack[0].m_obj;
uint8_t v_res_591_;
v_res_591_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString(v_e_571_);
stack->m_num = v_res_591_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString___boxed(lean_object* v_e_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString(v_e_592_);
lean_dec_ref(v_e_592_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg(lean_object* v_info_596_){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_598_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg___closed__0));
v___x_599_ = l_Lean_ConstantInfo_type(v_info_596_);
v___x_600_ = lean_expr_dbg_to_string(v___x_599_);
lean_dec_ref(v___x_599_);
v___x_601_ = lean_string_append(v___x_598_, v___x_600_);
lean_dec_ref(v___x_600_);
v___x_602_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_596_ = stack[0].m_obj;
lean_object* v_res_604_;
v_res_604_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg(v_info_596_);
stack->m_obj
 = v_res_604_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg___boxed(lean_object* v_info_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg(v_info_605_);
lean_dec_ref(v_info_605_);
return v_res_607_;
}
}
lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain(lean_object* v_info_608_, lean_object* v_x_609_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg(v_info_608_);
return v___x_611_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_608_ = stack[0].m_obj;
lean_object* v_x_609_ = stack[1].m_obj;
lean_object* v_res_612_;
v_res_612_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain(v_info_608_, v_x_609_);
stack->m_obj
 = v_res_612_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___boxed(lean_object* v_info_613_, lean_object* v_x_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain(v_info_613_, v_x_614_);
lean_dec_ref(v_info_613_);
return v_res_616_;
}
}
uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg(lean_object* v_env_623_, lean_object* v_args_624_){
_start:
{
lean_object* v___y_627_; lean_object* v___y_631_; lean_object* v___x_634_; uint8_t v___x_635_; lean_object* v___x_636_; 
v___x_634_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__1));
v___x_635_ = 0;
lean_inc_ref(v_env_623_);
v___x_636_ = l_Lean_Environment_find_x3f(v_env_623_, v___x_634_, v___x_635_);
if (lean_obj_tag(v___x_636_) == 1)
{
lean_object* v_val_637_; lean_object* v___x_638_; 
v_val_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_val_637_);
lean_dec_ref_known(v___x_636_, 1);
v___x_638_ = l_Lean_ConstantInfo_type(v_val_637_);
if (lean_obj_tag(v___x_638_) == 7)
{
lean_object* v_binderType_639_; lean_object* v_body_640_; uint8_t v___x_641_; 
v_binderType_639_ = lean_ctor_get(v___x_638_, 1);
lean_inc_ref(v_binderType_639_);
v_body_640_ = lean_ctor_get(v___x_638_, 2);
lean_inc_ref(v_body_640_);
lean_dec_ref_known(v___x_638_, 3);
v___x_641_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isListString(v_binderType_639_);
lean_dec_ref(v_binderType_639_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_dec_ref(v_body_640_);
lean_dec(v_args_624_);
lean_dec_ref(v_env_623_);
v___x_642_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg(v_val_637_);
lean_dec(v_val_637_);
v___y_631_ = v___x_642_;
goto v___jp_630_;
}
else
{
uint8_t v___x_643_; 
v___x_643_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUInt32(v_body_640_);
if (v___x_643_ == 0)
{
uint8_t v___x_644_; 
v___x_644_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit(v_body_640_);
lean_dec_ref(v_body_640_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec(v_args_624_);
lean_dec_ref(v_env_623_);
v___x_645_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg(v_val_637_);
lean_dec(v_val_637_);
v___y_631_ = v___x_645_;
goto v___jp_630_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec(v_val_637_);
v___x_646_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_623_, v___x_634_);
v___x_647_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v___x_646_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_649_; 
v_a_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v___x_647_, 1);
v___x_649_ = lean_apply_2(v_a_648_, v_args_624_, lean_box(0));
if (lean_obj_tag(v___x_649_) == 0)
{
uint32_t v___x_650_; 
lean_dec_ref_known(v___x_649_, 1);
v___x_650_ = 0;
return v___x_650_;
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
v_a_651_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_649_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
v___y_627_ = v___x_656_;
goto v___jp_626_;
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec(v_args_624_);
v_a_659_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_647_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_647_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v___y_627_ = v___x_664_;
goto v___jp_626_;
}
}
}
}
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec_ref(v_body_640_);
lean_dec(v_val_637_);
v___x_667_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_623_, v___x_634_);
v___x_668_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v___x_667_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v___x_670_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v___x_670_ = lean_apply_2(v_a_669_, v_args_624_, lean_box(0));
v___y_631_ = v___x_670_;
goto v___jp_630_;
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v_args_624_);
v_a_671_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_668_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_668_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
v___y_627_ = v___x_676_;
goto v___jp_626_;
}
}
}
}
}
}
else
{
uint8_t v___x_679_; 
lean_dec(v_args_624_);
v___x_679_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUInt32(v___x_638_);
if (v___x_679_ == 0)
{
uint8_t v___x_680_; 
v___x_680_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_isIOUnit(v___x_638_);
lean_dec_ref(v___x_638_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; 
lean_dec_ref(v_env_623_);
v___x_681_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain_invalidMain___redArg(v_val_637_);
lean_dec(v_val_637_);
v___y_631_ = v___x_681_;
goto v___jp_630_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v_val_637_);
v___x_682_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_623_, v___x_634_);
v___x_683_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v___x_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_685_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
v___x_685_ = lean_apply_1(v_a_684_, lean_box(0));
if (lean_obj_tag(v___x_685_) == 0)
{
uint32_t v___x_686_; 
lean_dec_ref_known(v___x_685_, 1);
v___x_686_ = 0;
return v___x_686_;
}
else
{
lean_object* v_a_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_694_; 
v_a_687_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_694_ == 0)
{
v___x_689_ = v___x_685_;
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_a_687_);
lean_dec(v___x_685_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_694_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_692_; 
if (v_isShared_690_ == 0)
{
v___x_692_ = v___x_689_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v_a_687_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
v___y_627_ = v___x_692_;
goto v___jp_626_;
}
}
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
v_a_695_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_683_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_683_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
v___y_627_ = v___x_700_;
goto v___jp_626_;
}
}
}
}
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec_ref(v___x_638_);
lean_dec(v_val_637_);
v___x_703_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_623_, v___x_634_);
v___x_704_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v___x_703_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_object* v_a_705_; lean_object* v___x_706_; 
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_704_, 1);
v___x_706_ = lean_apply_1(v_a_705_, lean_box(0));
v___y_631_ = v___x_706_;
goto v___jp_630_;
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_a_707_ = lean_ctor_get(v___x_704_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_704_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_704_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
v___y_627_ = v___x_712_;
goto v___jp_626_;
}
}
}
}
}
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec(v___x_636_);
lean_dec(v_args_624_);
lean_dec_ref(v_env_623_);
v___x_715_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__3));
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___y_627_ = v___x_716_;
goto v___jp_626_;
}
v___jp_626_:
{
lean_object* v___x_628_; uint32_t v___x_629_; 
v___x_628_ = lean_io_result_show_error(v___y_627_);
lean_dec_ref(v___y_627_);
v___x_629_ = 1;
return v___x_629_;
}
v___jp_630_:
{
if (lean_obj_tag(v___y_631_) == 0)
{
lean_object* v_a_632_; uint32_t v___x_633_; 
v_a_632_ = lean_ctor_get(v___y_631_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v___y_631_, 1);
v___x_633_ = lean_unbox_uint32(v_a_632_);
lean_dec(v_a_632_);
return v___x_633_;
}
else
{
v___y_627_ = v___y_631_;
goto v___jp_626_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_623_ = stack[0].m_obj;
lean_object* v_args_624_ = stack[1].m_obj;
uint32_t v_res_717_;
v_res_717_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg(v_env_623_, v_args_624_);
stack->m_num = v_res_717_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___boxed(lean_object* v_env_718_, lean_object* v_args_719_, lean_object* v_void_720_){
_start:
{
uint32_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg(v_env_718_, v_args_719_);
v_r_722_ = lean_box_uint32(v_res_721_);
return v_r_722_;
}
}
uint32_t lean_eval_main(lean_object* v_env_723_, lean_object* v_opts_724_, lean_object* v_args_725_){
_start:
{
uint32_t v___x_727_; 
lean_dec_ref(v_opts_724_);
v___x_727_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg(v_env_723_, v_args_725_);
return v___x_727_;
}
}
LEAN_EXPORT void lean_eval_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_723_ = stack[0].m_obj;
lean_object* v_opts_724_ = stack[1].m_obj;
lean_object* v_args_725_ = stack[2].m_obj;
uint32_t v_res_728_;
v_res_728_ = lean_eval_main(v_env_723_, v_opts_724_, v_args_725_);
stack->m_num = v_res_728_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___boxed(lean_object* v_env_729_, lean_object* v_opts_730_, lean_object* v_args_731_, lean_object* v_void_732_){
_start:
{
uint32_t v_res_733_; lean_object* v_r_734_; 
v_res_733_ = lean_eval_main(v_env_729_, v_opts_730_, v_args_731_);
v_r_734_ = lean_box_uint32(v_res_733_);
return v_r_734_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Bytecode_Instruction(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_Bytecode_Eval(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Bytecode_Instruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__2 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__2();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl___closed__2___boxed__const__2);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_Bytecode_Eval(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Bytecode_Instruction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_Bytecode_Eval(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Bytecode_Instruction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Bytecode_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_Bytecode_Eval(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_Bytecode_Eval(builtin);
}
#ifdef __cplusplus
}
#endif
