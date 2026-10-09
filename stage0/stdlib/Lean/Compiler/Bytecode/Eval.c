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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3(uint8_t, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "(interpreter) unknown declaration "};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__8 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "cannot evaluate code because '"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__9 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "' uses 'sorry' and/or contains errors"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10_value;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__13 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__13_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__14 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__14_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__15 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__15_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__16 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__16_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__17 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__17_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Float"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__18 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__18_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Float32"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__19 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__19_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "tobj"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__20 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__20_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "obj"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__21 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__21_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "tagged"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__22 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__22_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "lcErased"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__23 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__23_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lcVoid"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__24 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__24_value;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34___boxed__const__1;
static lean_once_cell_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34;
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
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Invalid type for `main`: "};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "main"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__0 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 14, 67, 68, 149, 142, 182, 10)}};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__1 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__2 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__3 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IO"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__4 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__15_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__5 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__6 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__7 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__8 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__8_value;
static const lean_ctor_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__9 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Could not find `main`"};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__10 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__10_value)}};
static const lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__11 = (const lean_object*)&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__11_value;
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
uint8_t v___y_3450__boxed_89_; size_t v_i_boxed_90_; size_t v_stop_boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v___y_3450__boxed_89_ = lean_unbox(v___y_85_);
v_i_boxed_90_ = lean_unbox_usize(v_i_87_);
lean_dec(v_i_87_);
v_stop_boxed_91_ = lean_unbox_usize(v_stop_88_);
lean_dec(v_stop_88_);
v_res_92_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__2(v___x_84_, v___y_3450__boxed_89_, v_as_86_, v_i_boxed_90_, v_stop_boxed_91_);
lean_dec_ref(v_as_86_);
lean_dec(v___x_84_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3(uint8_t v___x_94_, lean_object* v___x_95_, lean_object* v_as_96_, size_t v_i_97_, size_t v_stop_98_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_eq(v_i_97_, v_stop_98_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; uint8_t v_borrow_105_; uint8_t v___x_106_; uint8_t v___y_108_; 
v___x_104_ = lean_array_uget_borrowed(v_as_96_, v_i_97_);
v_borrow_105_ = lean_ctor_get_uint8(v___x_104_, sizeof(void*)*3);
v___x_106_ = 1;
if (v_borrow_105_ == 0)
{
if (v___x_94_ == 0)
{
goto v___jp_99_;
}
else
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_nat_dec_eq(v___x_95_, v___x_109_);
v___y_108_ = v___x_110_;
goto v___jp_107_;
}
}
else
{
v___y_108_ = v___x_94_;
goto v___jp_107_;
}
v___jp_107_:
{
if (v___y_108_ == 0)
{
goto v___jp_99_;
}
else
{
return v___x_106_;
}
}
}
else
{
uint8_t v___x_111_; 
v___x_111_ = 0;
return v___x_111_;
}
v___jp_99_:
{
size_t v___x_100_; size_t v___x_101_; 
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_add(v_i_97_, v___x_100_);
v_i_97_ = v___x_101_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_94_ = stack[0].m_num;
lean_object* v___x_95_ = stack[1].m_obj;
lean_object* v_as_96_ = stack[2].m_obj;
size_t v_i_97_ = stack[3].m_num;
size_t v_stop_98_ = stack[4].m_num;
uint8_t v_res_112_;
v_res_112_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3(v___x_94_, v___x_95_, v_as_96_, v_i_97_, v_stop_98_);
stack->m_num = v_res_112_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3___boxed(lean_object* v___x_113_, lean_object* v___x_114_, lean_object* v_as_115_, lean_object* v_i_116_, lean_object* v_stop_117_){
_start:
{
uint8_t v___x_3495__boxed_118_; size_t v_i_boxed_119_; size_t v_stop_boxed_120_; uint8_t v_res_121_; lean_object* v_r_122_; 
v___x_3495__boxed_118_ = lean_unbox(v___x_113_);
v_i_boxed_119_ = lean_unbox_usize(v_i_116_);
lean_dec(v_i_116_);
v_stop_boxed_120_ = lean_unbox_usize(v_stop_117_);
lean_dec(v_stop_117_);
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3(v___x_3495__boxed_118_, v___x_114_, v_as_115_, v_i_boxed_119_, v_stop_boxed_120_);
lean_dec_ref(v_as_115_);
lean_dec(v___x_114_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1(lean_object* v___x_123_, uint8_t v___y_124_, lean_object* v_as_125_, size_t v_i_126_, size_t v_stop_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = lean_usize_dec_eq(v_i_126_, v_stop_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v_type_130_; uint8_t v___x_131_; uint8_t v___y_133_; uint8_t v___x_137_; 
v___x_129_ = lean_array_uget_borrowed(v_as_125_, v_i_126_);
v_type_130_ = lean_ctor_get(v___x_129_, 2);
v___x_131_ = 1;
v___x_137_ = l_Lean_Expr_isVoid(v_type_130_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_nat_dec_eq(v___x_123_, v___x_138_);
v___y_133_ = v___x_139_;
goto v___jp_132_;
}
else
{
v___y_133_ = v___y_124_;
goto v___jp_132_;
}
v___jp_132_:
{
if (v___y_133_ == 0)
{
size_t v___x_134_; size_t v___x_135_; 
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_add(v_i_126_, v___x_134_);
v_i_126_ = v___x_135_;
goto _start;
}
else
{
return v___x_131_;
}
}
}
else
{
uint8_t v___x_140_; 
v___x_140_ = 0;
return v___x_140_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_123_ = stack[0].m_obj;
uint8_t v___y_124_ = stack[1].m_num;
lean_object* v_as_125_ = stack[2].m_obj;
size_t v_i_126_ = stack[3].m_num;
size_t v_stop_127_ = stack[4].m_num;
uint8_t v_res_141_;
v_res_141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1(v___x_123_, v___y_124_, v_as_125_, v_i_126_, v_stop_127_);
stack->m_num = v_res_141_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1___boxed(lean_object* v___x_142_, lean_object* v___y_143_, lean_object* v_as_144_, lean_object* v_i_145_, lean_object* v_stop_146_){
_start:
{
uint8_t v___y_3542__boxed_147_; size_t v_i_boxed_148_; size_t v_stop_boxed_149_; uint8_t v_res_150_; lean_object* v_r_151_; 
v___y_3542__boxed_147_ = lean_unbox(v___y_143_);
v_i_boxed_148_ = lean_unbox_usize(v_i_145_);
lean_dec(v_i_145_);
v_stop_boxed_149_ = lean_unbox_usize(v_stop_146_);
lean_dec(v_stop_146_);
v_res_150_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1(v___x_142_, v___y_3542__boxed_147_, v_as_144_, v_i_boxed_148_, v_stop_boxed_149_);
lean_dec_ref(v_as_144_);
lean_dec(v___x_142_);
v_r_151_ = lean_box(v_res_150_);
return v_r_151_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__3(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_155_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__2));
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = lean_unsigned_to_nat(70u);
v___x_158_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__1));
v___x_159_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__0));
v___x_160_ = l_mkPanicMessageWithDecl(v___x_159_, v___x_158_, v___x_157_, v___x_156_, v___x_155_);
return v___x_160_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__4(void){
_start:
{
uint32_t v___x_161_; uint32_t v___x_162_; 
v___x_161_ = 0;
v___x_162_ = l_Lean_Compiler_Bytecode_Instruction_pap(v___x_161_, v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__4, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__4_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__4);
v___x_164_ = lean_box_uint32(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_code_168_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = lean_mk_empty_array_with_capacity(v___x_165_);
v___x_167_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5___boxed__const__1;
v_code_168_ = lean_array_push(v___x_166_, v___x_167_);
return v_code_168_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__7(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_170_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__6));
v___x_171_ = lean_unsigned_to_nat(11u);
v___x_172_ = lean_unsigned_to_nat(68u);
v___x_173_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__1));
v___x_174_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__0));
v___x_175_ = l_mkPanicMessageWithDecl(v___x_174_, v___x_173_, v___x_172_, v___x_171_, v___x_170_);
return v___x_175_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11(void){
_start:
{
uint32_t v___x_179_; uint32_t v___x_180_; 
v___x_179_ = 0;
v___x_180_ = l_Lean_Compiler_Bytecode_Instruction_loadConst(v___x_179_);
return v___x_180_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12___boxed__const__1(void){
_start:
{
uint32_t v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__11);
v___x_182_ = lean_box_uint32(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_code_186_; 
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_mk_empty_array_with_capacity(v___x_183_);
v___x_185_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12___boxed__const__1;
v_code_186_ = lean_array_push(v___x_184_, v___x_185_);
return v_code_186_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25(void){
_start:
{
uint32_t v___x_199_; uint32_t v___x_200_; 
v___x_199_ = 0;
v___x_200_ = l_Lean_Compiler_Bytecode_Instruction_boxFloat32(v___x_199_, v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26___boxed__const__1(void){
_start:
{
uint32_t v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__25);
v___x_202_ = lean_box_uint32(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26(void){
_start:
{
lean_object* v_code_203_; lean_object* v___x_204_; lean_object* v_code_205_; 
v_code_203_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12);
v___x_204_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26___boxed__const__1;
v_code_205_ = lean_array_push(v_code_203_, v___x_204_);
return v_code_205_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27(void){
_start:
{
uint32_t v___x_206_; uint32_t v___x_207_; 
v___x_206_ = 0;
v___x_207_ = l_Lean_Compiler_Bytecode_Instruction_boxFloat(v___x_206_, v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28___boxed__const__1(void){
_start:
{
uint32_t v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__27);
v___x_209_ = lean_box_uint32(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28(void){
_start:
{
lean_object* v_code_210_; lean_object* v___x_211_; lean_object* v_code_212_; 
v_code_210_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12);
v___x_211_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28___boxed__const__1;
v_code_212_ = lean_array_push(v_code_210_, v___x_211_);
return v_code_212_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29(void){
_start:
{
uint32_t v___x_213_; uint32_t v___x_214_; 
v___x_213_ = 0;
v___x_214_ = l_Lean_Compiler_Bytecode_Instruction_boxUSize(v___x_213_, v___x_213_);
return v___x_214_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30___boxed__const__1(void){
_start:
{
uint32_t v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__29);
v___x_216_ = lean_box_uint32(v___x_215_);
return v___x_216_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30(void){
_start:
{
lean_object* v_code_217_; lean_object* v___x_218_; lean_object* v_code_219_; 
v_code_217_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12);
v___x_218_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30___boxed__const__1;
v_code_219_ = lean_array_push(v_code_217_, v___x_218_);
return v_code_219_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31(void){
_start:
{
uint32_t v___x_220_; uint32_t v___x_221_; 
v___x_220_ = 0;
v___x_221_ = l_Lean_Compiler_Bytecode_Instruction_boxUInt64(v___x_220_, v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32___boxed__const__1(void){
_start:
{
uint32_t v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__31);
v___x_223_ = lean_box_uint32(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32(void){
_start:
{
lean_object* v_code_224_; lean_object* v___x_225_; lean_object* v_code_226_; 
v_code_224_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12);
v___x_225_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32___boxed__const__1;
v_code_226_ = lean_array_push(v_code_224_, v___x_225_);
return v_code_226_;
}
}
static uint32_t _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33(void){
_start:
{
uint32_t v___x_227_; uint32_t v___x_228_; 
v___x_227_ = 0;
v___x_228_ = l_Lean_Compiler_Bytecode_Instruction_boxUInt32(v___x_227_, v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34___boxed__const__1(void){
_start:
{
uint32_t v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_uint32_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__33);
v___x_230_ = lean_box_uint32(v___x_229_);
return v___x_230_;
}
}
static lean_object* _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34(void){
_start:
{
lean_object* v_code_231_; lean_object* v___x_232_; lean_object* v_code_233_; 
v_code_231_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12);
v___x_232_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34___boxed__const__1;
v_code_233_ = lean_array_push(v_code_231_, v___x_232_);
return v_code_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(lean_object* v_env_234_, lean_object* v_constName_235_){
_start:
{
lean_object* v_code_237_; lean_object* v___y_248_; lean_object* v___y_254_; uint8_t v___y_255_; lean_object* v___y_257_; uint8_t v___y_258_; lean_object* v___y_259_; lean_object* v___y_260_; uint8_t v___y_261_; lean_object* v___y_267_; uint8_t v___y_268_; lean_object* v___y_269_; lean_object* v___y_270_; uint8_t v___y_271_; lean_object* v___y_273_; uint8_t v___y_274_; lean_object* v___y_275_; lean_object* v___y_276_; uint8_t v___y_277_; lean_object* v___y_283_; lean_object* v___y_284_; uint8_t v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; uint8_t v___y_288_; lean_object* v___y_291_; lean_object* v___y_292_; uint8_t v___y_293_; lean_object* v___y_294_; lean_object* v___y_295_; uint8_t v___y_296_; uint32_t v___y_298_; lean_object* v___y_299_; uint32_t v___y_305_; lean_object* v___y_306_; lean_object* v___y_311_; uint8_t v___x_322_; uint8_t v___x_323_; 
v___x_322_ = 1;
lean_inc(v_constName_235_);
lean_inc_ref(v_env_234_);
v___x_323_ = l_Lean_Environment_contains(v_env_234_, v_constName_235_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec_ref(v_env_234_);
v___x_324_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__8));
v___x_325_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_235_, v___x_322_);
v___x_326_ = lean_string_append(v___x_324_, v___x_325_);
lean_dec_ref(v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
return v___x_327_;
}
else
{
lean_object* v_boxedName_328_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_inc(v_constName_235_);
v_boxedName_328_ = l_Lean_Compiler_LCNF_mkBoxedName(v_constName_235_);
v___x_337_ = l_Lean_Compiler_LCNF_impureSigExt;
lean_inc(v_boxedName_328_);
lean_inc_ref(v_env_234_);
v___x_338_ = l_Lean_Compiler_LCNF_getSigCore_x3f___redArg(v_env_234_, v___x_337_, v_boxedName_328_);
if (lean_obj_tag(v___x_338_) == 1)
{
lean_object* v___x_339_; 
lean_dec_ref_known(v___x_338_, 1);
lean_dec(v_constName_235_);
lean_inc(v_boxedName_328_);
lean_inc_ref(v_env_234_);
v___x_339_ = lean_find_bytecode_decl(v_env_234_, v_boxedName_328_);
if (lean_obj_tag(v___x_339_) == 1)
{
lean_object* v_val_340_; lean_object* v_sorryDep_x3f_341_; 
v_val_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_val_340_);
lean_dec_ref_known(v___x_339_, 1);
v_sorryDep_x3f_341_ = lean_ctor_get(v_val_340_, 8);
lean_inc(v_sorryDep_x3f_341_);
lean_dec(v_val_340_);
if (lean_obj_tag(v_sorryDep_x3f_341_) == 1)
{
lean_object* v_val_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_354_; 
lean_dec(v_boxedName_328_);
lean_dec_ref(v_env_234_);
v_val_342_ = lean_ctor_get(v_sorryDep_x3f_341_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v_sorryDep_x3f_341_);
if (v_isSharedCheck_354_ == 0)
{
v___x_344_ = v_sorryDep_x3f_341_;
v_isShared_345_ = v_isSharedCheck_354_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_val_342_);
lean_dec(v_sorryDep_x3f_341_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_354_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
v___x_346_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__9));
v___x_347_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_342_, v___x_323_);
v___x_348_ = lean_string_append(v___x_346_, v___x_347_);
lean_dec_ref(v___x_347_);
v___x_349_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10));
v___x_350_ = lean_string_append(v___x_348_, v___x_349_);
if (v_isShared_345_ == 0)
{
lean_ctor_set_tag(v___x_344_, 0);
lean_ctor_set(v___x_344_, 0, v___x_350_);
v___x_352_ = v___x_344_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___x_350_);
v___x_352_ = v_reuseFailAlloc_353_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
return v___x_352_;
}
}
}
else
{
lean_dec(v_sorryDep_x3f_341_);
goto v___jp_329_;
}
}
else
{
lean_dec(v___x_339_);
goto v___jp_329_;
}
}
else
{
lean_object* v___x_355_; 
lean_dec(v___x_338_);
lean_dec(v_boxedName_328_);
lean_inc(v_constName_235_);
lean_inc_ref(v_env_234_);
v___x_355_ = l_Lean_Compiler_LCNF_getSigCore_x3f___redArg(v_env_234_, v___x_337_, v_constName_235_);
if (lean_obj_tag(v___x_355_) == 1)
{
lean_object* v_val_356_; lean_object* v___x_402_; 
v_val_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_val_356_);
lean_dec_ref_known(v___x_355_, 1);
lean_inc(v_constName_235_);
lean_inc_ref(v_env_234_);
v___x_402_ = lean_find_bytecode_decl(v_env_234_, v_constName_235_);
if (lean_obj_tag(v___x_402_) == 1)
{
lean_object* v_val_403_; lean_object* v_sorryDep_x3f_404_; 
v_val_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v___x_402_, 1);
v_sorryDep_x3f_404_ = lean_ctor_get(v_val_403_, 8);
lean_inc(v_sorryDep_x3f_404_);
lean_dec(v_val_403_);
if (lean_obj_tag(v_sorryDep_x3f_404_) == 1)
{
lean_object* v_val_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_417_; 
lean_dec(v_val_356_);
lean_dec(v_constName_235_);
lean_dec_ref(v_env_234_);
v_val_405_ = lean_ctor_get(v_sorryDep_x3f_404_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v_sorryDep_x3f_404_);
if (v_isSharedCheck_417_ == 0)
{
v___x_407_ = v_sorryDep_x3f_404_;
v_isShared_408_ = v_isSharedCheck_417_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_val_405_);
lean_dec(v_sorryDep_x3f_404_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_417_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_409_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__9));
v___x_410_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_405_, v___x_323_);
v___x_411_ = lean_string_append(v___x_409_, v___x_410_);
lean_dec_ref(v___x_410_);
v___x_412_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__10));
v___x_413_ = lean_string_append(v___x_411_, v___x_412_);
if (v_isShared_408_ == 0)
{
lean_ctor_set_tag(v___x_407_, 0);
lean_ctor_set(v___x_407_, 0, v___x_413_);
v___x_415_ = v___x_407_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
else
{
lean_dec(v_sorryDep_x3f_404_);
goto v___jp_357_;
}
}
else
{
lean_dec(v___x_402_);
goto v___jp_357_;
}
v___jp_357_:
{
lean_object* v_type_358_; lean_object* v_params_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_type_358_ = lean_ctor_get(v_val_356_, 2);
lean_inc_ref(v_type_358_);
v_params_359_ = lean_ctor_get(v_val_356_, 3);
lean_inc_ref(v_params_359_);
lean_dec(v_val_356_);
v___x_360_ = lean_array_get_size(v_params_359_);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_nat_dec_eq(v___x_360_, v___x_361_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; 
v___x_363_ = lean_nat_dec_lt(v___x_361_, v___x_360_);
if (v___x_363_ == 0)
{
v___y_291_ = v_type_358_;
v___y_292_ = v___x_360_;
v___y_293_ = v___x_362_;
v___y_294_ = v___x_361_;
v___y_295_ = v_params_359_;
v___y_296_ = v___x_323_;
goto v___jp_290_;
}
else
{
if (v___x_363_ == 0)
{
v___y_291_ = v_type_358_;
v___y_292_ = v___x_360_;
v___y_293_ = v___x_362_;
v___y_294_ = v___x_361_;
v___y_295_ = v_params_359_;
v___y_296_ = v___x_323_;
goto v___jp_290_;
}
else
{
size_t v___x_364_; size_t v___x_365_; uint8_t v___x_366_; 
v___x_364_ = ((size_t)0ULL);
v___x_365_ = lean_usize_of_nat(v___x_360_);
v___x_366_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__3(v___x_323_, v___x_360_, v_params_359_, v___x_364_, v___x_365_);
if (v___x_366_ == 0)
{
v___y_283_ = v_type_358_;
v___y_284_ = v___x_360_;
v___y_285_ = v___x_362_;
v___y_286_ = v___x_361_;
v___y_287_ = v_params_359_;
v___y_288_ = v___x_363_;
goto v___jp_282_;
}
else
{
lean_dec_ref(v_params_359_);
lean_dec_ref(v_type_358_);
lean_dec(v_constName_235_);
lean_dec_ref(v_env_234_);
goto v___jp_244_;
}
}
}
}
else
{
uint32_t v___x_367_; lean_object* v_code_368_; 
lean_dec_ref(v_params_359_);
v___x_367_ = 0;
v_code_368_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12);
if (lean_obj_tag(v_type_358_) == 4)
{
lean_object* v_declName_369_; 
v_declName_369_ = lean_ctor_get(v_type_358_, 0);
lean_inc(v_declName_369_);
if (lean_obj_tag(v_declName_369_) == 1)
{
lean_object* v_pre_370_; 
v_pre_370_ = lean_ctor_get(v_declName_369_, 0);
if (lean_obj_tag(v_pre_370_) == 0)
{
lean_object* v_us_371_; lean_object* v_str_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_us_371_ = lean_ctor_get(v_type_358_, 1);
lean_inc(v_us_371_);
lean_dec_ref_known(v_type_358_, 2);
v_str_372_ = lean_ctor_get(v_declName_369_, 1);
lean_inc_ref(v_str_372_);
lean_dec_ref_known(v_declName_369_, 2);
v___x_373_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__13));
v___x_374_ = lean_string_dec_eq(v_str_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_375_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__14));
v___x_376_ = lean_string_dec_eq(v_str_372_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__15));
v___x_378_ = lean_string_dec_eq(v_str_372_, v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__16));
v___x_380_ = lean_string_dec_eq(v_str_372_, v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__17));
v___x_382_ = lean_string_dec_eq(v_str_372_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__18));
v___x_384_ = lean_string_dec_eq(v_str_372_, v___x_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__19));
v___x_386_ = lean_string_dec_eq(v_str_372_, v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__20));
v___x_388_ = lean_string_dec_eq(v_str_372_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__21));
v___x_390_ = lean_string_dec_eq(v_str_372_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__22));
v___x_392_ = lean_string_dec_eq(v_str_372_, v___x_391_);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_393_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__23));
v___x_394_ = lean_string_dec_eq(v_str_372_, v___x_393_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__24));
v___x_396_ = lean_string_dec_eq(v_str_372_, v___x_395_);
lean_dec_ref(v_str_372_);
if (v___x_396_ == 0)
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
else
{
if (lean_obj_tag(v_us_371_) == 0)
{
v_code_237_ = v_code_368_;
goto v___jp_236_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
v_code_237_ = v_code_368_;
goto v___jp_236_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
v_code_237_ = v_code_368_;
goto v___jp_236_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
v___y_298_ = v___x_367_;
v___y_299_ = v_code_368_;
goto v___jp_297_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
v___y_298_ = v___x_367_;
v___y_299_ = v_code_368_;
goto v___jp_297_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
lean_object* v_code_397_; 
v_code_397_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26);
v_code_237_ = v_code_397_;
goto v___jp_236_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
lean_object* v_code_398_; 
v_code_398_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28);
v_code_237_ = v_code_398_;
goto v___jp_236_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
lean_object* v_code_399_; 
v_code_399_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30);
v_code_237_ = v_code_399_;
goto v___jp_236_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
lean_object* v_code_400_; 
v_code_400_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32);
v_code_237_ = v_code_400_;
goto v___jp_236_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
lean_object* v_code_401_; 
v_code_401_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34);
v_code_237_ = v_code_401_;
goto v___jp_236_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
v___y_305_ = v___x_367_;
v___y_306_ = v_code_368_;
goto v___jp_304_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref(v_str_372_);
if (lean_obj_tag(v_us_371_) == 0)
{
v___y_305_ = v___x_367_;
v___y_306_ = v_code_368_;
goto v___jp_304_;
}
else
{
lean_dec(v_us_371_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
else
{
lean_dec_ref_known(v_declName_369_, 2);
lean_dec_ref_known(v_type_358_, 2);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
else
{
lean_dec(v_declName_369_);
lean_dec_ref_known(v_type_358_, 2);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
else
{
lean_dec_ref(v_type_358_);
v___y_311_ = v_code_368_;
goto v___jp_310_;
}
}
}
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
lean_dec(v___x_355_);
lean_dec_ref(v_env_234_);
v___x_418_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__8));
v___x_419_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_constName_235_, v___x_323_);
v___x_420_ = lean_string_append(v___x_418_, v___x_419_);
lean_dec_ref(v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
v___jp_329_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v_runtimeDecl_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_332_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5);
v___x_333_ = lean_array_push(v___x_331_, v_boxedName_328_);
v_runtimeDecl_334_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl(v___x_332_, v___x_333_);
v___x_335_ = lean_eval_bytecode_decl(v_env_234_, v_runtimeDecl_334_);
lean_dec_ref(v_runtimeDecl_334_);
lean_dec_ref(v_env_234_);
v___x_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
v___jp_236_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v_runtimeDecl_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_238_ = lean_unsigned_to_nat(1u);
v___x_239_ = lean_mk_empty_array_with_capacity(v___x_238_);
v___x_240_ = lean_array_push(v___x_239_, v_constName_235_);
v_runtimeDecl_241_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_simpleBytecodeDecl(v_code_237_, v___x_240_);
lean_dec_ref(v_code_237_);
v___x_242_ = lean_eval_bytecode_decl(v_env_234_, v_runtimeDecl_241_);
lean_dec_ref(v_runtimeDecl_241_);
lean_dec_ref(v_env_234_);
v___x_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
return v___x_243_;
}
v___jp_244_:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__3, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__3_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__3);
v___x_246_ = l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__0(v___x_245_);
return v___x_246_;
}
v___jp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_249_ = lean_array_get_size(v___y_248_);
lean_dec_ref(v___y_248_);
v___x_250_ = lean_unsigned_to_nat(16u);
v___x_251_ = lean_nat_dec_le(v___x_249_, v___x_250_);
if (v___x_251_ == 0)
{
lean_dec(v_constName_235_);
lean_dec_ref(v_env_234_);
goto v___jp_244_;
}
else
{
lean_object* v_code_252_; 
v_code_252_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__5);
v_code_237_ = v_code_252_;
goto v___jp_236_;
}
}
v___jp_253_:
{
if (v___y_255_ == 0)
{
lean_dec_ref(v___y_254_);
lean_dec(v_constName_235_);
lean_dec_ref(v_env_234_);
goto v___jp_244_;
}
else
{
v___y_248_ = v___y_254_;
goto v___jp_247_;
}
}
v___jp_256_:
{
uint8_t v___x_262_; 
v___x_262_ = lean_nat_dec_lt(v___y_259_, v___y_257_);
if (v___x_262_ == 0)
{
lean_dec(v___y_257_);
v___y_248_ = v___y_260_;
goto v___jp_247_;
}
else
{
if (v___x_262_ == 0)
{
lean_dec(v___y_257_);
v___y_248_ = v___y_260_;
goto v___jp_247_;
}
else
{
size_t v___x_263_; size_t v___x_264_; uint8_t v___x_265_; 
v___x_263_ = ((size_t)0ULL);
v___x_264_ = lean_usize_of_nat(v___y_257_);
v___x_265_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__1(v___y_257_, v___y_261_, v___y_260_, v___x_263_, v___x_264_);
lean_dec(v___y_257_);
if (v___x_265_ == 0)
{
v___y_248_ = v___y_260_;
goto v___jp_247_;
}
else
{
v___y_254_ = v___y_260_;
v___y_255_ = v___y_258_;
goto v___jp_253_;
}
}
}
}
v___jp_266_:
{
if (v___y_271_ == 0)
{
lean_dec(v___y_267_);
v___y_254_ = v___y_270_;
v___y_255_ = v___y_268_;
goto v___jp_253_;
}
else
{
v___y_257_ = v___y_267_;
v___y_258_ = v___y_268_;
v___y_259_ = v___y_269_;
v___y_260_ = v___y_270_;
v___y_261_ = v___y_271_;
goto v___jp_256_;
}
}
v___jp_272_:
{
if (v___y_277_ == 0)
{
v___y_267_ = v___y_273_;
v___y_268_ = v___y_274_;
v___y_269_ = v___y_275_;
v___y_270_ = v___y_276_;
v___y_271_ = v___y_274_;
goto v___jp_266_;
}
else
{
uint8_t v___x_278_; 
v___x_278_ = lean_nat_dec_lt(v___y_275_, v___y_273_);
if (v___x_278_ == 0)
{
v___y_257_ = v___y_273_;
v___y_258_ = v___y_274_;
v___y_259_ = v___y_275_;
v___y_260_ = v___y_276_;
v___y_261_ = v___y_277_;
goto v___jp_256_;
}
else
{
if (v___x_278_ == 0)
{
v___y_257_ = v___y_273_;
v___y_258_ = v___y_274_;
v___y_259_ = v___y_275_;
v___y_260_ = v___y_276_;
v___y_261_ = v___y_277_;
goto v___jp_256_;
}
else
{
size_t v___x_279_; size_t v___x_280_; uint8_t v___x_281_; 
v___x_279_ = ((size_t)0ULL);
v___x_280_ = lean_usize_of_nat(v___y_273_);
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__2(v___y_273_, v___y_277_, v___y_276_, v___x_279_, v___x_280_);
if (v___x_281_ == 0)
{
v___y_257_ = v___y_273_;
v___y_258_ = v___y_274_;
v___y_259_ = v___y_275_;
v___y_260_ = v___y_276_;
v___y_261_ = v___x_278_;
goto v___jp_256_;
}
else
{
v___y_267_ = v___y_273_;
v___y_268_ = v___y_274_;
v___y_269_ = v___y_275_;
v___y_270_ = v___y_276_;
v___y_271_ = v___y_274_;
goto v___jp_266_;
}
}
}
}
}
v___jp_282_:
{
uint8_t v___x_289_; 
v___x_289_ = l_Lean_Compiler_LCNF_ImpureType_Lean_Expr_isScalar(v___y_283_);
lean_dec_ref(v___y_283_);
if (v___x_289_ == 0)
{
v___y_273_ = v___y_284_;
v___y_274_ = v___y_285_;
v___y_275_ = v___y_286_;
v___y_276_ = v___y_287_;
v___y_277_ = v___y_288_;
goto v___jp_272_;
}
else
{
v___y_273_ = v___y_284_;
v___y_274_ = v___y_285_;
v___y_275_ = v___y_286_;
v___y_276_ = v___y_287_;
v___y_277_ = v___y_285_;
goto v___jp_272_;
}
}
v___jp_290_:
{
if (v___y_296_ == 0)
{
lean_dec_ref(v___y_291_);
v___y_273_ = v___y_292_;
v___y_274_ = v___y_293_;
v___y_275_ = v___y_294_;
v___y_276_ = v___y_295_;
v___y_277_ = v___y_293_;
goto v___jp_272_;
}
else
{
v___y_283_ = v___y_291_;
v___y_284_ = v___y_292_;
v___y_285_ = v___y_293_;
v___y_286_ = v___y_294_;
v___y_287_ = v___y_295_;
v___y_288_ = v___y_296_;
goto v___jp_282_;
}
}
v___jp_297_:
{
uint32_t v___x_300_; uint32_t v___x_301_; lean_object* v___x_302_; lean_object* v_code_303_; 
v___x_300_ = 1;
v___x_301_ = l_Lean_Compiler_Bytecode_Instruction_inc(v___y_298_, v___x_300_);
v___x_302_ = lean_box_uint32(v___x_301_);
v_code_303_ = lean_array_push(v___y_299_, v___x_302_);
v_code_237_ = v_code_303_;
goto v___jp_236_;
}
v___jp_304_:
{
uint32_t v___x_307_; lean_object* v___x_308_; lean_object* v_code_309_; 
v___x_307_ = l_Lean_Compiler_Bytecode_Instruction_boxSmall(v___y_305_, v___y_305_);
v___x_308_ = lean_box_uint32(v___x_307_);
v_code_309_ = lean_array_push(v___y_306_, v___x_308_);
v_code_237_ = v_code_309_;
goto v___jp_236_;
}
v___jp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_obj_once(&l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__7, &l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__7_once, _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__7);
v___x_313_ = l_panic___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl_spec__4(v___x_312_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v___y_311_);
lean_dec(v_constName_235_);
lean_dec_ref(v_env_234_);
v_a_314_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_313_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_dec_ref_known(v___x_313_, 1);
v_code_237_ = v___y_311_;
goto v___jp_236_;
}
}
}
}
LEAN_EXPORT lean_object* lean_eval_const(lean_object* v_env_422_, lean_object* v___opts_423_, lean_object* v_constName_424_){
_start:
{
lean_object* v___x_425_; 
lean_dec_ref(v___opts_423_);
v___x_425_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_422_, v_constName_424_);
return v___x_425_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(lean_object* v_e_426_){
_start:
{
if (lean_obj_tag(v_e_426_) == 0)
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_436_; 
v_a_428_ = lean_ctor_get(v_e_426_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_e_426_);
if (v_isSharedCheck_436_ == 0)
{
v___x_430_ = v_e_426_;
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v_e_426_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_436_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = lean_mk_io_user_error(v_a_428_);
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 1);
lean_ctor_set(v___x_430_, 0, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_432_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_a_437_ = lean_ctor_get(v_e_426_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v_e_426_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v_e_426_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v_e_426_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set_tag(v___x_439_, 0);
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_426_ = stack[0].m_obj;
lean_object* v_res_445_;
v_res_445_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v_e_426_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg___boxed(lean_object* v_e_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v_e_446_);
return v_res_448_;
}
}
lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0(lean_object* v_00_u03b1_449_, lean_object* v_e_450_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v_e_450_);
return v___x_452_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_450_ = stack[1].m_obj;
lean_object* v_res_453_;
v_res_453_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0(lean_box(0), v_e_450_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___boxed(lean_object* v_00_u03b1_454_, lean_object* v_e_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0(v_00_u03b1_454_, v_e_455_);
return v_res_457_;
}
}
lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg(lean_object* v_env_460_, lean_object* v_decl_461_, lean_object* v_initDecl_462_){
_start:
{
lean_object* v___x_464_; 
lean_inc(v_decl_461_);
lean_inc_ref(v_env_460_);
v___x_464_ = lean_find_bytecode_decl(v_env_460_, v_decl_461_);
if (lean_obj_tag(v___x_464_) == 1)
{
lean_object* v_val_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
lean_dec(v_decl_461_);
v_val_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v___x_464_, 1);
v___x_466_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_460_, v_initDecl_462_);
v___x_467_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v___x_466_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = lean_apply_1(v_a_468_, lean_box(0));
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_479_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_479_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_479_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_474_ = lean_runtime_mark_persistent(v_a_470_);
v___x_475_ = lean_bytecode_store_init_value(v_val_465_, v___x_474_);
lean_dec(v_val_465_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 0, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
}
else
{
lean_object* v_a_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_487_; 
lean_dec(v_val_465_);
v_a_480_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_487_ == 0)
{
v___x_482_ = v___x_469_;
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_a_480_);
lean_dec(v___x_469_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_487_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_485_; 
if (v_isShared_483_ == 0)
{
v___x_485_ = v___x_482_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_a_480_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
}
}
else
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_val_465_);
v_a_488_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_467_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_467_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
else
{
lean_object* v___x_496_; uint8_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec(v___x_464_);
lean_dec(v_initDecl_462_);
lean_dec_ref(v_env_460_);
v___x_496_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___closed__0));
v___x_497_ = 1;
v___x_498_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_461_, v___x_497_);
v___x_499_ = lean_string_append(v___x_496_, v___x_498_);
lean_dec_ref(v___x_498_);
v___x_500_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___closed__1));
v___x_501_ = lean_string_append(v___x_499_, v___x_500_);
v___x_502_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_460_ = stack[0].m_obj;
lean_object* v_decl_461_ = stack[1].m_obj;
lean_object* v_initDecl_462_ = stack[2].m_obj;
lean_object* v_res_504_;
v_res_504_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg(v_env_460_, v_decl_461_, v_initDecl_462_);
stack->m_obj
 = v_res_504_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg___boxed(lean_object* v_env_505_, lean_object* v_decl_506_, lean_object* v_initDecl_507_, lean_object* v_a_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg(v_env_505_, v_decl_506_, v_initDecl_507_);
return v_res_509_;
}
}
lean_object* lean_run_init(lean_object* v_env_510_, lean_object* v_opts_511_, lean_object* v_decl_512_, lean_object* v_initDecl_513_){
_start:
{
lean_object* v___x_515_; 
lean_dec_ref(v_opts_511_);
v___x_515_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___redArg(v_env_510_, v_decl_512_, v_initDecl_513_);
return v___x_515_;
}
}
LEAN_EXPORT void lean_run_init_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_510_ = stack[0].m_obj;
lean_object* v_opts_511_ = stack[1].m_obj;
lean_object* v_decl_512_ = stack[2].m_obj;
lean_object* v_initDecl_513_ = stack[3].m_obj;
lean_object* v_res_516_;
v_res_516_ = lean_run_init(v_env_510_, v_opts_511_, v_decl_512_, v_initDecl_513_);
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl___boxed(lean_object* v_env_517_, lean_object* v_opts_518_, lean_object* v_decl_519_, lean_object* v_initDecl_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = lean_run_init(v_env_517_, v_opts_518_, v_decl_519_, v_initDecl_520_);
return v_res_522_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_showError_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_524_ = stack[1].m_obj;
lean_object* v_res_526_;
v_res_526_ = lean_io_result_show_error(v_e_524_);
stack->m_obj
 = v_res_526_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_showError___boxed(lean_object* v_00_u03b1_527_, lean_object* v_e_528_, lean_object* v_a_00___x40___internal___hyg_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = lean_io_result_show_error(v_e_528_);
lean_dec_ref(v_e_528_);
return v_res_530_;
}
}
lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0(lean_object* v_val_532_, lean_object* v_x_533_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_535_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0___closed__0));
v___x_536_ = l_Lean_ConstantInfo_type(v_val_532_);
v___x_537_ = lean_expr_dbg_to_string(v___x_536_);
lean_dec_ref(v___x_536_);
v___x_538_ = lean_string_append(v___x_535_, v___x_537_);
lean_dec_ref(v___x_537_);
v___x_539_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_532_ = stack[0].m_obj;
lean_object* v_x_533_ = stack[1].m_obj;
lean_object* v_res_541_;
v_res_541_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0(v_val_532_, v_x_533_);
stack->m_obj
 = v_res_541_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0___boxed(lean_object* v_val_542_, lean_object* v_x_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0(v_val_542_, v_x_543_);
lean_dec_ref(v_val_542_);
return v_res_545_;
}
}
lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1(lean_object* v_invalidMain_546_, lean_object* v_x_547_){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = lean_box(0);
v___x_550_ = lean_apply_2(v_invalidMain_546_, v___x_549_, lean_box(0));
return v___x_550_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_invalidMain_546_ = stack[0].m_obj;
lean_object* v_x_547_ = stack[1].m_obj;
lean_object* v_res_551_;
v_res_551_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1(v_invalidMain_546_, v_x_547_);
stack->m_obj
 = v_res_551_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1___boxed(lean_object* v_invalidMain_552_, lean_object* v_x_553_, lean_object* v___y_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1(v_invalidMain_552_, v_x_553_);
lean_dec_ref(v_x_553_);
return v_res_555_;
}
}
lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(lean_object* v_invalidMain_556_, lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_box(0);
v___x_561_ = lean_apply_2(v_invalidMain_556_, v___x_560_, lean_box(0));
return v___x_561_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_invalidMain_556_ = stack[0].m_obj;
lean_object* v_x_557_ = stack[1].m_obj;
lean_object* v_x_558_ = stack[2].m_obj;
lean_object* v_res_562_;
v_res_562_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_556_, v_x_557_, v_x_558_);
stack->m_obj
 = v_res_562_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2___boxed(lean_object* v_invalidMain_563_, lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v___y_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_563_, v_x_564_, v_x_565_);
lean_dec_ref(v_x_565_);
lean_dec_ref(v_x_564_);
return v_res_567_;
}
}
uint32_t l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg(lean_object* v_env_585_, lean_object* v_args_586_){
_start:
{
lean_object* v___y_589_; lean_object* v___y_593_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; 
v___x_642_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__1));
v___x_643_ = 0;
lean_inc_ref(v_env_585_);
v___x_644_ = l_Lean_Environment_find_x3f(v_env_585_, v___x_642_, v___x_643_);
if (lean_obj_tag(v___x_644_) == 1)
{
lean_object* v_val_645_; lean_object* v_invalidMain_646_; lean_object* v___x_647_; 
v_val_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc_n(v_val_645_, 2);
lean_dec_ref_known(v___x_644_, 1);
v_invalidMain_646_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v_invalidMain_646_, 0, v_val_645_);
v___x_647_ = l_Lean_ConstantInfo_type(v_val_645_);
switch(lean_obj_tag(v___x_647_))
{
case 7:
{
lean_object* v_binderType_648_; 
v_binderType_648_ = lean_ctor_get(v___x_647_, 1);
lean_inc_ref(v_binderType_648_);
if (lean_obj_tag(v_binderType_648_) == 5)
{
lean_object* v_fn_649_; 
v_fn_649_ = lean_ctor_get(v_binderType_648_, 0);
if (lean_obj_tag(v_fn_649_) == 4)
{
lean_object* v_declName_650_; 
v_declName_650_ = lean_ctor_get(v_fn_649_, 0);
if (lean_obj_tag(v_declName_650_) == 1)
{
lean_object* v_pre_651_; 
v_pre_651_ = lean_ctor_get(v_declName_650_, 0);
if (lean_obj_tag(v_pre_651_) == 0)
{
lean_object* v_body_652_; lean_object* v_arg_653_; lean_object* v_us_654_; lean_object* v_str_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_body_652_ = lean_ctor_get(v___x_647_, 2);
lean_inc_ref(v_body_652_);
lean_dec_ref_known(v___x_647_, 3);
v_arg_653_ = lean_ctor_get(v_binderType_648_, 1);
v_us_654_ = lean_ctor_get(v_fn_649_, 1);
v_str_655_ = lean_ctor_get(v_declName_650_, 1);
v___x_656_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__2));
v___x_657_ = lean_string_dec_eq(v_str_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_658_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v_binderType_648_, v_body_652_);
lean_dec_ref(v_body_652_);
lean_dec_ref_known(v_binderType_648_, 2);
v___y_593_ = v___x_658_;
goto v___jp_592_;
}
else
{
lean_inc(v_us_654_);
lean_inc_ref(v_arg_653_);
lean_inc(v_pre_651_);
lean_dec_ref_known(v_binderType_648_, 2);
if (lean_obj_tag(v_arg_653_) == 4)
{
lean_object* v_declName_659_; 
v_declName_659_ = lean_ctor_get(v_arg_653_, 0);
if (lean_obj_tag(v_declName_659_) == 1)
{
lean_object* v_pre_660_; 
v_pre_660_ = lean_ctor_get(v_declName_659_, 0);
if (lean_obj_tag(v_pre_660_) == 0)
{
lean_object* v_us_661_; lean_object* v_str_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_us_661_ = lean_ctor_get(v_arg_653_, 1);
v_str_662_ = lean_ctor_get(v_declName_659_, 1);
v___x_663_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__3));
v___x_664_ = lean_string_dec_eq(v_str_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_665_ = l_Lean_Name_str___override(v_pre_660_, v___x_656_);
v___x_666_ = l_Lean_Expr_const___override(v___x_665_, v_us_654_);
v___x_667_ = l_Lean_Expr_app___override(v___x_666_, v_arg_653_);
v___x_668_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v___x_667_, v_body_652_);
lean_dec_ref(v_body_652_);
lean_dec_ref(v___x_667_);
v___y_593_ = v___x_668_;
goto v___jp_592_;
}
else
{
lean_inc(v_us_661_);
lean_inc(v_pre_660_);
lean_dec_ref_known(v_arg_653_, 2);
if (lean_obj_tag(v_body_652_) == 5)
{
lean_object* v_fn_669_; 
v_fn_669_ = lean_ctor_get(v_body_652_, 0);
if (lean_obj_tag(v_fn_669_) == 4)
{
lean_object* v_declName_670_; 
v_declName_670_ = lean_ctor_get(v_fn_669_, 0);
if (lean_obj_tag(v_declName_670_) == 1)
{
lean_object* v_pre_671_; 
v_pre_671_ = lean_ctor_get(v_declName_670_, 0);
if (lean_obj_tag(v_pre_671_) == 0)
{
lean_object* v_arg_672_; lean_object* v_us_673_; lean_object* v_str_674_; lean_object* v___x_675_; uint8_t v___x_676_; 
v_arg_672_ = lean_ctor_get(v_body_652_, 1);
v_us_673_ = lean_ctor_get(v_fn_669_, 1);
v_str_674_ = lean_ctor_get(v_declName_670_, 1);
v___x_675_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__4));
v___x_676_ = lean_string_dec_eq(v_str_674_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_677_ = l_Lean_Name_str___override(v_pre_671_, v___x_656_);
v___x_678_ = l_Lean_Expr_const___override(v___x_677_, v_us_654_);
v___x_679_ = l_Lean_Name_str___override(v_pre_671_, v___x_663_);
v___x_680_ = l_Lean_Expr_const___override(v___x_679_, v_us_661_);
v___x_681_ = l_Lean_Expr_app___override(v___x_678_, v___x_680_);
v___x_682_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v___x_681_, v_body_652_);
lean_dec_ref_known(v_body_652_, 2);
lean_dec_ref(v___x_681_);
v___y_593_ = v___x_682_;
goto v___jp_592_;
}
else
{
lean_inc(v_us_673_);
lean_inc_ref(v_arg_672_);
lean_inc(v_pre_671_);
lean_dec_ref_known(v_body_652_, 2);
if (lean_obj_tag(v_arg_672_) == 4)
{
lean_object* v_declName_683_; lean_object* v___x_684_; uint8_t v___x_685_; 
lean_dec(v_us_673_);
lean_dec(v_us_661_);
lean_dec(v_us_654_);
lean_dec_ref(v_invalidMain_646_);
v_declName_683_ = lean_ctor_get(v_arg_672_, 0);
lean_inc(v_declName_683_);
lean_dec_ref_known(v_arg_672_, 2);
v___x_684_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__5));
v___x_685_ = lean_name_eq(v_declName_683_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_686_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__7));
v___x_687_ = lean_name_eq(v_declName_683_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_688_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__9));
v___x_689_ = lean_name_eq(v_declName_683_, v___x_688_);
lean_dec(v_declName_683_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_690_ = lean_box(0);
v___x_691_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0(v_val_645_, v___x_690_);
lean_dec(v_val_645_);
v___y_593_ = v___x_691_;
goto v___jp_592_;
}
else
{
lean_dec(v_val_645_);
goto v___jp_596_;
}
}
else
{
lean_dec(v_declName_683_);
lean_dec(v_val_645_);
goto v___jp_596_;
}
}
else
{
lean_object* v___x_692_; lean_object* v___x_693_; 
lean_dec(v_declName_683_);
lean_dec(v_val_645_);
v___x_692_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_585_, v___x_642_);
v___x_693_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v___x_692_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_695_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = lean_apply_2(v_a_694_, v_args_586_, lean_box(0));
v___y_593_ = v___x_695_;
goto v___jp_592_;
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec(v_args_586_);
v_a_696_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_693_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_693_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v___y_589_ = v___x_701_;
goto v___jp_588_;
}
}
}
}
}
else
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_704_ = l_Lean_Name_str___override(v_pre_671_, v___x_656_);
v___x_705_ = l_Lean_Expr_const___override(v___x_704_, v_us_654_);
v___x_706_ = l_Lean_Name_str___override(v_pre_671_, v___x_663_);
v___x_707_ = l_Lean_Expr_const___override(v___x_706_, v_us_661_);
v___x_708_ = l_Lean_Expr_app___override(v___x_705_, v___x_707_);
v___x_709_ = l_Lean_Name_str___override(v_pre_671_, v___x_675_);
v___x_710_ = l_Lean_Expr_const___override(v___x_709_, v_us_673_);
v___x_711_ = l_Lean_Expr_app___override(v___x_710_, v_arg_672_);
v___x_712_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v___x_708_, v___x_711_);
lean_dec_ref(v___x_711_);
lean_dec_ref(v___x_708_);
v___y_593_ = v___x_712_;
goto v___jp_592_;
}
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_713_ = l_Lean_Name_str___override(v_pre_660_, v___x_656_);
v___x_714_ = l_Lean_Expr_const___override(v___x_713_, v_us_654_);
v___x_715_ = l_Lean_Name_str___override(v_pre_660_, v___x_663_);
v___x_716_ = l_Lean_Expr_const___override(v___x_715_, v_us_661_);
v___x_717_ = l_Lean_Expr_app___override(v___x_714_, v___x_716_);
v___x_718_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v___x_717_, v_body_652_);
lean_dec_ref_known(v_body_652_, 2);
lean_dec_ref(v___x_717_);
v___y_593_ = v___x_718_;
goto v___jp_592_;
}
}
else
{
lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_719_ = l_Lean_Name_str___override(v_pre_660_, v___x_656_);
v___x_720_ = l_Lean_Expr_const___override(v___x_719_, v_us_654_);
v___x_721_ = l_Lean_Name_str___override(v_pre_660_, v___x_663_);
v___x_722_ = l_Lean_Expr_const___override(v___x_721_, v_us_661_);
v___x_723_ = l_Lean_Expr_app___override(v___x_720_, v___x_722_);
v___x_724_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v___x_723_, v_body_652_);
lean_dec_ref_known(v_body_652_, 2);
lean_dec_ref(v___x_723_);
v___y_593_ = v___x_724_;
goto v___jp_592_;
}
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_725_ = l_Lean_Name_str___override(v_pre_660_, v___x_656_);
v___x_726_ = l_Lean_Expr_const___override(v___x_725_, v_us_654_);
v___x_727_ = l_Lean_Name_str___override(v_pre_660_, v___x_663_);
v___x_728_ = l_Lean_Expr_const___override(v___x_727_, v_us_661_);
v___x_729_ = l_Lean_Expr_app___override(v___x_726_, v___x_728_);
v___x_730_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v___x_729_, v_body_652_);
lean_dec_ref_known(v_body_652_, 2);
lean_dec_ref(v___x_729_);
v___y_593_ = v___x_730_;
goto v___jp_592_;
}
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_731_ = l_Lean_Name_str___override(v_pre_660_, v___x_656_);
v___x_732_ = l_Lean_Expr_const___override(v___x_731_, v_us_654_);
v___x_733_ = l_Lean_Name_str___override(v_pre_660_, v___x_663_);
v___x_734_ = l_Lean_Expr_const___override(v___x_733_, v_us_661_);
v___x_735_ = l_Lean_Expr_app___override(v___x_732_, v___x_734_);
v___x_736_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v___x_735_, v_body_652_);
lean_dec_ref(v_body_652_);
lean_dec_ref(v___x_735_);
v___y_593_ = v___x_736_;
goto v___jp_592_;
}
}
}
else
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_737_ = l_Lean_Name_str___override(v_pre_651_, v___x_656_);
v___x_738_ = l_Lean_Expr_const___override(v___x_737_, v_us_654_);
v___x_739_ = l_Lean_Expr_app___override(v___x_738_, v_arg_653_);
v___x_740_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v___x_739_, v_body_652_);
lean_dec_ref(v_body_652_);
lean_dec_ref(v___x_739_);
v___y_593_ = v___x_740_;
goto v___jp_592_;
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_741_ = l_Lean_Name_str___override(v_pre_651_, v___x_656_);
v___x_742_ = l_Lean_Expr_const___override(v___x_741_, v_us_654_);
v___x_743_ = l_Lean_Expr_app___override(v___x_742_, v_arg_653_);
v___x_744_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v___x_743_, v_body_652_);
lean_dec_ref(v_body_652_);
lean_dec_ref(v___x_743_);
v___y_593_ = v___x_744_;
goto v___jp_592_;
}
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_745_ = l_Lean_Name_str___override(v_pre_651_, v___x_656_);
v___x_746_ = l_Lean_Expr_const___override(v___x_745_, v_us_654_);
v___x_747_ = l_Lean_Expr_app___override(v___x_746_, v_arg_653_);
v___x_748_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v___x_747_, v_body_652_);
lean_dec_ref(v_body_652_);
lean_dec_ref(v___x_747_);
v___y_593_ = v___x_748_;
goto v___jp_592_;
}
}
}
else
{
lean_object* v_body_749_; lean_object* v___x_750_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v_body_749_ = lean_ctor_get(v___x_647_, 2);
lean_inc_ref(v_body_749_);
lean_dec_ref_known(v___x_647_, 3);
v___x_750_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v_binderType_648_, v_body_749_);
lean_dec_ref(v_body_749_);
lean_dec_ref_known(v_binderType_648_, 2);
v___y_593_ = v___x_750_;
goto v___jp_592_;
}
}
else
{
lean_object* v_body_751_; lean_object* v___x_752_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v_body_751_ = lean_ctor_get(v___x_647_, 2);
lean_inc_ref(v_body_751_);
lean_dec_ref_known(v___x_647_, 3);
v___x_752_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v_binderType_648_, v_body_751_);
lean_dec_ref(v_body_751_);
lean_dec_ref_known(v_binderType_648_, 2);
v___y_593_ = v___x_752_;
goto v___jp_592_;
}
}
else
{
lean_object* v_body_753_; lean_object* v___x_754_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v_body_753_ = lean_ctor_get(v___x_647_, 2);
lean_inc_ref(v_body_753_);
lean_dec_ref_known(v___x_647_, 3);
v___x_754_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v_binderType_648_, v_body_753_);
lean_dec_ref(v_body_753_);
lean_dec_ref_known(v_binderType_648_, 2);
v___y_593_ = v___x_754_;
goto v___jp_592_;
}
}
else
{
lean_object* v_body_755_; lean_object* v___x_756_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v_body_755_ = lean_ctor_get(v___x_647_, 2);
lean_inc_ref(v_body_755_);
lean_dec_ref_known(v___x_647_, 3);
v___x_756_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__2(v_invalidMain_646_, v_binderType_648_, v_body_755_);
lean_dec_ref(v_body_755_);
lean_dec_ref(v_binderType_648_);
v___y_593_ = v___x_756_;
goto v___jp_592_;
}
}
case 5:
{
lean_object* v_fn_757_; 
lean_dec(v_args_586_);
v_fn_757_ = lean_ctor_get(v___x_647_, 0);
if (lean_obj_tag(v_fn_757_) == 4)
{
lean_object* v_declName_758_; 
v_declName_758_ = lean_ctor_get(v_fn_757_, 0);
if (lean_obj_tag(v_declName_758_) == 1)
{
lean_object* v_pre_759_; 
v_pre_759_ = lean_ctor_get(v_declName_758_, 0);
if (lean_obj_tag(v_pre_759_) == 0)
{
lean_object* v_arg_760_; lean_object* v_us_761_; lean_object* v_str_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_arg_760_ = lean_ctor_get(v___x_647_, 1);
v_us_761_ = lean_ctor_get(v_fn_757_, 1);
v_str_762_ = lean_ctor_get(v_declName_758_, 1);
v___x_763_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__4));
v___x_764_ = lean_string_dec_eq(v_str_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; 
lean_dec(v_val_645_);
lean_dec_ref(v_env_585_);
v___x_765_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1(v_invalidMain_646_, v___x_647_);
lean_dec_ref_known(v___x_647_, 2);
v___y_593_ = v___x_765_;
goto v___jp_592_;
}
else
{
lean_inc(v_us_761_);
lean_inc_ref(v_arg_760_);
lean_inc(v_pre_759_);
lean_dec_ref_known(v___x_647_, 2);
if (lean_obj_tag(v_arg_760_) == 4)
{
lean_object* v_declName_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
lean_dec(v_us_761_);
lean_dec_ref(v_invalidMain_646_);
v_declName_766_ = lean_ctor_get(v_arg_760_, 0);
lean_inc(v_declName_766_);
lean_dec_ref_known(v_arg_760_, 2);
v___x_767_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__5));
v___x_768_ = lean_name_eq(v_declName_766_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; uint8_t v___x_770_; 
v___x_769_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__7));
v___x_770_ = lean_name_eq(v_declName_766_, v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__9));
v___x_772_ = lean_name_eq(v_declName_766_, v___x_771_);
lean_dec(v_declName_766_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec_ref(v_env_585_);
v___x_773_ = lean_box(0);
v___x_774_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__0(v_val_645_, v___x_773_);
lean_dec(v_val_645_);
v___y_593_ = v___x_774_;
goto v___jp_592_;
}
else
{
lean_dec(v_val_645_);
goto v___jp_619_;
}
}
else
{
lean_dec(v_declName_766_);
lean_dec(v_val_645_);
goto v___jp_619_;
}
}
else
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec(v_declName_766_);
lean_dec(v_val_645_);
v___x_775_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_585_, v___x_642_);
v___x_776_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v___x_775_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
v___x_778_ = lean_apply_1(v_a_777_, lean_box(0));
v___y_593_ = v___x_778_;
goto v___jp_592_;
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
v_a_779_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_776_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_776_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
v___y_589_ = v___x_784_;
goto v___jp_588_;
}
}
}
}
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v_val_645_);
lean_dec_ref(v_env_585_);
v___x_787_ = l_Lean_Name_str___override(v_pre_759_, v___x_763_);
v___x_788_ = l_Lean_Expr_const___override(v___x_787_, v_us_761_);
v___x_789_ = l_Lean_Expr_app___override(v___x_788_, v_arg_760_);
v___x_790_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1(v_invalidMain_646_, v___x_789_);
lean_dec_ref(v___x_789_);
v___y_593_ = v___x_790_;
goto v___jp_592_;
}
}
}
else
{
lean_object* v___x_791_; 
lean_dec(v_val_645_);
lean_dec_ref(v_env_585_);
v___x_791_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1(v_invalidMain_646_, v___x_647_);
lean_dec_ref_known(v___x_647_, 2);
v___y_593_ = v___x_791_;
goto v___jp_592_;
}
}
else
{
lean_object* v___x_792_; 
lean_dec(v_val_645_);
lean_dec_ref(v_env_585_);
v___x_792_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1(v_invalidMain_646_, v___x_647_);
lean_dec_ref_known(v___x_647_, 2);
v___y_593_ = v___x_792_;
goto v___jp_592_;
}
}
else
{
lean_object* v___x_793_; 
lean_dec(v_val_645_);
lean_dec_ref(v_env_585_);
v___x_793_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1(v_invalidMain_646_, v___x_647_);
lean_dec_ref_known(v___x_647_, 2);
v___y_593_ = v___x_793_;
goto v___jp_592_;
}
}
default: 
{
lean_object* v___x_794_; 
lean_dec(v_val_645_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_794_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___lam__1(v_invalidMain_646_, v___x_647_);
lean_dec_ref(v___x_647_);
v___y_593_ = v___x_794_;
goto v___jp_592_;
}
}
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; 
lean_dec(v___x_644_);
lean_dec(v_args_586_);
lean_dec_ref(v_env_585_);
v___x_795_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__11));
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
v___y_589_ = v___x_796_;
goto v___jp_588_;
}
v___jp_588_:
{
lean_object* v___x_590_; uint32_t v___x_591_; 
v___x_590_ = lean_io_result_show_error(v___y_589_);
lean_dec_ref(v___y_589_);
v___x_591_ = 1;
return v___x_591_;
}
v___jp_592_:
{
if (lean_obj_tag(v___y_593_) == 0)
{
lean_object* v_a_594_; uint32_t v___x_595_; 
v_a_594_ = lean_ctor_get(v___y_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___y_593_, 1);
v___x_595_ = lean_unbox_uint32(v_a_594_);
lean_dec(v_a_594_);
return v___x_595_;
}
else
{
v___y_589_ = v___y_593_;
goto v___jp_588_;
}
}
v___jp_596_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__1));
v___x_598_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_585_, v___x_597_);
v___x_599_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v___x_598_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v_a_600_; lean_object* v___x_601_; 
v_a_600_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_a_600_);
lean_dec_ref_known(v___x_599_, 1);
v___x_601_ = lean_apply_2(v_a_600_, v_args_586_, lean_box(0));
if (lean_obj_tag(v___x_601_) == 0)
{
uint32_t v___x_602_; 
lean_dec_ref_known(v___x_601_, 1);
v___x_602_ = 0;
return v___x_602_;
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_601_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_601_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
v___y_589_ = v___x_608_;
goto v___jp_588_;
}
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_args_586_);
v_a_611_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_599_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_599_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
v___y_589_ = v___x_616_;
goto v___jp_588_;
}
}
}
}
v___jp_619_:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((lean_object*)(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___closed__1));
v___x_621_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg(v_env_585_, v___x_620_);
v___x_622_ = l_IO_ofExcept___at___00__private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runInitImpl_spec__0___redArg(v___x_621_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___x_624_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v___x_622_, 1);
v___x_624_ = lean_apply_1(v_a_623_, lean_box(0));
if (lean_obj_tag(v___x_624_) == 0)
{
uint32_t v___x_625_; 
lean_dec_ref_known(v___x_624_, 1);
v___x_625_ = 0;
return v___x_625_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
v_a_626_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_624_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_624_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
v___y_589_ = v___x_631_;
goto v___jp_588_;
}
}
}
}
else
{
lean_object* v_a_634_; lean_object* v___x_636_; uint8_t v_isShared_637_; uint8_t v_isSharedCheck_641_; 
v_a_634_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_641_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_641_ == 0)
{
v___x_636_ = v___x_622_;
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
else
{
lean_inc(v_a_634_);
lean_dec(v___x_622_);
v___x_636_ = lean_box(0);
v_isShared_637_ = v_isSharedCheck_641_;
goto v_resetjp_635_;
}
v_resetjp_635_:
{
lean_object* v___x_639_; 
if (v_isShared_637_ == 0)
{
v___x_639_ = v___x_636_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
v___y_589_ = v___x_639_;
goto v___jp_588_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_585_ = stack[0].m_obj;
lean_object* v_args_586_ = stack[1].m_obj;
uint32_t v_res_797_;
v_res_797_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg(v_env_585_, v_args_586_);
stack->m_num = v_res_797_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg___boxed(lean_object* v_env_798_, lean_object* v_args_799_, lean_object* v_void_800_){
_start:
{
uint32_t v_res_801_; lean_object* v_r_802_; 
v_res_801_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg(v_env_798_, v_args_799_);
v_r_802_ = lean_box_uint32(v_res_801_);
return v_r_802_;
}
}
uint32_t lean_eval_main(lean_object* v_env_803_, lean_object* v_opts_804_, lean_object* v_args_805_){
_start:
{
uint32_t v___x_807_; 
lean_dec_ref(v_opts_804_);
v___x_807_ = l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___redArg(v_env_803_, v_args_805_);
return v___x_807_;
}
}
LEAN_EXPORT void lean_eval_main_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_803_ = stack[0].m_obj;
lean_object* v_opts_804_ = stack[1].m_obj;
lean_object* v_args_805_ = stack[2].m_obj;
uint32_t v_res_808_;
v_res_808_ = lean_eval_main(v_env_803_, v_opts_804_, v_args_805_);
stack->m_num = v_res_808_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_runMain___boxed(lean_object* v_env_809_, lean_object* v_opts_810_, lean_object* v_args_811_, lean_object* v_void_812_){
_start:
{
uint32_t v_res_813_; lean_object* v_r_814_; 
v_res_813_ = lean_eval_main(v_env_809_, v_opts_810_, v_args_811_);
v_r_814_ = lean_box_uint32(v_res_813_);
return v_r_814_;
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
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__12___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__26___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__28___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__30___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__32___boxed__const__1);
l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34___boxed__const__1 = _init_l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34___boxed__const__1();
lean_mark_persistent(l___private_Lean_Compiler_Bytecode_Eval_0__Lean_Compiler_Bytecode_evalConstCoreImpl___redArg___closed__34___boxed__const__1);
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
