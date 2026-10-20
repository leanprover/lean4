// Lean compiler output
// Module: Lean.Compiler.IR.Meta
// Imports: public import Lean.Compiler.IR.CompilerM
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_IR_Alt_body(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
uint8_t l_Lean_isDeclMeta(lean_object*, lean_object*);
lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_setDeclMeta(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_IR_Decl_name(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_getIRPhases(lean_object*, lean_object*);
uint8_t l_Lean_instBEqIRPhases_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inferMeta"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(167, 96, 118, 160, 52, 15, 195, 103)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(178, 39, 14, 26, 17, 0, 113, 234)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Marking "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = " as meta because it is in `meta` closure"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = " as meta because it is tagged with `meta`"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_inferMeta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_inferMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Cannot evaluate constant `"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "` as it is neither marked nor imported as `meta`"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2 = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2_value;
LEAN_EXPORT lean_object* lean_eval_check_meta(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__0_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__1_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__3_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(72, 245, 227, 28, 172, 102, 215, 20)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "IR"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__5_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(15, 1, 131, 81, 163, 33, 163, 70)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__7_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(239, 116, 124, 204, 58, 248, 65, 36)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__9_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(2, 178, 250, 58, 136, 151, 133, 206)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__10_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 22, 108, 217, 231, 198, 61, 134)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__11_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(152, 36, 47, 73, 15, 106, 26, 28)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__12_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__13_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(85, 23, 125, 60, 249, 62, 248, 154)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__14_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__15_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(232, 103, 59, 209, 95, 49, 160, 48)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__16_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__2_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(65, 75, 213, 97, 69, 253, 1, 188)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__17_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__4_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 219, 136, 122, 106, 242, 0, 11)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__18_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__6_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 135, 17, 167, 105, 21, 177, 96)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__19_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__8_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 174, 68, 41, 157, 175, 184, 23)}};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collect(lean_object* v_f_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = lean_box(0);
v___x_4_ = l_Lean_NameSet_insert(v_a_2_, v_f_1_);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_3_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
switch(lean_obj_tag(v_a_6_))
{
case 0:
{
lean_object* v_e_8_; lean_object* v_b_9_; lean_object* v_f_11_; lean_object* v___y_12_; 
v_e_8_ = lean_ctor_get(v_a_6_, 2);
lean_inc_ref(v_e_8_);
v_b_9_ = lean_ctor_get(v_a_6_, 3);
lean_inc(v_b_9_);
lean_dec_ref_known(v_a_6_, 4);
switch(lean_obj_tag(v_e_8_))
{
case 6:
{
lean_object* v_c_16_; 
v_c_16_ = lean_ctor_get(v_e_8_, 0);
lean_inc(v_c_16_);
lean_dec_ref_known(v_e_8_, 2);
v_f_11_ = v_c_16_;
v___y_12_ = v_a_7_;
goto v___jp_10_;
}
case 7:
{
lean_object* v_c_17_; 
v_c_17_ = lean_ctor_get(v_e_8_, 0);
lean_inc(v_c_17_);
lean_dec_ref_known(v_e_8_, 2);
v_f_11_ = v_c_17_;
v___y_12_ = v_a_7_;
goto v___jp_10_;
}
default: 
{
lean_dec_ref(v_e_8_);
v_a_6_ = v_b_9_;
goto _start;
}
}
v___jp_10_:
{
lean_object* v___x_13_; lean_object* v_snd_14_; 
v___x_13_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collect(v_f_11_, v___y_12_);
v_snd_14_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_snd_14_);
lean_dec_ref(v___x_13_);
v_a_6_ = v_b_9_;
v_a_7_ = v_snd_14_;
goto _start;
}
}
case 1:
{
lean_object* v_v_19_; lean_object* v_b_20_; lean_object* v___x_21_; lean_object* v_snd_22_; 
v_v_19_ = lean_ctor_get(v_a_6_, 2);
lean_inc(v_v_19_);
v_b_20_ = lean_ctor_get(v_a_6_, 3);
lean_inc(v_b_20_);
lean_dec_ref_known(v_a_6_, 4);
v___x_21_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(v_v_19_, v_a_7_);
v_snd_22_ = lean_ctor_get(v___x_21_, 1);
lean_inc(v_snd_22_);
lean_dec_ref(v___x_21_);
v_a_6_ = v_b_20_;
v_a_7_ = v_snd_22_;
goto _start;
}
case 9:
{
lean_object* v_cs_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v_cs_24_ = lean_ctor_get(v_a_6_, 3);
lean_inc_ref(v_cs_24_);
lean_dec_ref_known(v_a_6_, 4);
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_array_get_size(v_cs_24_);
v___x_27_ = lean_box(0);
v___x_28_ = lean_nat_dec_lt(v___x_25_, v___x_26_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; 
lean_dec_ref(v_cs_24_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_27_);
lean_ctor_set(v___x_29_, 1, v_a_7_);
return v___x_29_;
}
else
{
size_t v___x_30_; size_t v___x_31_; lean_object* v___x_32_; 
v___x_30_ = ((size_t)0ULL);
v___x_31_ = lean_usize_of_nat(v___x_26_);
v___x_32_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_cs_24_, v___x_30_, v___x_31_, v___x_27_, v_a_7_);
lean_dec_ref(v_cs_24_);
return v___x_32_;
}
}
default: 
{
uint8_t v___x_33_; 
v___x_33_ = l_Lean_IR_FnBody_isTerminal(v_a_6_);
if (v___x_33_ == 0)
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_IR_FnBody_body(v_a_6_);
lean_dec(v_a_6_);
v_a_6_ = v___x_34_;
goto _start;
}
else
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_a_6_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v_a_7_);
return v___x_37_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(lean_object* v_as_38_, size_t v_i_39_, size_t v_stop_40_, lean_object* v_b_41_, lean_object* v___y_42_){
_start:
{
uint8_t v___x_43_; 
v___x_43_ = lean_usize_dec_eq(v_i_39_, v_stop_40_);
if (v___x_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_fst_47_; lean_object* v_snd_48_; size_t v___x_49_; size_t v___x_50_; 
v___x_44_ = lean_array_uget_borrowed(v_as_38_, v_i_39_);
v___x_45_ = l_Lean_IR_Alt_body(v___x_44_);
v___x_46_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(v___x_45_, v___y_42_);
v_fst_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc(v_fst_47_);
v_snd_48_ = lean_ctor_get(v___x_46_, 1);
lean_inc(v_snd_48_);
lean_dec_ref(v___x_46_);
v___x_49_ = ((size_t)1ULL);
v___x_50_ = lean_usize_add(v_i_39_, v___x_49_);
v_i_39_ = v___x_50_;
v_b_41_ = v_fst_47_;
v___y_42_ = v_snd_48_;
goto _start;
}
else
{
lean_object* v___x_52_; 
v___x_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_52_, 0, v_b_41_);
lean_ctor_set(v___x_52_, 1, v___y_42_);
return v___x_52_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0___boxed(lean_object* v_as_53_, lean_object* v_i_54_, lean_object* v_stop_55_, lean_object* v_b_56_, lean_object* v___y_57_){
_start:
{
size_t v_i_boxed_58_; size_t v_stop_boxed_59_; lean_object* v_res_60_; 
v_i_boxed_58_ = lean_unbox_usize(v_i_54_);
lean_dec(v_i_54_);
v_stop_boxed_59_ = lean_unbox_usize(v_stop_55_);
lean_dec(v_stop_55_);
v_res_60_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_as_53_, v_i_boxed_58_, v_stop_boxed_59_, v_b_56_, v___y_57_);
lean_dec_ref(v_as_53_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectDecl(lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
if (lean_obj_tag(v_a_61_) == 0)
{
lean_object* v_body_63_; lean_object* v___x_64_; 
v_body_63_ = lean_ctor_get(v_a_61_, 3);
lean_inc(v_body_63_);
lean_dec_ref_known(v_a_61_, 5);
v___x_64_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(v_body_63_, v_a_62_);
return v___x_64_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; 
lean_dec_ref_known(v_a_61_, 4);
v___x_65_ = lean_box(0);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v_a_62_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls(lean_object* v_decl_67_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v_snd_70_; 
v___x_68_ = l_Lean_NameSet_empty;
v___x_69_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectDecl(v_decl_67_, v___x_68_);
v_snd_70_ = lean_ctor_get(v___x_69_, 1);
lean_inc(v_snd_70_);
lean_dec_ref(v___x_69_);
return v_snd_70_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_71_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0);
v___x_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_74_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_75_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1);
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
lean_ctor_set(v___x_77_, 2, v___x_76_);
lean_ctor_set(v___x_77_, 3, v___x_76_);
lean_ctor_set(v___x_77_, 4, v___x_75_);
lean_ctor_set(v___x_77_, 5, v___x_75_);
lean_ctor_set(v___x_77_, 6, v___x_75_);
lean_ctor_set(v___x_77_, 7, v___x_75_);
lean_ctor_set(v___x_77_, 8, v___x_75_);
lean_ctor_set(v___x_77_, 9, v___x_75_);
lean_ctor_set(v___x_77_, 10, v___x_75_);
lean_ctor_set(v___x_77_, 11, v___x_74_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_unsigned_to_nat(32u);
v___x_79_ = lean_mk_empty_array_with_capacity(v___x_78_);
v___x_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_81_ = ((size_t)5ULL);
v___x_82_ = lean_unsigned_to_nat(0u);
v___x_83_ = lean_unsigned_to_nat(32u);
v___x_84_ = lean_mk_empty_array_with_capacity(v___x_83_);
v___x_85_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3);
v___x_86_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_82_);
lean_ctor_set(v___x_86_, 3, v___x_82_);
lean_ctor_set_usize(v___x_86_, 4, v___x_81_);
return v___x_86_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = lean_box(1);
v___x_88_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4);
v___x_89_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1);
v___x_90_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_87_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(lean_object* v_msgData_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___x_95_; lean_object* v_toCold_96_; lean_object* v_env_97_; lean_object* v_options_98_; uint8_t v___x_99_; lean_object* v_env_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_95_ = lean_st_ref_get(v___y_93_);
v_toCold_96_ = lean_ctor_get(v___y_92_, 0);
v_env_97_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_env_97_);
lean_dec(v___x_95_);
v_options_98_ = lean_ctor_get(v_toCold_96_, 2);
v___x_99_ = 0;
v_env_100_ = l_Lean_Environment_setRecordingDeps(v_env_97_, v___x_99_);
v___x_101_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2);
v___x_102_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_98_);
v___x_103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_103_, 0, v_env_100_);
lean_ctor_set(v___x_103_, 1, v___x_101_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
lean_ctor_set(v___x_103_, 3, v_options_98_);
v___x_104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
lean_ctor_set(v___x_104_, 1, v_msgData_91_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___boxed(lean_object* v_msgData_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(v_msgData_106_, v___y_107_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v___y_107_);
return v_res_110_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_111_; double v___x_112_; 
v___x_111_ = lean_unsigned_to_nat(0u);
v___x_112_ = lean_float_of_nat(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(lean_object* v_cls_116_, lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_ref_121_; lean_object* v___x_122_; lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_168_; 
v_ref_121_ = lean_ctor_get(v___y_118_, 2);
v___x_122_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(v_msg_117_, v___y_118_, v___y_119_);
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_168_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_168_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_168_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v_traceState_128_; lean_object* v_env_129_; lean_object* v_nextMacroScope_130_; lean_object* v_ngen_131_; lean_object* v_auxDeclNGen_132_; lean_object* v_cache_133_; lean_object* v_recordedDeps_134_; lean_object* v_messages_135_; lean_object* v_infoState_136_; lean_object* v_snapshotTasks_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_167_; 
v___x_127_ = lean_st_ref_take(v___y_119_);
v_traceState_128_ = lean_ctor_get(v___x_127_, 4);
v_env_129_ = lean_ctor_get(v___x_127_, 0);
v_nextMacroScope_130_ = lean_ctor_get(v___x_127_, 1);
v_ngen_131_ = lean_ctor_get(v___x_127_, 2);
v_auxDeclNGen_132_ = lean_ctor_get(v___x_127_, 3);
v_cache_133_ = lean_ctor_get(v___x_127_, 5);
v_recordedDeps_134_ = lean_ctor_get(v___x_127_, 6);
v_messages_135_ = lean_ctor_get(v___x_127_, 7);
v_infoState_136_ = lean_ctor_get(v___x_127_, 8);
v_snapshotTasks_137_ = lean_ctor_get(v___x_127_, 9);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_167_ == 0)
{
v___x_139_ = v___x_127_;
v_isShared_140_ = v_isSharedCheck_167_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snapshotTasks_137_);
lean_inc(v_infoState_136_);
lean_inc(v_messages_135_);
lean_inc(v_recordedDeps_134_);
lean_inc(v_cache_133_);
lean_inc(v_traceState_128_);
lean_inc(v_auxDeclNGen_132_);
lean_inc(v_ngen_131_);
lean_inc(v_nextMacroScope_130_);
lean_inc(v_env_129_);
lean_dec(v___x_127_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_167_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
uint64_t v_tid_141_; lean_object* v_traces_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_166_; 
v_tid_141_ = lean_ctor_get_uint64(v_traceState_128_, sizeof(void*)*1);
v_traces_142_ = lean_ctor_get(v_traceState_128_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_traceState_128_);
if (v_isSharedCheck_166_ == 0)
{
v___x_144_ = v_traceState_128_;
v_isShared_145_ = v_isSharedCheck_166_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_traces_142_);
lean_dec(v_traceState_128_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_166_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_147_; double v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_box(0);
v___x_148_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0);
v___x_149_ = 0;
v___x_150_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1));
v___x_151_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_151_, 0, v_cls_116_);
lean_ctor_set(v___x_151_, 1, v___x_147_);
lean_ctor_set(v___x_151_, 2, v___x_150_);
lean_ctor_set_float(v___x_151_, sizeof(void*)*3, v___x_148_);
lean_ctor_set_float(v___x_151_, sizeof(void*)*3 + 8, v___x_148_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*3 + 16, v___x_149_);
v___x_152_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2));
v___x_153_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_151_);
lean_ctor_set(v___x_153_, 1, v_a_123_);
lean_ctor_set(v___x_153_, 2, v___x_152_);
lean_inc(v_ref_121_);
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v_ref_121_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = l_Lean_PersistentArray_push___redArg(v_traces_142_, v___x_154_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_155_);
v___x_157_ = v___x_144_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_155_);
lean_ctor_set_uint64(v_reuseFailAlloc_165_, sizeof(void*)*1, v_tid_141_);
v___x_157_ = v_reuseFailAlloc_165_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_159_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 4, v___x_157_);
v___x_159_ = v___x_139_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_env_129_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_nextMacroScope_130_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_ngen_131_);
lean_ctor_set(v_reuseFailAlloc_164_, 3, v_auxDeclNGen_132_);
lean_ctor_set(v_reuseFailAlloc_164_, 4, v___x_157_);
lean_ctor_set(v_reuseFailAlloc_164_, 5, v_cache_133_);
lean_ctor_set(v_reuseFailAlloc_164_, 6, v_recordedDeps_134_);
lean_ctor_set(v_reuseFailAlloc_164_, 7, v_messages_135_);
lean_ctor_set(v_reuseFailAlloc_164_, 8, v_infoState_136_);
lean_ctor_set(v_reuseFailAlloc_164_, 9, v_snapshotTasks_137_);
v___x_159_ = v_reuseFailAlloc_164_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_160_ = lean_st_ref_put(v___y_119_, v___x_159_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_146_);
v___x_162_ = v___x_125_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_146_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___boxed(lean_object* v_cls_169_, lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(v_cls_169_, v_msg_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
return v_res_174_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0);
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5));
v___x_190_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7));
v___x_191_ = l_Lean_Name_append(v___x_190_, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9));
v___x_194_ = l_Lean_stringToMessageData(v___x_193_);
return v___x_194_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11));
v___x_197_ = l_Lean_stringToMessageData(v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(lean_object* v_init_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v_k_203_; lean_object* v_l_204_; lean_object* v_r_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v_k_203_ = lean_ctor_get(v_x_199_, 1);
lean_inc(v_k_203_);
v_l_204_ = lean_ctor_get(v_x_199_, 3);
lean_inc(v_l_204_);
v_r_205_ = lean_ctor_get(v_x_199_, 4);
lean_inc(v_r_205_);
lean_dec_ref_known(v_x_199_, 5);
v___x_206_ = lean_box(0);
v___x_207_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v_init_198_, v_l_204_, v___y_200_, v___y_201_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v___x_208_; lean_object* v_env_209_; uint8_t v___x_210_; 
lean_dec_ref_known(v___x_207_, 1);
v___x_208_ = lean_st_ref_get(v___y_201_);
v_env_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc_ref(v_env_209_);
lean_dec(v___x_208_);
v___x_210_ = l_Lean_isDeclMeta(v_env_209_, v_k_203_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_IR_findLocalDecl___redArg(v_k_203_, v___y_201_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
if (lean_obj_tag(v_a_212_) == 1)
{
lean_object* v_val_213_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v_toCold_248_; lean_object* v_options_249_; uint8_t v_hasTrace_250_; 
v_val_213_ = lean_ctor_get(v_a_212_, 0);
lean_inc(v_val_213_);
lean_dec_ref_known(v_a_212_, 1);
v_toCold_248_ = lean_ctor_get(v___y_200_, 0);
v_options_249_ = lean_ctor_get(v_toCold_248_, 2);
v_hasTrace_250_ = lean_ctor_get_uint8(v_options_249_, sizeof(void*)*1);
if (v_hasTrace_250_ == 0)
{
v___y_215_ = v___y_200_;
v___y_216_ = v___y_201_;
goto v___jp_214_;
}
else
{
lean_object* v_inheritedTraceOptions_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v_inheritedTraceOptions_251_ = lean_ctor_get(v_toCold_248_, 11);
v___x_252_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5));
v___x_253_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8);
v___x_254_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_251_, v_options_249_, v___x_253_);
if (v___x_254_ == 0)
{
v___y_215_ = v___y_200_;
v___y_216_ = v___y_201_;
goto v___jp_214_;
}
else
{
lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_255_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10);
lean_inc(v_k_203_);
v___x_256_ = l_Lean_MessageData_ofName(v_k_203_);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_257_);
lean_ctor_set(v___x_259_, 1, v___x_258_);
v___x_260_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(v___x_252_, v___x_259_, v___y_200_, v___y_201_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_dec_ref_known(v___x_260_, 1);
v___y_215_ = v___y_200_;
v___y_216_ = v___y_201_;
goto v___jp_214_;
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v_val_213_);
lean_dec(v_r_205_);
lean_dec(v_k_203_);
v_a_261_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_260_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
v___jp_214_:
{
lean_object* v___x_217_; lean_object* v_env_218_; lean_object* v_nextMacroScope_219_; lean_object* v_ngen_220_; lean_object* v_auxDeclNGen_221_; lean_object* v_traceState_222_; lean_object* v_recordedDeps_223_; lean_object* v_messages_224_; lean_object* v_infoState_225_; lean_object* v_snapshotTasks_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_246_; 
v___x_217_ = lean_st_ref_take(v___y_216_);
v_env_218_ = lean_ctor_get(v___x_217_, 0);
v_nextMacroScope_219_ = lean_ctor_get(v___x_217_, 1);
v_ngen_220_ = lean_ctor_get(v___x_217_, 2);
v_auxDeclNGen_221_ = lean_ctor_get(v___x_217_, 3);
v_traceState_222_ = lean_ctor_get(v___x_217_, 4);
v_recordedDeps_223_ = lean_ctor_get(v___x_217_, 6);
v_messages_224_ = lean_ctor_get(v___x_217_, 7);
v_infoState_225_ = lean_ctor_get(v___x_217_, 8);
v_snapshotTasks_226_ = lean_ctor_get(v___x_217_, 9);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v___x_217_, 5);
lean_dec(v_unused_247_);
v___x_228_ = v___x_217_;
v_isShared_229_ = v_isSharedCheck_246_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_snapshotTasks_226_);
lean_inc(v_infoState_225_);
lean_inc(v_messages_224_);
lean_inc(v_recordedDeps_223_);
lean_inc(v_traceState_222_);
lean_inc(v_auxDeclNGen_221_);
lean_inc(v_ngen_220_);
lean_inc(v_nextMacroScope_219_);
lean_inc(v_env_218_);
lean_dec(v___x_217_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_246_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = l_Lean_setDeclMeta(v_env_218_, v_k_203_);
v___x_231_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1);
if (v_isShared_229_ == 0)
{
lean_ctor_set(v___x_228_, 5, v___x_231_);
lean_ctor_set(v___x_228_, 0, v___x_230_);
v___x_233_ = v___x_228_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_nextMacroScope_219_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_ngen_220_);
lean_ctor_set(v_reuseFailAlloc_245_, 3, v_auxDeclNGen_221_);
lean_ctor_set(v_reuseFailAlloc_245_, 4, v_traceState_222_);
lean_ctor_set(v_reuseFailAlloc_245_, 5, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_245_, 6, v_recordedDeps_223_);
lean_ctor_set(v_reuseFailAlloc_245_, 7, v_messages_224_);
lean_ctor_set(v_reuseFailAlloc_245_, 8, v_infoState_225_);
lean_ctor_set(v_reuseFailAlloc_245_, 9, v_snapshotTasks_226_);
v___x_233_ = v_reuseFailAlloc_245_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_st_ref_put(v___y_216_, v___x_233_);
v___x_235_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(v_val_213_, v___y_215_, v___y_216_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_dec_ref_known(v___x_235_, 1);
v_init_198_ = v___x_206_;
v_x_199_ = v_r_205_;
goto _start;
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_r_205_);
v_a_237_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_235_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_242_; 
if (v_isShared_240_ == 0)
{
v___x_242_ = v___x_239_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_237_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_212_);
lean_dec(v_k_203_);
v_init_198_ = v___x_206_;
v_x_199_ = v_r_205_;
goto _start;
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_r_205_);
lean_dec(v_k_203_);
v_a_270_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_211_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_211_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
else
{
lean_dec(v_k_203_);
v_init_198_ = v___x_206_;
v_x_199_ = v_r_205_;
goto _start;
}
}
else
{
lean_dec(v_r_205_);
lean_dec(v_k_203_);
return v___x_207_;
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v_init_198_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(lean_object* v_decl_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls(v_decl_281_);
v___x_286_ = lean_box(0);
v___x_287_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v___x_286_, v___x_285_, v_a_282_, v_a_283_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_294_ == 0)
{
lean_object* v_unused_295_; 
v_unused_295_ = lean_ctor_get(v___x_287_, 0);
lean_dec(v_unused_295_);
v___x_289_ = v___x_287_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_dec(v___x_287_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_286_);
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_286_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
else
{
lean_object* v_a_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_303_; 
v_a_296_ = lean_ctor_get(v___x_287_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_287_);
if (v_isSharedCheck_303_ == 0)
{
v___x_298_ = v___x_287_;
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_a_296_);
lean_dec(v___x_287_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_303_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_301_; 
if (v_isShared_299_ == 0)
{
v___x_301_ = v___x_298_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_a_296_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta___boxed(lean_object* v_decl_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(v_decl_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___boxed(lean_object* v_init_309_, lean_object* v_x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v_init_309_, v_x_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_314_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0));
v___x_317_ = l_Lean_stringToMessageData(v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(lean_object* v_as_318_, size_t v_sz_319_, size_t v_i_320_, lean_object* v_b_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v_a_326_; uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_lt(v_i_320_, v_sz_319_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v_b_321_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v_a_333_; lean_object* v___x_334_; lean_object* v_env_335_; lean_object* v___x_336_; lean_object* v___y_338_; lean_object* v___y_339_; uint8_t v___x_362_; 
v___x_332_ = lean_box(0);
v_a_333_ = lean_array_uget_borrowed(v_as_318_, v_i_320_);
v___x_334_ = lean_st_ref_get(v___y_323_);
v_env_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc_ref(v_env_335_);
lean_dec(v___x_334_);
v___x_336_ = l_Lean_IR_Decl_name(v_a_333_);
lean_inc(v___x_336_);
v___x_362_ = l_Lean_isMarkedMeta(v_env_335_, v___x_336_);
if (v___x_362_ == 0)
{
lean_dec(v___x_336_);
v_a_326_ = v___x_332_;
goto v___jp_325_;
}
else
{
lean_object* v_toCold_363_; lean_object* v_options_364_; uint8_t v_hasTrace_365_; 
v_toCold_363_ = lean_ctor_get(v___y_322_, 0);
v_options_364_ = lean_ctor_get(v_toCold_363_, 2);
v_hasTrace_365_ = lean_ctor_get_uint8(v_options_364_, sizeof(void*)*1);
if (v_hasTrace_365_ == 0)
{
v___y_338_ = v___y_322_;
v___y_339_ = v___y_323_;
goto v___jp_337_;
}
else
{
lean_object* v_inheritedTraceOptions_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_inheritedTraceOptions_366_ = lean_ctor_get(v_toCold_363_, 11);
v___x_367_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5));
v___x_368_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8);
v___x_369_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_366_, v_options_364_, v___x_368_);
if (v___x_369_ == 0)
{
v___y_338_ = v___y_322_;
v___y_339_ = v___y_323_;
goto v___jp_337_;
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_370_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10);
lean_inc(v___x_336_);
v___x_371_ = l_Lean_MessageData_ofName(v___x_336_);
v___x_372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1);
v___x_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(v___x_367_, v___x_374_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_dec_ref_known(v___x_375_, 1);
v___y_338_ = v___y_322_;
v___y_339_ = v___y_323_;
goto v___jp_337_;
}
else
{
lean_dec(v___x_336_);
return v___x_375_;
}
}
}
}
v___jp_337_:
{
lean_object* v___x_340_; lean_object* v_env_341_; lean_object* v_nextMacroScope_342_; lean_object* v_ngen_343_; lean_object* v_auxDeclNGen_344_; lean_object* v_traceState_345_; lean_object* v_recordedDeps_346_; lean_object* v_messages_347_; lean_object* v_infoState_348_; lean_object* v_snapshotTasks_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_360_; 
v___x_340_ = lean_st_ref_take(v___y_339_);
v_env_341_ = lean_ctor_get(v___x_340_, 0);
v_nextMacroScope_342_ = lean_ctor_get(v___x_340_, 1);
v_ngen_343_ = lean_ctor_get(v___x_340_, 2);
v_auxDeclNGen_344_ = lean_ctor_get(v___x_340_, 3);
v_traceState_345_ = lean_ctor_get(v___x_340_, 4);
v_recordedDeps_346_ = lean_ctor_get(v___x_340_, 6);
v_messages_347_ = lean_ctor_get(v___x_340_, 7);
v_infoState_348_ = lean_ctor_get(v___x_340_, 8);
v_snapshotTasks_349_ = lean_ctor_get(v___x_340_, 9);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_360_ == 0)
{
lean_object* v_unused_361_; 
v_unused_361_ = lean_ctor_get(v___x_340_, 5);
lean_dec(v_unused_361_);
v___x_351_ = v___x_340_;
v_isShared_352_ = v_isSharedCheck_360_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_snapshotTasks_349_);
lean_inc(v_infoState_348_);
lean_inc(v_messages_347_);
lean_inc(v_recordedDeps_346_);
lean_inc(v_traceState_345_);
lean_inc(v_auxDeclNGen_344_);
lean_inc(v_ngen_343_);
lean_inc(v_nextMacroScope_342_);
lean_inc(v_env_341_);
lean_dec(v___x_340_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_360_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_353_ = l_Lean_setDeclMeta(v_env_341_, v___x_336_);
v___x_354_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 5, v___x_354_);
lean_ctor_set(v___x_351_, 0, v___x_353_);
v___x_356_ = v___x_351_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v_nextMacroScope_342_);
lean_ctor_set(v_reuseFailAlloc_359_, 2, v_ngen_343_);
lean_ctor_set(v_reuseFailAlloc_359_, 3, v_auxDeclNGen_344_);
lean_ctor_set(v_reuseFailAlloc_359_, 4, v_traceState_345_);
lean_ctor_set(v_reuseFailAlloc_359_, 5, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_359_, 6, v_recordedDeps_346_);
lean_ctor_set(v_reuseFailAlloc_359_, 7, v_messages_347_);
lean_ctor_set(v_reuseFailAlloc_359_, 8, v_infoState_348_);
lean_ctor_set(v_reuseFailAlloc_359_, 9, v_snapshotTasks_349_);
v___x_356_ = v_reuseFailAlloc_359_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_st_ref_put(v___y_339_, v___x_356_);
lean_inc(v_a_333_);
v___x_358_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(v_a_333_, v___y_338_, v___y_339_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_dec_ref_known(v___x_358_, 1);
v_a_326_ = v___x_332_;
goto v___jp_325_;
}
else
{
return v___x_358_;
}
}
}
}
}
v___jp_325_:
{
size_t v___x_327_; size_t v___x_328_; 
v___x_327_ = ((size_t)1ULL);
v___x_328_ = lean_usize_add(v_i_320_, v___x_327_);
v_i_320_ = v___x_328_;
v_b_321_ = v_a_326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___boxed(lean_object* v_as_376_, lean_object* v_sz_377_, lean_object* v_i_378_, lean_object* v_b_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_){
_start:
{
size_t v_sz_boxed_383_; size_t v_i_boxed_384_; lean_object* v_res_385_; 
v_sz_boxed_383_ = lean_unbox_usize(v_sz_377_);
lean_dec(v_sz_377_);
v_i_boxed_384_ = lean_unbox_usize(v_i_378_);
lean_dec(v_i_378_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(v_as_376_, v_sz_boxed_383_, v_i_boxed_384_, v_b_379_, v___y_380_, v___y_381_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
lean_dec_ref(v_as_376_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferMeta(lean_object* v_decls_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_390_; lean_object* v_env_391_; lean_object* v___x_392_; uint8_t v_isModule_393_; 
v___x_390_ = lean_st_ref_get(v_a_388_);
v_env_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc_ref(v_env_391_);
lean_dec(v___x_390_);
v___x_392_ = l_Lean_Environment_header(v_env_391_);
lean_dec_ref(v_env_391_);
v_isModule_393_ = lean_ctor_get_uint8(v___x_392_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_392_);
if (v_isModule_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_394_ = lean_box(0);
v___x_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; size_t v_sz_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_396_ = lean_box(0);
v_sz_397_ = lean_array_size(v_decls_386_);
v___x_398_ = ((size_t)0ULL);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(v_decls_386_, v_sz_397_, v___x_398_, v___x_396_, v_a_387_, v_a_388_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_399_, 0);
lean_dec(v_unused_407_);
v___x_401_ = v___x_399_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_dec(v___x_399_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v___x_396_);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_396_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
else
{
return v___x_399_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferMeta___boxed(lean_object* v_decls_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_IR_inferMeta(v_decls_408_, v_a_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec_ref(v_decls_408_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* lean_eval_check_meta(lean_object* v_env_417_, lean_object* v_declName_418_){
_start:
{
uint8_t v___x_419_; uint8_t v___x_420_; uint8_t v___x_421_; 
lean_inc(v_declName_418_);
v___x_419_ = l_Lean_getIRPhases(v_env_417_, v_declName_418_);
v___x_420_ = 0;
v___x_421_ = l_Lean_instBEqIRPhases_beq(v___x_419_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; 
lean_dec(v_declName_418_);
v___x_422_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0));
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_423_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1));
v___x_424_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_418_, v___x_421_);
v___x_425_ = lean_string_append(v___x_423_, v___x_424_);
lean_dec_ref(v___x_424_);
v___x_426_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2));
v___x_427_ = lean_string_append(v___x_425_, v___x_426_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
return v___x_428_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_unsigned_to_nat(3167601923u);
v___x_479_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_));
v___x_480_ = l_Lean_Name_num___override(v___x_479_, v___x_478_);
return v___x_480_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_482_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_));
v___x_483_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_484_ = l_Lean_Name_str___override(v___x_483_, v___x_482_);
return v___x_484_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_));
v___x_487_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_488_ = l_Lean_Name_str___override(v___x_487_, v___x_486_);
return v___x_488_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = lean_unsigned_to_nat(2u);
v___x_490_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_491_ = l_Lean_Name_num___override(v___x_490_, v___x_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_493_; uint8_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_493_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5));
v___x_494_ = 0;
v___x_495_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_496_ = l_Lean_registerTraceClass(v___x_493_, v___x_494_, v___x_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2____boxed(lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_();
return v_res_498_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Meta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_Meta(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_Meta(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_Meta(builtin);
}
#ifdef __cplusplus
}
#endif
