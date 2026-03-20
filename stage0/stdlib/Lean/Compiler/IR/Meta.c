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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_isDeclMeta(lean_object*, lean_object*);
lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_setDeclMeta(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_IR_Alt_body(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__0;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__1;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__2;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inferMeta"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__4_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__6_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 96, 118, 160, 52, 15, 195, 103)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__6_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(178, 39, 14, 26, 17, 0, 113, 234)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__6_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Marking "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__7_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__8;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = " as meta because it is in `meta` closure"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__9 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__9_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__10;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_6_);
switch(lean_obj_tag(v_e_8_))
{
case 6:
{
lean_object* v_c_16_; 
v_c_16_ = lean_ctor_get(v_e_8_, 0);
lean_inc(v_c_16_);
lean_dec_ref(v_e_8_);
v_f_11_ = v_c_16_;
v___y_12_ = v_a_7_;
goto v___jp_10_;
}
case 7:
{
lean_object* v_c_17_; 
v_c_17_ = lean_ctor_get(v_e_8_, 0);
lean_inc(v_c_17_);
lean_dec_ref(v_e_8_);
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
lean_dec_ref(v_a_6_);
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
lean_dec_ref(v_a_6_);
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
uint8_t v___x_30_; 
v___x_30_ = lean_nat_dec_le(v___x_26_, v___x_26_);
if (v___x_30_ == 0)
{
if (v___x_28_ == 0)
{
lean_object* v___x_31_; 
lean_dec_ref(v_cs_24_);
v___x_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_31_, 0, v___x_27_);
lean_ctor_set(v___x_31_, 1, v_a_7_);
return v___x_31_;
}
else
{
size_t v___x_32_; size_t v___x_33_; lean_object* v___x_34_; 
v___x_32_ = ((size_t)0ULL);
v___x_33_ = lean_usize_of_nat(v___x_26_);
v___x_34_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_cs_24_, v___x_32_, v___x_33_, v___x_27_, v_a_7_);
lean_dec_ref(v_cs_24_);
return v___x_34_;
}
}
else
{
size_t v___x_35_; size_t v___x_36_; lean_object* v___x_37_; 
v___x_35_ = ((size_t)0ULL);
v___x_36_ = lean_usize_of_nat(v___x_26_);
v___x_37_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_cs_24_, v___x_35_, v___x_36_, v___x_27_, v_a_7_);
lean_dec_ref(v_cs_24_);
return v___x_37_;
}
}
}
default: 
{
uint8_t v___x_38_; 
v___x_38_ = l_Lean_IR_FnBody_isTerminal(v_a_6_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_IR_FnBody_body(v_a_6_);
lean_dec(v_a_6_);
v_a_6_ = v___x_39_;
goto _start;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_dec(v_a_6_);
v___x_41_ = lean_box(0);
v___x_42_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v_a_7_);
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(lean_object* v_as_43_, size_t v_i_44_, size_t v_stop_45_, lean_object* v_b_46_, lean_object* v___y_47_){
_start:
{
uint8_t v___x_48_; 
v___x_48_ = lean_usize_dec_eq(v_i_44_, v_stop_45_);
if (v___x_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v_fst_52_; lean_object* v_snd_53_; size_t v___x_54_; size_t v___x_55_; 
v___x_49_ = lean_array_uget_borrowed(v_as_43_, v_i_44_);
v___x_50_ = l_Lean_IR_Alt_body(v___x_49_);
v___x_51_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(v___x_50_, v___y_47_);
v_fst_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_fst_52_);
v_snd_53_ = lean_ctor_get(v___x_51_, 1);
lean_inc(v_snd_53_);
lean_dec_ref(v___x_51_);
v___x_54_ = ((size_t)1ULL);
v___x_55_ = lean_usize_add(v_i_44_, v___x_54_);
v_i_44_ = v___x_55_;
v_b_46_ = v_fst_52_;
v___y_47_ = v_snd_53_;
goto _start;
}
else
{
lean_object* v___x_57_; 
v___x_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_57_, 0, v_b_46_);
lean_ctor_set(v___x_57_, 1, v___y_47_);
return v___x_57_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0___boxed(lean_object* v_as_58_, lean_object* v_i_59_, lean_object* v_stop_60_, lean_object* v_b_61_, lean_object* v___y_62_){
_start:
{
size_t v_i_boxed_63_; size_t v_stop_boxed_64_; lean_object* v_res_65_; 
v_i_boxed_63_ = lean_unbox_usize(v_i_59_);
lean_dec(v_i_59_);
v_stop_boxed_64_ = lean_unbox_usize(v_stop_60_);
lean_dec(v_stop_60_);
v_res_65_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody_spec__0(v_as_58_, v_i_boxed_63_, v_stop_boxed_64_, v_b_61_, v___y_62_);
lean_dec_ref(v_as_58_);
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectDecl(lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
if (lean_obj_tag(v_a_66_) == 0)
{
lean_object* v_body_68_; lean_object* v___x_69_; 
v_body_68_ = lean_ctor_get(v_a_66_, 3);
lean_inc(v_body_68_);
lean_dec_ref(v_a_66_);
v___x_69_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectFnBody(v_body_68_, v_a_67_);
return v___x_69_;
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec_ref(v_a_66_);
v___x_70_ = lean_box(0);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v_a_67_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls(lean_object* v_decl_72_){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v_snd_75_; 
v___x_73_ = l_Lean_NameSet_empty;
v___x_74_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls_collectDecl(v_decl_72_, v___x_73_);
v_snd_75_ = lean_ctor_get(v___x_74_, 1);
lean_inc(v_snd_75_);
lean_dec_ref(v___x_74_);
return v_snd_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg(lean_object* v_cls_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_options_82_; uint8_t v_hasTrace_83_; 
v_options_82_ = lean_ctor_get(v___y_80_, 2);
v_hasTrace_83_ = lean_ctor_get_uint8(v_options_82_, sizeof(void*)*1);
if (v_hasTrace_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_cls_79_);
v___x_84_ = lean_box(v_hasTrace_83_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
else
{
lean_object* v_inheritedTraceOptions_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v_inheritedTraceOptions_86_ = lean_ctor_get(v___y_80_, 13);
v___x_87_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg___closed__1));
v___x_88_ = l_Lean_Name_append(v___x_87_, v_cls_79_);
v___x_89_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_86_, v_options_82_, v___x_88_);
lean_dec(v___x_88_);
v___x_90_ = lean_box(v___x_89_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg___boxed(lean_object* v_cls_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg(v_cls_92_, v___y_93_);
lean_dec_ref(v___y_93_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(lean_object* v_cls_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg(v_cls_96_, v___y_97_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___boxed(lean_object* v_cls_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(v_cls_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_105_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_106_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__1);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
lean_ctor_set(v___x_111_, 2, v___x_110_);
lean_ctor_set(v___x_111_, 3, v___x_109_);
lean_ctor_set(v___x_111_, 4, v___x_109_);
lean_ctor_set(v___x_111_, 5, v___x_109_);
lean_ctor_set(v___x_111_, 6, v___x_109_);
lean_ctor_set(v___x_111_, 7, v___x_109_);
lean_ctor_set(v___x_111_, 8, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__3(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_unsigned_to_nat(32u);
v___x_113_ = lean_mk_empty_array_with_capacity(v___x_112_);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__4(void){
_start:
{
size_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_115_ = ((size_t)5ULL);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_unsigned_to_nat(32u);
v___x_118_ = lean_mk_empty_array_with_capacity(v___x_117_);
v___x_119_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__3);
v___x_120_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_116_);
lean_ctor_set(v___x_120_, 3, v___x_116_);
lean_ctor_set_usize(v___x_120_, 4, v___x_115_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__5(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_121_ = lean_box(1);
v___x_122_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__4);
v___x_123_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__1);
v___x_124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_122_);
lean_ctor_set(v___x_124_, 2, v___x_121_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1(lean_object* v_msgData_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v___x_129_; lean_object* v_env_130_; lean_object* v_options_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_129_ = lean_st_ref_get(v___y_127_);
v_env_130_ = lean_ctor_get(v___x_129_, 0);
lean_inc_ref(v_env_130_);
lean_dec(v___x_129_);
v_options_131_ = lean_ctor_get(v___y_126_, 2);
v___x_132_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__2);
v___x_133_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___closed__5);
lean_inc_ref(v_options_131_);
v___x_134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_134_, 0, v_env_130_);
lean_ctor_set(v___x_134_, 1, v___x_132_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
lean_ctor_set(v___x_134_, 3, v_options_131_);
v___x_135_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_msgData_125_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1___boxed(lean_object* v_msgData_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1(v_msgData_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
return v_res_141_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0(void){
_start:
{
lean_object* v___x_142_; double v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_float_of_nat(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(lean_object* v_cls_147_, lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_ref_152_; lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_198_; 
v_ref_152_ = lean_ctor_get(v___y_149_, 5);
v___x_153_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1_spec__1(v_msg_148_, v___y_149_, v___y_150_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_198_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_198_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_198_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v_traceState_159_; lean_object* v_env_160_; lean_object* v_nextMacroScope_161_; lean_object* v_ngen_162_; lean_object* v_auxDeclNGen_163_; lean_object* v_cache_164_; lean_object* v_messages_165_; lean_object* v_infoState_166_; lean_object* v_snapshotTasks_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_197_; 
v___x_158_ = lean_st_ref_take(v___y_150_);
v_traceState_159_ = lean_ctor_get(v___x_158_, 4);
v_env_160_ = lean_ctor_get(v___x_158_, 0);
v_nextMacroScope_161_ = lean_ctor_get(v___x_158_, 1);
v_ngen_162_ = lean_ctor_get(v___x_158_, 2);
v_auxDeclNGen_163_ = lean_ctor_get(v___x_158_, 3);
v_cache_164_ = lean_ctor_get(v___x_158_, 5);
v_messages_165_ = lean_ctor_get(v___x_158_, 6);
v_infoState_166_ = lean_ctor_get(v___x_158_, 7);
v_snapshotTasks_167_ = lean_ctor_get(v___x_158_, 8);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_197_ == 0)
{
v___x_169_ = v___x_158_;
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_snapshotTasks_167_);
lean_inc(v_infoState_166_);
lean_inc(v_messages_165_);
lean_inc(v_cache_164_);
lean_inc(v_traceState_159_);
lean_inc(v_auxDeclNGen_163_);
lean_inc(v_ngen_162_);
lean_inc(v_nextMacroScope_161_);
lean_inc(v_env_160_);
lean_dec(v___x_158_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
uint64_t v_tid_171_; lean_object* v_traces_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_196_; 
v_tid_171_ = lean_ctor_get_uint64(v_traceState_159_, sizeof(void*)*1);
v_traces_172_ = lean_ctor_get(v_traceState_159_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v_traceState_159_);
if (v_isSharedCheck_196_ == 0)
{
v___x_174_ = v_traceState_159_;
v_isShared_175_ = v_isSharedCheck_196_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_traces_172_);
lean_dec(v_traceState_159_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_196_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; double v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_176_ = lean_box(0);
v___x_177_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0);
v___x_178_ = 0;
v___x_179_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1));
v___x_180_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_180_, 0, v_cls_147_);
lean_ctor_set(v___x_180_, 1, v___x_176_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
lean_ctor_set_float(v___x_180_, sizeof(void*)*3, v___x_177_);
lean_ctor_set_float(v___x_180_, sizeof(void*)*3 + 8, v___x_177_);
lean_ctor_set_uint8(v___x_180_, sizeof(void*)*3 + 16, v___x_178_);
v___x_181_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2));
v___x_182_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v_a_154_);
lean_ctor_set(v___x_182_, 2, v___x_181_);
lean_inc(v_ref_152_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_ref_152_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = l_Lean_PersistentArray_push___redArg(v_traces_172_, v___x_183_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_184_);
v___x_186_ = v___x_174_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_184_);
lean_ctor_set_uint64(v_reuseFailAlloc_195_, sizeof(void*)*1, v_tid_171_);
v___x_186_ = v_reuseFailAlloc_195_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_188_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 4, v___x_186_);
v___x_188_ = v___x_169_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_env_160_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_nextMacroScope_161_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_ngen_162_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_auxDeclNGen_163_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_194_, 5, v_cache_164_);
lean_ctor_set(v_reuseFailAlloc_194_, 6, v_messages_165_);
lean_ctor_set(v_reuseFailAlloc_194_, 7, v_infoState_166_);
lean_ctor_set(v_reuseFailAlloc_194_, 8, v_snapshotTasks_167_);
v___x_188_ = v_reuseFailAlloc_194_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_189_ = lean_st_ref_set(v___y_150_, v___x_188_);
v___x_190_ = lean_box(0);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_190_);
v___x_192_ = v___x_156_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___boxed(lean_object* v_cls_199_, lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v_cls_199_, v_msg_200_, v___y_201_, v___y_202_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_204_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_205_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__0, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__0);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__2(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__1);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__8(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__7));
v___x_219_ = l_Lean_stringToMessageData(v___x_218_);
return v___x_219_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__10(void){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__9));
v___x_222_ = l_Lean_stringToMessageData(v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2(lean_object* v_init_223_, lean_object* v_x_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
if (lean_obj_tag(v_x_224_) == 0)
{
lean_object* v_k_228_; lean_object* v_l_229_; lean_object* v_r_230_; lean_object* v___x_231_; 
v_k_228_ = lean_ctor_get(v_x_224_, 1);
lean_inc(v_k_228_);
v_l_229_ = lean_ctor_get(v_x_224_, 3);
lean_inc(v_l_229_);
v_r_230_ = lean_ctor_get(v_x_224_, 4);
lean_inc(v_r_230_);
lean_dec_ref(v_x_224_);
v___x_231_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2(v_init_223_, v_l_229_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v___x_232_; lean_object* v_env_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
lean_dec_ref(v___x_231_);
v___x_232_ = lean_st_ref_get(v___y_226_);
v_env_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc_ref(v_env_233_);
lean_dec(v___x_232_);
v___x_234_ = lean_box(0);
v___x_235_ = l_Lean_isDeclMeta(v_env_233_, v_k_228_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
v___x_236_ = l_Lean_IR_findLocalDecl___redArg(v_k_228_, v___y_226_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref(v___x_236_);
if (lean_obj_tag(v_a_237_) == 1)
{
lean_object* v_val_238_; lean_object* v___y_240_; lean_object* v___y_241_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v_a_274_; uint8_t v___x_275_; 
v_val_238_ = lean_ctor_get(v_a_237_, 0);
lean_inc(v_val_238_);
lean_dec_ref(v_a_237_);
v___x_272_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__6));
v___x_273_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg(v___x_272_, v___y_225_);
v_a_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_a_274_);
lean_dec_ref(v___x_273_);
v___x_275_ = lean_unbox(v_a_274_);
lean_dec(v_a_274_);
if (v___x_275_ == 0)
{
v___y_240_ = v___y_225_;
v___y_241_ = v___y_226_;
goto v___jp_239_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_276_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__8);
lean_inc(v_k_228_);
v___x_277_ = l_Lean_MessageData_ofName(v_k_228_);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___x_279_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__10, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__10_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__10);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___x_281_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v___x_272_, v___x_280_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_dec_ref(v___x_281_);
v___y_240_ = v___y_225_;
v___y_241_ = v___y_226_;
goto v___jp_239_;
}
else
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
lean_dec(v_val_238_);
lean_dec(v_r_230_);
lean_dec(v_k_228_);
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
}
v___jp_239_:
{
lean_object* v___x_242_; lean_object* v_env_243_; lean_object* v_nextMacroScope_244_; lean_object* v_ngen_245_; lean_object* v_auxDeclNGen_246_; lean_object* v_traceState_247_; lean_object* v_messages_248_; lean_object* v_infoState_249_; lean_object* v_snapshotTasks_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_270_; 
v___x_242_ = lean_st_ref_take(v___y_241_);
v_env_243_ = lean_ctor_get(v___x_242_, 0);
v_nextMacroScope_244_ = lean_ctor_get(v___x_242_, 1);
v_ngen_245_ = lean_ctor_get(v___x_242_, 2);
v_auxDeclNGen_246_ = lean_ctor_get(v___x_242_, 3);
v_traceState_247_ = lean_ctor_get(v___x_242_, 4);
v_messages_248_ = lean_ctor_get(v___x_242_, 6);
v_infoState_249_ = lean_ctor_get(v___x_242_, 7);
v_snapshotTasks_250_ = lean_ctor_get(v___x_242_, 8);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_270_ == 0)
{
lean_object* v_unused_271_; 
v_unused_271_ = lean_ctor_get(v___x_242_, 5);
lean_dec(v_unused_271_);
v___x_252_ = v___x_242_;
v_isShared_253_ = v_isSharedCheck_270_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_snapshotTasks_250_);
lean_inc(v_infoState_249_);
lean_inc(v_messages_248_);
lean_inc(v_traceState_247_);
lean_inc(v_auxDeclNGen_246_);
lean_inc(v_ngen_245_);
lean_inc(v_nextMacroScope_244_);
lean_inc(v_env_243_);
lean_dec(v___x_242_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_270_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_257_; 
v___x_254_ = l_Lean_setDeclMeta(v_env_243_, v_k_228_);
v___x_255_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__2);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 5, v___x_255_);
lean_ctor_set(v___x_252_, 0, v___x_254_);
v___x_257_ = v___x_252_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_nextMacroScope_244_);
lean_ctor_set(v_reuseFailAlloc_269_, 2, v_ngen_245_);
lean_ctor_set(v_reuseFailAlloc_269_, 3, v_auxDeclNGen_246_);
lean_ctor_set(v_reuseFailAlloc_269_, 4, v_traceState_247_);
lean_ctor_set(v_reuseFailAlloc_269_, 5, v___x_255_);
lean_ctor_set(v_reuseFailAlloc_269_, 6, v_messages_248_);
lean_ctor_set(v_reuseFailAlloc_269_, 7, v_infoState_249_);
lean_ctor_set(v_reuseFailAlloc_269_, 8, v_snapshotTasks_250_);
v___x_257_ = v_reuseFailAlloc_269_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_st_ref_set(v___y_241_, v___x_257_);
v___x_259_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(v_val_238_, v___y_240_, v___y_241_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_dec_ref(v___x_259_);
v_init_223_ = v___x_234_;
v_x_224_ = v_r_230_;
goto _start;
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v_r_230_);
v_a_261_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_259_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_259_);
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
}
}
else
{
lean_dec(v_a_237_);
lean_dec(v_k_228_);
v_init_223_ = v___x_234_;
v_x_224_ = v_r_230_;
goto _start;
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
lean_dec(v_r_230_);
lean_dec(v_k_228_);
v_a_291_ = lean_ctor_get(v___x_236_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_236_);
if (v_isSharedCheck_298_ == 0)
{
v___x_293_ = v___x_236_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_236_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_a_291_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
else
{
lean_dec(v_k_228_);
v_init_223_ = v___x_234_;
v_x_224_ = v_r_230_;
goto _start;
}
}
else
{
lean_dec(v_r_230_);
lean_dec(v_k_228_);
return v___x_231_;
}
}
else
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_300_, 0, v_init_223_);
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(lean_object* v_decl_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls(v_decl_302_);
v___x_307_ = lean_box(0);
v___x_308_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2(v___x_307_, v___x_306_, v_a_303_, v_a_304_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; 
v_unused_316_ = lean_ctor_get(v___x_308_, 0);
lean_dec(v_unused_316_);
v___x_310_ = v___x_308_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_dec(v___x_308_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
lean_ctor_set(v___x_310_, 0, v___x_307_);
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_307_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
else
{
lean_object* v_a_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_324_; 
v_a_317_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_324_ == 0)
{
v___x_319_ = v___x_308_;
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_a_317_);
lean_dec(v___x_308_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_324_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_322_; 
if (v_isShared_320_ == 0)
{
v___x_322_ = v___x_319_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_a_317_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta___boxed(lean_object* v_decl_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(v_decl_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___boxed(lean_object* v_init_330_, lean_object* v_x_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2(v_init_330_, v_x_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
return v_res_335_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0));
v___x_338_ = l_Lean_stringToMessageData(v___x_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(lean_object* v_as_339_, size_t v_sz_340_, size_t v_i_341_, lean_object* v_b_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_a_347_; uint8_t v___x_351_; 
v___x_351_ = lean_usize_dec_lt(v_i_341_, v_sz_340_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v_b_342_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v_env_354_; lean_object* v___x_355_; lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___y_359_; lean_object* v___y_360_; uint8_t v___x_382_; 
v___x_353_ = lean_st_ref_get(v___y_344_);
v_env_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc_ref(v_env_354_);
lean_dec(v___x_353_);
v___x_355_ = lean_box(0);
v_a_356_ = lean_array_uget_borrowed(v_as_339_, v_i_341_);
v___x_357_ = l_Lean_IR_Decl_name(v_a_356_);
lean_inc(v___x_357_);
v___x_382_ = l_Lean_isMarkedMeta(v_env_354_, v___x_357_);
if (v___x_382_ == 0)
{
lean_dec(v___x_357_);
v_a_347_ = v___x_355_;
goto v___jp_346_;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_383_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__6));
v___x_384_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___redArg(v___x_383_, v___y_343_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; uint8_t v___x_386_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref(v___x_384_);
v___x_386_ = lean_unbox(v_a_385_);
lean_dec(v_a_385_);
if (v___x_386_ == 0)
{
v___y_359_ = v___y_343_;
v___y_360_ = v___y_344_;
goto v___jp_358_;
}
else
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_387_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__8, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__8_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__8);
lean_inc(v___x_357_);
v___x_388_ = l_Lean_MessageData_ofName(v___x_357_);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1);
v___x_391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_389_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
v___x_392_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v___x_383_, v___x_391_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_dec_ref(v___x_392_);
v___y_359_ = v___y_343_;
v___y_360_ = v___y_344_;
goto v___jp_358_;
}
else
{
lean_dec(v___x_357_);
return v___x_392_;
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec(v___x_357_);
v_a_393_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___x_384_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_384_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
v___jp_358_:
{
lean_object* v___x_361_; lean_object* v_env_362_; lean_object* v_nextMacroScope_363_; lean_object* v_ngen_364_; lean_object* v_auxDeclNGen_365_; lean_object* v_traceState_366_; lean_object* v_messages_367_; lean_object* v_infoState_368_; lean_object* v_snapshotTasks_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_380_; 
v___x_361_ = lean_st_ref_take(v___y_360_);
v_env_362_ = lean_ctor_get(v___x_361_, 0);
v_nextMacroScope_363_ = lean_ctor_get(v___x_361_, 1);
v_ngen_364_ = lean_ctor_get(v___x_361_, 2);
v_auxDeclNGen_365_ = lean_ctor_get(v___x_361_, 3);
v_traceState_366_ = lean_ctor_get(v___x_361_, 4);
v_messages_367_ = lean_ctor_get(v___x_361_, 6);
v_infoState_368_ = lean_ctor_get(v___x_361_, 7);
v_snapshotTasks_369_ = lean_ctor_get(v___x_361_, 8);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v___x_361_, 5);
lean_dec(v_unused_381_);
v___x_371_ = v___x_361_;
v_isShared_372_ = v_isSharedCheck_380_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_snapshotTasks_369_);
lean_inc(v_infoState_368_);
lean_inc(v_messages_367_);
lean_inc(v_traceState_366_);
lean_inc(v_auxDeclNGen_365_);
lean_inc(v_ngen_364_);
lean_inc(v_nextMacroScope_363_);
lean_inc(v_env_362_);
lean_dec(v___x_361_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_380_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = l_Lean_setDeclMeta(v_env_362_, v___x_357_);
v___x_374_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__2);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 5, v___x_374_);
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v___x_373_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_nextMacroScope_363_);
lean_ctor_set(v_reuseFailAlloc_379_, 2, v_ngen_364_);
lean_ctor_set(v_reuseFailAlloc_379_, 3, v_auxDeclNGen_365_);
lean_ctor_set(v_reuseFailAlloc_379_, 4, v_traceState_366_);
lean_ctor_set(v_reuseFailAlloc_379_, 5, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_379_, 6, v_messages_367_);
lean_ctor_set(v_reuseFailAlloc_379_, 7, v_infoState_368_);
lean_ctor_set(v_reuseFailAlloc_379_, 8, v_snapshotTasks_369_);
v___x_376_ = v_reuseFailAlloc_379_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_st_ref_set(v___y_360_, v___x_376_);
lean_inc(v_a_356_);
v___x_378_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(v_a_356_, v___y_359_, v___y_360_);
if (lean_obj_tag(v___x_378_) == 0)
{
lean_dec_ref(v___x_378_);
v_a_347_ = v___x_355_;
goto v___jp_346_;
}
else
{
return v___x_378_;
}
}
}
}
}
v___jp_346_:
{
size_t v___x_348_; size_t v___x_349_; 
v___x_348_ = ((size_t)1ULL);
v___x_349_ = lean_usize_add(v_i_341_, v___x_348_);
v_i_341_ = v___x_349_;
v_b_342_ = v_a_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___boxed(lean_object* v_as_401_, lean_object* v_sz_402_, lean_object* v_i_403_, lean_object* v_b_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_402_);
lean_dec(v_sz_402_);
v_i_boxed_409_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(v_as_401_, v_sz_boxed_408_, v_i_boxed_409_, v_b_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec_ref(v_as_401_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferMeta(lean_object* v_decls_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v___x_415_; lean_object* v_env_416_; lean_object* v___x_417_; uint8_t v_isModule_418_; 
v___x_415_ = lean_st_ref_get(v_a_413_);
v_env_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc_ref(v_env_416_);
lean_dec(v___x_415_);
v___x_417_ = l_Lean_Environment_header(v_env_416_);
lean_dec_ref(v_env_416_);
v_isModule_418_ = lean_ctor_get_uint8(v___x_417_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_417_);
if (v_isModule_418_ == 0)
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_box(0);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; size_t v_sz_422_; size_t v___x_423_; lean_object* v___x_424_; 
v___x_421_ = lean_box(0);
v_sz_422_ = lean_array_size(v_decls_411_);
v___x_423_ = ((size_t)0ULL);
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(v_decls_411_, v_sz_422_, v___x_423_, v___x_421_, v_a_412_, v_a_413_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; 
v_unused_432_ = lean_ctor_get(v___x_424_, 0);
lean_dec(v_unused_432_);
v___x_426_ = v___x_424_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_dec(v___x_424_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 0, v___x_421_);
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_421_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
else
{
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferMeta___boxed(lean_object* v_decls_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_IR_inferMeta(v_decls_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_decls_433_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* lean_eval_check_meta(lean_object* v_env_442_, lean_object* v_declName_443_){
_start:
{
uint8_t v___x_444_; uint8_t v___x_445_; uint8_t v___x_446_; 
lean_inc(v_declName_443_);
v___x_444_ = l_Lean_getIRPhases(v_env_442_, v_declName_443_);
v___x_445_ = 0;
v___x_446_ = l_Lean_instBEqIRPhases_beq(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec(v_declName_443_);
v___x_447_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0));
return v___x_447_;
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1));
v___x_449_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_443_, v___x_446_);
v___x_450_ = lean_string_append(v___x_448_, v___x_449_);
lean_dec_ref(v___x_449_);
v___x_451_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2));
v___x_452_ = lean_string_append(v___x_450_, v___x_451_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_unsigned_to_nat(3167601923u);
v___x_504_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_));
v___x_505_ = l_Lean_Name_num___override(v___x_504_, v___x_503_);
return v___x_505_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_));
v___x_508_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_509_ = l_Lean_Name_str___override(v___x_508_, v___x_507_);
return v___x_509_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_511_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_));
v___x_512_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_513_ = l_Lean_Name_str___override(v___x_512_, v___x_511_);
return v___x_513_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_unsigned_to_nat(2u);
v___x_515_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_516_ = l_Lean_Name_num___override(v___x_515_, v___x_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_518_; uint8_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_518_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__2___closed__6));
v___x_519_ = 0;
v___x_520_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_521_ = l_Lean_registerTraceClass(v___x_518_, v___x_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2____boxed(lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_();
return v_res_523_;
}
}
lean_object* runtime_initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_Meta(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
