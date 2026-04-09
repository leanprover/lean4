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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
uint8_t l_Lean_isDeclMeta(lean_object*, lean_object*);
lean_object* l_Lean_IR_findLocalDecl___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_setDeclMeta(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "inferMeta"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ir"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "compiler"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(25, 100, 103, 244, 164, 70, 204, 201)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(167, 96, 118, 160, 52, 15, 195, 103)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(178, 39, 14, 26, 17, 0, 113, 234)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Marking "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = " as meta because it is in `meta` closure"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13;
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_76_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__0);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_79_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_80_);
lean_ctor_set(v___x_81_, 2, v___x_80_);
lean_ctor_set(v___x_81_, 3, v___x_80_);
lean_ctor_set(v___x_81_, 4, v___x_79_);
lean_ctor_set(v___x_81_, 5, v___x_79_);
lean_ctor_set(v___x_81_, 6, v___x_79_);
lean_ctor_set(v___x_81_, 7, v___x_79_);
lean_ctor_set(v___x_81_, 8, v___x_79_);
lean_ctor_set(v___x_81_, 9, v___x_79_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_unsigned_to_nat(32u);
v___x_83_ = lean_mk_empty_array_with_capacity(v___x_82_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_85_ = ((size_t)5ULL);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_unsigned_to_nat(32u);
v___x_88_ = lean_mk_empty_array_with_capacity(v___x_87_);
v___x_89_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__3);
v___x_90_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_86_);
lean_ctor_set(v___x_90_, 3, v___x_86_);
lean_ctor_set_usize(v___x_90_, 4, v___x_85_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_box(1);
v___x_92_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__4);
v___x_93_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__1);
v___x_94_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_91_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(lean_object* v_msgData_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; lean_object* v_env_100_; lean_object* v_options_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_99_ = lean_st_ref_get(v___y_97_);
v_env_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc_ref(v_env_100_);
lean_dec(v___x_99_);
v_options_101_ = lean_ctor_get(v___y_96_, 2);
v___x_102_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__2);
v___x_103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_101_);
v___x_104_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_104_, 0, v_env_100_);
lean_ctor_set(v___x_104_, 1, v___x_102_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
lean_ctor_set(v___x_104_, 3, v_options_101_);
v___x_105_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_msgData_95_);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0___boxed(lean_object* v_msgData_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(v_msgData_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_111_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0(void){
_start:
{
lean_object* v___x_112_; double v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_float_of_nat(v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(lean_object* v_cls_117_, lean_object* v_msg_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_ref_122_; lean_object* v___x_123_; lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_168_; 
v_ref_122_ = lean_ctor_get(v___y_119_, 5);
v___x_123_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0_spec__0(v_msg_118_, v___y_119_, v___y_120_);
v_a_124_ = lean_ctor_get(v___x_123_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_168_ == 0)
{
v___x_126_ = v___x_123_;
v_isShared_127_ = v_isSharedCheck_168_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_123_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_168_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_128_; lean_object* v_traceState_129_; lean_object* v_env_130_; lean_object* v_nextMacroScope_131_; lean_object* v_ngen_132_; lean_object* v_auxDeclNGen_133_; lean_object* v_cache_134_; lean_object* v_messages_135_; lean_object* v_infoState_136_; lean_object* v_snapshotTasks_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_167_; 
v___x_128_ = lean_st_ref_take(v___y_120_);
v_traceState_129_ = lean_ctor_get(v___x_128_, 4);
v_env_130_ = lean_ctor_get(v___x_128_, 0);
v_nextMacroScope_131_ = lean_ctor_get(v___x_128_, 1);
v_ngen_132_ = lean_ctor_get(v___x_128_, 2);
v_auxDeclNGen_133_ = lean_ctor_get(v___x_128_, 3);
v_cache_134_ = lean_ctor_get(v___x_128_, 5);
v_messages_135_ = lean_ctor_get(v___x_128_, 6);
v_infoState_136_ = lean_ctor_get(v___x_128_, 7);
v_snapshotTasks_137_ = lean_ctor_get(v___x_128_, 8);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_167_ == 0)
{
v___x_139_ = v___x_128_;
v_isShared_140_ = v_isSharedCheck_167_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_snapshotTasks_137_);
lean_inc(v_infoState_136_);
lean_inc(v_messages_135_);
lean_inc(v_cache_134_);
lean_inc(v_traceState_129_);
lean_inc(v_auxDeclNGen_133_);
lean_inc(v_ngen_132_);
lean_inc(v_nextMacroScope_131_);
lean_inc(v_env_130_);
lean_dec(v___x_128_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_167_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
uint64_t v_tid_141_; lean_object* v_traces_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_166_; 
v_tid_141_ = lean_ctor_get_uint64(v_traceState_129_, sizeof(void*)*1);
v_traces_142_ = lean_ctor_get(v_traceState_129_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v_traceState_129_);
if (v_isSharedCheck_166_ == 0)
{
v___x_144_ = v_traceState_129_;
v_isShared_145_ = v_isSharedCheck_166_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_traces_142_);
lean_dec(v_traceState_129_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_166_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; double v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_146_ = lean_box(0);
v___x_147_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0, &l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__0);
v___x_148_ = 0;
v___x_149_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__1));
v___x_150_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_150_, 0, v_cls_117_);
lean_ctor_set(v___x_150_, 1, v___x_146_);
lean_ctor_set(v___x_150_, 2, v___x_149_);
lean_ctor_set_float(v___x_150_, sizeof(void*)*3, v___x_147_);
lean_ctor_set_float(v___x_150_, sizeof(void*)*3 + 8, v___x_147_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*3 + 16, v___x_148_);
v___x_151_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0___closed__2));
v___x_152_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set(v___x_152_, 1, v_a_124_);
lean_ctor_set(v___x_152_, 2, v___x_151_);
lean_inc(v_ref_122_);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v_ref_122_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = l_Lean_PersistentArray_push___redArg(v_traces_142_, v___x_153_);
if (v_isShared_145_ == 0)
{
lean_ctor_set(v___x_144_, 0, v___x_154_);
v___x_156_ = v___x_144_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_154_);
lean_ctor_set_uint64(v_reuseFailAlloc_165_, sizeof(void*)*1, v_tid_141_);
v___x_156_ = v_reuseFailAlloc_165_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_158_; 
if (v_isShared_140_ == 0)
{
lean_ctor_set(v___x_139_, 4, v___x_156_);
v___x_158_ = v___x_139_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_env_130_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_nextMacroScope_131_);
lean_ctor_set(v_reuseFailAlloc_164_, 2, v_ngen_132_);
lean_ctor_set(v_reuseFailAlloc_164_, 3, v_auxDeclNGen_133_);
lean_ctor_set(v_reuseFailAlloc_164_, 4, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_164_, 5, v_cache_134_);
lean_ctor_set(v_reuseFailAlloc_164_, 6, v_messages_135_);
lean_ctor_set(v_reuseFailAlloc_164_, 7, v_infoState_136_);
lean_ctor_set(v_reuseFailAlloc_164_, 8, v_snapshotTasks_137_);
v___x_158_ = v_reuseFailAlloc_164_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_162_; 
v___x_159_ = lean_st_ref_set(v___y_120_, v___x_158_);
v___x_160_ = lean_box(0);
if (v_isShared_127_ == 0)
{
lean_ctor_set(v___x_126_, 0, v___x_160_);
v___x_162_ = v___x_126_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_160_);
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
lean_object* v___x_175_; 
v___x_175_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_175_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__0);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__1);
v___x_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6));
v___x_191_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__8));
v___x_192_ = l_Lean_Name_append(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__10));
v___x_195_ = l_Lean_stringToMessageData(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__12));
v___x_198_ = l_Lean_stringToMessageData(v___x_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(lean_object* v_init_199_, lean_object* v_x_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
if (lean_obj_tag(v_x_200_) == 0)
{
lean_object* v_k_204_; lean_object* v_l_205_; lean_object* v_r_206_; lean_object* v___x_207_; 
v_k_204_ = lean_ctor_get(v_x_200_, 1);
lean_inc(v_k_204_);
v_l_205_ = lean_ctor_get(v_x_200_, 3);
lean_inc(v_l_205_);
v_r_206_ = lean_ctor_get(v_x_200_, 4);
lean_inc(v_r_206_);
lean_dec_ref(v_x_200_);
v___x_207_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v_init_199_, v_l_205_, v___y_201_, v___y_202_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v___x_208_; lean_object* v_env_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
lean_dec_ref(v___x_207_);
v___x_208_ = lean_st_ref_get(v___y_202_);
v_env_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc_ref(v_env_209_);
lean_dec(v___x_208_);
v___x_210_ = lean_box(0);
v___x_211_ = l_Lean_isDeclMeta(v_env_209_, v_k_204_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_IR_findLocalDecl___redArg(v_k_204_, v___y_202_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_a_213_; 
v_a_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_a_213_);
lean_dec_ref(v___x_212_);
if (lean_obj_tag(v_a_213_) == 1)
{
lean_object* v_val_214_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v_options_248_; uint8_t v_hasTrace_249_; 
v_val_214_ = lean_ctor_get(v_a_213_, 0);
lean_inc(v_val_214_);
lean_dec_ref(v_a_213_);
v_options_248_ = lean_ctor_get(v___y_201_, 2);
v_hasTrace_249_ = lean_ctor_get_uint8(v_options_248_, sizeof(void*)*1);
if (v_hasTrace_249_ == 0)
{
v___y_216_ = v___y_201_;
v___y_217_ = v___y_202_;
goto v___jp_215_;
}
else
{
lean_object* v_inheritedTraceOptions_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v_inheritedTraceOptions_250_ = lean_ctor_get(v___y_201_, 13);
v___x_251_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6));
v___x_252_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9);
v___x_253_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_250_, v_options_248_, v___x_252_);
if (v___x_253_ == 0)
{
v___y_216_ = v___y_201_;
v___y_217_ = v___y_202_;
goto v___jp_215_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_254_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11);
lean_inc(v_k_204_);
v___x_255_ = l_Lean_MessageData_ofName(v_k_204_);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__13);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(v___x_251_, v___x_258_, v___y_201_, v___y_202_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_dec_ref(v___x_259_);
v___y_216_ = v___y_201_;
v___y_217_ = v___y_202_;
goto v___jp_215_;
}
else
{
lean_object* v_a_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_267_; 
lean_dec(v_val_214_);
lean_dec(v_r_206_);
lean_dec(v_k_204_);
v_a_260_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_267_ == 0)
{
v___x_262_ = v___x_259_;
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_a_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_267_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_265_; 
if (v_isShared_263_ == 0)
{
v___x_265_ = v___x_262_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_a_260_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
return v___x_265_;
}
}
}
}
}
v___jp_215_:
{
lean_object* v___x_218_; lean_object* v_env_219_; lean_object* v_nextMacroScope_220_; lean_object* v_ngen_221_; lean_object* v_auxDeclNGen_222_; lean_object* v_traceState_223_; lean_object* v_messages_224_; lean_object* v_infoState_225_; lean_object* v_snapshotTasks_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_246_; 
v___x_218_ = lean_st_ref_take(v___y_217_);
v_env_219_ = lean_ctor_get(v___x_218_, 0);
v_nextMacroScope_220_ = lean_ctor_get(v___x_218_, 1);
v_ngen_221_ = lean_ctor_get(v___x_218_, 2);
v_auxDeclNGen_222_ = lean_ctor_get(v___x_218_, 3);
v_traceState_223_ = lean_ctor_get(v___x_218_, 4);
v_messages_224_ = lean_ctor_get(v___x_218_, 6);
v_infoState_225_ = lean_ctor_get(v___x_218_, 7);
v_snapshotTasks_226_ = lean_ctor_get(v___x_218_, 8);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v___x_218_, 5);
lean_dec(v_unused_247_);
v___x_228_ = v___x_218_;
v_isShared_229_ = v_isSharedCheck_246_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_snapshotTasks_226_);
lean_inc(v_infoState_225_);
lean_inc(v_messages_224_);
lean_inc(v_traceState_223_);
lean_inc(v_auxDeclNGen_222_);
lean_inc(v_ngen_221_);
lean_inc(v_nextMacroScope_220_);
lean_inc(v_env_219_);
lean_dec(v___x_218_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_246_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v___x_230_ = l_Lean_setDeclMeta(v_env_219_, v_k_204_);
v___x_231_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2);
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
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_nextMacroScope_220_);
lean_ctor_set(v_reuseFailAlloc_245_, 2, v_ngen_221_);
lean_ctor_set(v_reuseFailAlloc_245_, 3, v_auxDeclNGen_222_);
lean_ctor_set(v_reuseFailAlloc_245_, 4, v_traceState_223_);
lean_ctor_set(v_reuseFailAlloc_245_, 5, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_245_, 6, v_messages_224_);
lean_ctor_set(v_reuseFailAlloc_245_, 7, v_infoState_225_);
lean_ctor_set(v_reuseFailAlloc_245_, 8, v_snapshotTasks_226_);
v___x_233_ = v_reuseFailAlloc_245_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_st_ref_set(v___y_217_, v___x_233_);
v___x_235_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(v_val_214_, v___y_216_, v___y_217_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_dec_ref(v___x_235_);
v_init_199_ = v___x_210_;
v_x_200_ = v_r_206_;
goto _start;
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_r_206_);
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
lean_dec(v_a_213_);
lean_dec(v_k_204_);
v_init_199_ = v___x_210_;
v_x_200_ = v_r_206_;
goto _start;
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_r_206_);
lean_dec(v_k_204_);
v_a_269_ = lean_ctor_get(v___x_212_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_212_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_212_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_212_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_dec(v_k_204_);
v_init_199_ = v___x_210_;
v_x_200_ = v_r_206_;
goto _start;
}
}
else
{
lean_dec(v_r_206_);
lean_dec(v_k_204_);
return v___x_207_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v_init_199_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(lean_object* v_decl_280_, lean_object* v_a_281_, lean_object* v_a_282_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_collectUsedFDecls(v_decl_280_);
v___x_285_ = lean_box(0);
v___x_286_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v___x_285_, v___x_284_, v_a_281_, v_a_282_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_293_; 
v_isSharedCheck_293_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; 
v_unused_294_ = lean_ctor_get(v___x_286_, 0);
lean_dec(v_unused_294_);
v___x_288_ = v___x_286_;
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
else
{
lean_dec(v___x_286_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_293_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_291_; 
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_285_);
v___x_291_ = v___x_288_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_285_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
else
{
lean_object* v_a_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_302_; 
v_a_295_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_302_ == 0)
{
v___x_297_ = v___x_286_;
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_a_295_);
lean_dec(v___x_286_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_302_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_300_; 
if (v_isShared_298_ == 0)
{
v___x_300_ = v___x_297_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_a_295_);
v___x_300_ = v_reuseFailAlloc_301_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
return v___x_300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta___boxed(lean_object* v_decl_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(v_decl_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___boxed(lean_object* v_init_308_, lean_object* v_x_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1(v_init_308_, v_x_309_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
return v_res_313_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__0));
v___x_316_ = l_Lean_stringToMessageData(v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(lean_object* v_as_317_, size_t v_sz_318_, size_t v_i_319_, lean_object* v_b_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_a_325_; uint8_t v___x_329_; 
v___x_329_ = lean_usize_dec_lt(v_i_319_, v_sz_318_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_b_320_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; lean_object* v_env_332_; lean_object* v___x_333_; lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v___y_337_; lean_object* v___y_338_; uint8_t v___x_360_; 
v___x_331_ = lean_st_ref_get(v___y_322_);
v_env_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc_ref(v_env_332_);
lean_dec(v___x_331_);
v___x_333_ = lean_box(0);
v_a_334_ = lean_array_uget_borrowed(v_as_317_, v_i_319_);
v___x_335_ = l_Lean_IR_Decl_name(v_a_334_);
lean_inc(v___x_335_);
v___x_360_ = l_Lean_isMarkedMeta(v_env_332_, v___x_335_);
if (v___x_360_ == 0)
{
lean_dec(v___x_335_);
v_a_325_ = v___x_333_;
goto v___jp_324_;
}
else
{
lean_object* v_options_361_; uint8_t v_hasTrace_362_; 
v_options_361_ = lean_ctor_get(v___y_321_, 2);
v_hasTrace_362_ = lean_ctor_get_uint8(v_options_361_, sizeof(void*)*1);
if (v_hasTrace_362_ == 0)
{
v___y_337_ = v___y_321_;
v___y_338_ = v___y_322_;
goto v___jp_336_;
}
else
{
lean_object* v_inheritedTraceOptions_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_inheritedTraceOptions_363_ = lean_ctor_get(v___y_321_, 13);
v___x_364_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6));
v___x_365_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__9);
v___x_366_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_363_, v_options_361_, v___x_365_);
if (v___x_366_ == 0)
{
v___y_337_ = v___y_321_;
v___y_338_ = v___y_322_;
goto v___jp_336_;
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_367_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__11);
lean_inc(v___x_335_);
v___x_368_ = l_Lean_MessageData_ofName(v___x_335_);
v___x_369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___closed__1);
v___x_371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = l_Lean_addTrace___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__0(v___x_364_, v___x_371_, v___y_321_, v___y_322_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_dec_ref(v___x_372_);
v___y_337_ = v___y_321_;
v___y_338_ = v___y_322_;
goto v___jp_336_;
}
else
{
lean_dec(v___x_335_);
return v___x_372_;
}
}
}
}
v___jp_336_:
{
lean_object* v___x_339_; lean_object* v_env_340_; lean_object* v_nextMacroScope_341_; lean_object* v_ngen_342_; lean_object* v_auxDeclNGen_343_; lean_object* v_traceState_344_; lean_object* v_messages_345_; lean_object* v_infoState_346_; lean_object* v_snapshotTasks_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_358_; 
v___x_339_ = lean_st_ref_take(v___y_338_);
v_env_340_ = lean_ctor_get(v___x_339_, 0);
v_nextMacroScope_341_ = lean_ctor_get(v___x_339_, 1);
v_ngen_342_ = lean_ctor_get(v___x_339_, 2);
v_auxDeclNGen_343_ = lean_ctor_get(v___x_339_, 3);
v_traceState_344_ = lean_ctor_get(v___x_339_, 4);
v_messages_345_ = lean_ctor_get(v___x_339_, 6);
v_infoState_346_ = lean_ctor_get(v___x_339_, 7);
v_snapshotTasks_347_ = lean_ctor_get(v___x_339_, 8);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v___x_339_, 5);
lean_dec(v_unused_359_);
v___x_349_ = v___x_339_;
v_isShared_350_ = v_isSharedCheck_358_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_snapshotTasks_347_);
lean_inc(v_infoState_346_);
lean_inc(v_messages_345_);
lean_inc(v_traceState_344_);
lean_inc(v_auxDeclNGen_343_);
lean_inc(v_ngen_342_);
lean_inc(v_nextMacroScope_341_);
lean_inc(v_env_340_);
lean_dec(v___x_339_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_358_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_351_ = l_Lean_setDeclMeta(v_env_340_, v___x_335_);
v___x_352_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2, &l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__2);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 5, v___x_352_);
lean_ctor_set(v___x_349_, 0, v___x_351_);
v___x_354_ = v___x_349_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_nextMacroScope_341_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_ngen_342_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_auxDeclNGen_343_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_traceState_344_);
lean_ctor_set(v_reuseFailAlloc_357_, 5, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_357_, 6, v_messages_345_);
lean_ctor_set(v_reuseFailAlloc_357_, 7, v_infoState_346_);
lean_ctor_set(v_reuseFailAlloc_357_, 8, v_snapshotTasks_347_);
v___x_354_ = v_reuseFailAlloc_357_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = lean_st_ref_set(v___y_338_, v___x_354_);
lean_inc(v_a_334_);
v___x_356_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta(v_a_334_, v___y_337_, v___y_338_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_dec_ref(v___x_356_);
v_a_325_ = v___x_333_;
goto v___jp_324_;
}
else
{
return v___x_356_;
}
}
}
}
}
v___jp_324_:
{
size_t v___x_326_; size_t v___x_327_; 
v___x_326_ = ((size_t)1ULL);
v___x_327_ = lean_usize_add(v_i_319_, v___x_326_);
v_i_319_ = v___x_327_;
v_b_320_ = v_a_325_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0___boxed(lean_object* v_as_373_, lean_object* v_sz_374_, lean_object* v_i_375_, lean_object* v_b_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
size_t v_sz_boxed_380_; size_t v_i_boxed_381_; lean_object* v_res_382_; 
v_sz_boxed_380_ = lean_unbox_usize(v_sz_374_);
lean_dec(v_sz_374_);
v_i_boxed_381_ = lean_unbox_usize(v_i_375_);
lean_dec(v_i_375_);
v_res_382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(v_as_373_, v_sz_boxed_380_, v_i_boxed_381_, v_b_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec_ref(v_as_373_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferMeta(lean_object* v_decls_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v___x_387_; lean_object* v_env_388_; lean_object* v___x_389_; uint8_t v_isModule_390_; 
v___x_387_ = lean_st_ref_get(v_a_385_);
v_env_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_ref(v_env_388_);
lean_dec(v___x_387_);
v___x_389_ = l_Lean_Environment_header(v_env_388_);
lean_dec_ref(v_env_388_);
v_isModule_390_ = lean_ctor_get_uint8(v___x_389_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_389_);
if (v_isModule_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; size_t v_sz_394_; size_t v___x_395_; lean_object* v___x_396_; 
v___x_393_ = lean_box(0);
v_sz_394_ = lean_array_size(v_decls_383_);
v___x_395_ = ((size_t)0ULL);
v___x_396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_inferMeta_spec__0(v_decls_383_, v_sz_394_, v___x_395_, v___x_393_, v_a_384_, v_a_385_);
if (lean_obj_tag(v___x_396_) == 0)
{
lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_403_; 
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_403_ == 0)
{
lean_object* v_unused_404_; 
v_unused_404_ = lean_ctor_get(v___x_396_, 0);
lean_dec(v_unused_404_);
v___x_398_ = v___x_396_;
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
else
{
lean_dec(v___x_396_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_403_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_401_; 
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_393_);
v___x_401_ = v___x_398_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_393_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_inferMeta___boxed(lean_object* v_decls_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_IR_inferMeta(v_decls_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
lean_dec_ref(v_decls_405_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* lean_eval_check_meta(lean_object* v_env_414_, lean_object* v_declName_415_){
_start:
{
uint8_t v___x_416_; uint8_t v___x_417_; uint8_t v___x_418_; 
lean_inc(v_declName_415_);
v___x_416_ = l_Lean_getIRPhases(v_env_414_, v_declName_415_);
v___x_417_ = 0;
v___x_418_ = l_Lean_instBEqIRPhases_beq(v___x_416_, v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
lean_dec(v_declName_415_);
v___x_419_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__0));
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_420_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__1));
v___x_421_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_415_, v___x_418_);
v___x_422_ = lean_string_append(v___x_420_, v___x_421_);
lean_dec_ref(v___x_421_);
v___x_423_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_evalCheckMeta___closed__2));
v___x_424_ = lean_string_append(v___x_422_, v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = lean_unsigned_to_nat(3167601923u);
v___x_476_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__20_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_));
v___x_477_ = l_Lean_Name_num___override(v___x_476_, v___x_475_);
return v___x_477_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__22_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_));
v___x_480_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__21_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_481_ = l_Lean_Name_str___override(v___x_480_, v___x_479_);
return v___x_481_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_483_ = ((lean_object*)(l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__24_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_));
v___x_484_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__23_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_485_ = l_Lean_Name_str___override(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_unsigned_to_nat(2u);
v___x_487_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__25_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_488_ = l_Lean_Name_num___override(v___x_487_, v___x_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_490_; uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_490_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_IR_Meta_0__Lean_IR_setClosureMeta_spec__1___closed__6));
v___x_491_ = 0;
v___x_492_ = lean_obj_once(&l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_, &l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn___closed__26_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_);
v___x_493_ = l_Lean_registerTraceClass(v___x_490_, v___x_491_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2____boxed(lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Compiler_IR_Meta_0__Lean_IR_initFn_00___x40_Lean_Compiler_IR_Meta_3167601923____hygCtx___hyg_2_();
return v_res_495_;
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
