// Lean compiler output
// Module: Lean.Linter.Init
// Imports: public import Lean.MonadEnv public import Lean.EnvExtension import Init.Data.Function
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logWarningAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_instEmptyCollectionLinterSets___aux__1;
LEAN_EXPORT lean_object* l_Lean_Linter_instEmptyCollectionLinterSets;
LEAN_EXPORT lean_object* l_Lean_Linter_instInhabitedLinterSets___aux__1;
LEAN_EXPORT lean_object* l_Lean_Linter_instInhabitedLinterSets;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSetEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0 = (const lean_object*)&l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0_value;
static const lean_ctor_object l_Lean_Linter_instInhabitedLinterSetsState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0_value)}};
static const lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default___closed__1 = (const lean_object*)&l_Lean_Linter_instInhabitedLinterSetsState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default = (const lean_object*)&l_Lean_Linter_instInhabitedLinterSetsState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_instInhabitedLinterSetsState = (const lean_object*)&l_Lean_Linter_instInhabitedLinterSetsState_default___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_builtinLinterSetsRef;
LEAN_EXPORT lean_object* l_Lean_Linter_addBuiltinLinterSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_addBuiltinLinterSet___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "linterSetsExt"};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 168, 78, 71, 242, 123, 0, 76)}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linterSetsExt;
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 180, 119, 173, 178, 109, 102, 175)}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "enable all linters"};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 167, 123, 44, 188, 59, 15, 50)}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_all;
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 170, .m_capacity = 170, .m_length = 167, .m_data = "enables the set of extra linters — linters that are turned off by default and only available via `lake lint`. An extra linter early-returns unless this option is true."};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(58, 197, 127, 54, 42, 254, 83, 167)}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_extra;
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "coreInternal"};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(216, 202, 150, 38, 196, 187, 132, 57)}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 159, .m_capacity = 159, .m_length = 156, .m_data = "enables the set of core-internal linters — linters that enforce conventions of the Lean repository itself and are not intended for use by non-core projects."};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(195, 14, 14, 18, 112, 30, 27, 197)}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_coreInternal;
static const lean_array_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_envLinterOptionsRef;
LEAN_EXPORT lean_object* l_Lean_Linter_addEnvLinterOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_addEnvLinterOption___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterAll(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_isLinterEnabledByOptions___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_linterMessageTag___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_linter"};
static const lean_object* l_Lean_Linter_linterMessageTag___closed__0 = (const lean_object*)&l_Lean_Linter_linterMessageTag___closed__0_value;
static const lean_ctor_object l_Lean_Linter_linterMessageTag___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_linterMessageTag___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_linterMessageTag___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_linterMessageTag___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_linterMessageTag___closed__1_value_aux_1),((lean_object*)&l_Lean_Linter_linterMessageTag___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 5, 234, 242, 158, 66, 116, 160)}};
static const lean_object* l_Lean_Linter_linterMessageTag___closed__1 = (const lean_object*)&l_Lean_Linter_linterMessageTag___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_linterMessageTag = (const lean_object*)&l_Lean_Linter_linterMessageTag___closed__1_value;
static const lean_string_object l_Lean_Linter_logLint___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___redArg___closed__1;
static const lean_string_object l_Lean_Linter_logLint___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___redArg___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_MessageData_isLinterMessage___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_isLinterMessage___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_MessageData_isLinterMessage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_isLinterMessage___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_MessageData_isLinterMessage___closed__0 = (const lean_object*)&l_Lean_MessageData_isLinterMessage___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_MessageData_isLinterMessage(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_isLinterMessage___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "envLinterSnapshotExt"};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 41, 149, 210, 14, 67, 245, 121)}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_envLinterSnapshotExt;
LEAN_EXPORT lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Linter_instEmptyCollectionLinterSets___aux__1(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(1);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Linter_instEmptyCollectionLinterSets(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(1);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Linter_instInhabitedLinterSets___aux__1(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(1);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Linter_instInhabitedLinterSets(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_box(1);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(lean_object* v_t_5_, lean_object* v_k_6_, lean_object* v_fallback_7_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_k_8_; lean_object* v_v_9_; lean_object* v_l_10_; lean_object* v_r_11_; uint8_t v___x_12_; 
v_k_8_ = lean_ctor_get(v_t_5_, 1);
v_v_9_ = lean_ctor_get(v_t_5_, 2);
v_l_10_ = lean_ctor_get(v_t_5_, 3);
v_r_11_ = lean_ctor_get(v_t_5_, 4);
v___x_12_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6_, v_k_8_);
switch(v___x_12_)
{
case 0:
{
v_t_5_ = v_l_10_;
goto _start;
}
case 1:
{
lean_inc(v_v_9_);
return v_v_9_;
}
default: 
{
v_t_5_ = v_r_11_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_7_);
return v_fallback_7_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg___boxed(lean_object* v_t_15_, lean_object* v_k_16_, lean_object* v_fallback_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_t_15_, v_k_16_, v_fallback_17_);
lean_dec(v_fallback_17_);
lean_dec(v_k_16_);
lean_dec(v_t_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(lean_object* v_setName_21_, lean_object* v_init_22_, lean_object* v_x_23_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
lean_object* v_k_24_; lean_object* v_l_25_; lean_object* v_r_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v_k_24_ = lean_ctor_get(v_x_23_, 1);
lean_inc(v_k_24_);
v_l_25_ = lean_ctor_get(v_x_23_, 3);
lean_inc(v_l_25_);
v_r_26_ = lean_ctor_get(v_x_23_, 4);
lean_inc(v_r_26_);
lean_dec_ref_known(v_x_23_, 5);
lean_inc_n(v_setName_21_, 2);
v___x_27_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_setName_21_, v_init_22_, v_l_25_);
v___x_28_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_29_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v___x_27_, v_k_24_, v___x_28_);
v___x_30_ = lean_array_push(v___x_29_, v_setName_21_);
v___x_31_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_24_, v___x_30_, v___x_27_);
v_init_22_ = v___x_31_;
v_x_23_ = v_r_26_;
goto _start;
}
else
{
lean_dec(v_setName_21_);
return v_init_22_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSetEntry(lean_object* v_map_33_, lean_object* v_setName_34_, lean_object* v_options_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_setName_34_, v_map_33_, v_options_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0(lean_object* v_00_u03b4_37_, lean_object* v_t_38_, lean_object* v_k_39_, lean_object* v_fallback_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_t_38_, v_k_39_, v_fallback_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___boxed(lean_object* v_00_u03b4_42_, lean_object* v_t_43_, lean_object* v_k_44_, lean_object* v_fallback_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0(v_00_u03b4_42_, v_t_43_, v_k_44_, v_fallback_45_);
lean_dec(v_fallback_45_);
lean_dec(v_k_44_);
lean_dec(v_t_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1(lean_object* v_setName_47_, lean_object* v_init_48_, lean_object* v_t_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_setName_47_, v_init_48_, v_t_49_);
return v___x_50_;
}
}
lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_60_ = lean_st_mk_ref(v___x_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_62_;
v_res_62_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2_();
stack->m_obj
 = v_res_62_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2____boxed(lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2_();
return v_res_64_;
}
}
lean_object* l_Lean_Linter_addBuiltinLinterSet(lean_object* v_setName_65_, lean_object* v_linterNames_66_){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_68_ = l_Lean_Linter_builtinLinterSetsRef;
v___x_69_ = lean_st_ref_take(v___x_68_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v_setName_65_);
lean_ctor_set(v___x_70_, 1, v_linterNames_66_);
v___x_71_ = lean_array_push(v___x_69_, v___x_70_);
v___x_72_ = lean_st_ref_put(v___x_68_, v___x_71_);
v___x_73_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_73_, 0, v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT void l_Lean_Linter_addBuiltinLinterSet_0interp(lean_interpreter_value* stack)
{
lean_object* v_setName_65_ = stack[0].m_obj;
lean_object* v_linterNames_66_ = stack[1].m_obj;
lean_object* v_res_74_;
v_res_74_ = l_Lean_Linter_addBuiltinLinterSet(v_setName_65_, v_linterNames_66_);
stack->m_obj
 = v_res_74_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_addBuiltinLinterSet___boxed(lean_object* v_setName_75_, lean_object* v_linterNames_76_, lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l_Lean_Linter_addBuiltinLinterSet(v_setName_75_, v_linterNames_76_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v_st_79_, lean_object* v_x_80_){
_start:
{
lean_object* v_fst_81_; lean_object* v_snd_82_; lean_object* v_merged_83_; lean_object* v_localEntries_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_93_; 
v_fst_81_ = lean_ctor_get(v_x_80_, 0);
v_snd_82_ = lean_ctor_get(v_x_80_, 1);
v_merged_83_ = lean_ctor_get(v_st_79_, 0);
v_localEntries_84_ = lean_ctor_get(v_st_79_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v_st_79_);
if (v_isSharedCheck_93_ == 0)
{
v___x_86_ = v_st_79_;
v_isShared_87_ = v_isSharedCheck_93_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_localEntries_84_);
lean_inc(v_merged_83_);
lean_dec(v_st_79_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_93_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
lean_inc(v_snd_82_);
lean_inc(v_fst_81_);
v___x_88_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_81_, v_merged_83_, v_snd_82_);
v___x_89_ = lean_array_push(v_localEntries_84_, v_x_80_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 1, v___x_89_);
lean_ctor_set(v___x_86_, 0, v___x_88_);
v___x_91_ = v___x_86_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v_x_94_, lean_object* v_s_95_){
_start:
{
lean_object* v_localEntries_96_; lean_object* v___x_97_; 
v_localEntries_96_ = lean_ctor_get(v_s_95_, 1);
lean_inc_ref_n(v_localEntries_96_, 3);
v___x_97_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_97_, 0, v_localEntries_96_);
lean_ctor_set(v___x_97_, 1, v_localEntries_96_);
lean_ctor_set(v___x_97_, 2, v_localEntries_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v_x_98_, lean_object* v_s_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v_x_98_, v_s_99_);
lean_dec_ref(v_s_99_);
lean_dec_ref(v_x_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v_x_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(0);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v_x_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v_x_103_);
lean_dec_ref(v_x_103_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v_st_105_){
_start:
{
lean_object* v_localEntries_106_; 
v_localEntries_106_ = lean_ctor_get(v_st_105_, 1);
lean_inc_ref(v_localEntries_106_);
return v_localEntries_106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v_st_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v_st_107_);
lean_dec_ref(v_st_107_);
return v_res_108_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(lean_object* v_as_109_, size_t v_i_110_, size_t v_stop_111_, lean_object* v_b_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = lean_usize_dec_eq(v_i_110_, v_stop_111_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v_fst_115_; lean_object* v_snd_116_; lean_object* v___x_117_; size_t v___x_118_; size_t v___x_119_; 
v___x_114_ = lean_array_uget_borrowed(v_as_109_, v_i_110_);
v_fst_115_ = lean_ctor_get(v___x_114_, 0);
v_snd_116_ = lean_ctor_get(v___x_114_, 1);
lean_inc(v_snd_116_);
lean_inc(v_fst_115_);
v___x_117_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_115_, v_b_112_, v_snd_116_);
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_add(v_i_110_, v___x_118_);
v_i_110_ = v___x_119_;
v_b_112_ = v___x_117_;
goto _start;
}
else
{
return v_b_112_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_109_ = stack[0].m_obj;
size_t v_i_110_ = stack[1].m_num;
size_t v_stop_111_ = stack[2].m_num;
lean_object* v_b_112_ = stack[3].m_obj;
lean_object* v_res_121_;
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v_as_109_, v_i_110_, v_stop_111_, v_b_112_);
stack->m_obj
 = v_res_121_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2___boxed(lean_object* v_as_122_, lean_object* v_i_123_, lean_object* v_stop_124_, lean_object* v_b_125_){
_start:
{
size_t v_i_boxed_126_; size_t v_stop_boxed_127_; lean_object* v_res_128_; 
v_i_boxed_126_ = lean_unbox_usize(v_i_123_);
lean_dec(v_i_123_);
v_stop_boxed_127_ = lean_unbox_usize(v_stop_124_);
lean_dec(v_stop_124_);
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v_as_122_, v_i_boxed_126_, v_stop_boxed_127_, v_b_125_);
lean_dec_ref(v_as_122_);
return v_res_128_;
}
}
lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v___x_129_){
_start:
{
lean_object* v___x_131_; lean_object* v___y_133_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_131_ = lean_st_ref_get(v___x_129_);
v___x_137_ = lean_box(1);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_array_get_size(v___x_131_);
v___x_140_ = lean_nat_dec_lt(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_dec(v___x_131_);
v___y_133_ = v___x_137_;
goto v___jp_132_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = lean_nat_dec_le(v___x_139_, v___x_139_);
if (v___x_141_ == 0)
{
if (v___x_140_ == 0)
{
lean_dec(v___x_131_);
v___y_133_ = v___x_137_;
goto v___jp_132_;
}
else
{
size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; 
v___x_142_ = ((size_t)0ULL);
v___x_143_ = lean_usize_of_nat(v___x_139_);
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v___x_131_, v___x_142_, v___x_143_, v___x_137_);
lean_dec(v___x_131_);
v___y_133_ = v___x_144_;
goto v___jp_132_;
}
}
else
{
size_t v___x_145_; size_t v___x_146_; lean_object* v___x_147_; 
v___x_145_ = ((size_t)0ULL);
v___x_146_ = lean_usize_of_nat(v___x_139_);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v___x_131_, v___x_145_, v___x_146_, v___x_137_);
lean_dec(v___x_131_);
v___y_133_ = v___x_147_;
goto v___jp_132_;
}
}
v___jp_132_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___y_133_);
lean_ctor_set(v___x_135_, 1, v___x_134_);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_129_ = stack[0].m_obj;
lean_object* v_res_148_;
v_res_148_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v___x_129_);
stack->m_obj
 = v_res_148_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v___x_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v___x_149_);
lean_dec(v___x_149_);
return v_res_151_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(lean_object* v_as_152_, size_t v_i_153_, size_t v_stop_154_, lean_object* v_b_155_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = lean_usize_dec_eq(v_i_153_, v_stop_154_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v_fst_158_; lean_object* v_snd_159_; lean_object* v___x_160_; size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; 
v___x_157_ = lean_array_uget_borrowed(v_as_152_, v_i_153_);
v_fst_158_ = lean_ctor_get(v___x_157_, 0);
v_snd_159_ = lean_ctor_get(v___x_157_, 1);
lean_inc(v_snd_159_);
lean_inc(v_fst_158_);
v___x_160_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_158_, v_b_155_, v_snd_159_);
v___x_161_ = ((size_t)1ULL);
v___x_162_ = lean_usize_add(v_i_153_, v___x_161_);
v___x_163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v_as_152_, v___x_162_, v_stop_154_, v___x_160_);
return v___x_163_;
}
else
{
return v_b_155_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_152_ = stack[0].m_obj;
size_t v_i_153_ = stack[1].m_num;
size_t v_stop_154_ = stack[2].m_num;
lean_object* v_b_155_ = stack[3].m_obj;
lean_object* v_res_164_;
v_res_164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v_as_152_, v_i_153_, v_stop_154_, v_b_155_);
stack->m_obj
 = v_res_164_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_165_, lean_object* v_i_166_, lean_object* v_stop_167_, lean_object* v_b_168_){
_start:
{
size_t v_i_boxed_169_; size_t v_stop_boxed_170_; lean_object* v_res_171_; 
v_i_boxed_169_ = lean_unbox_usize(v_i_166_);
lean_dec(v_i_166_);
v_stop_boxed_170_ = lean_unbox_usize(v_stop_167_);
lean_dec(v_stop_167_);
v_res_171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v_as_165_, v_i_boxed_169_, v_stop_boxed_170_, v_b_168_);
lean_dec_ref(v_as_165_);
return v_res_171_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(lean_object* v_as_172_, size_t v_i_173_, size_t v_stop_174_, lean_object* v_b_175_){
_start:
{
lean_object* v___y_177_; uint8_t v___x_181_; 
v___x_181_ = lean_usize_dec_eq(v_i_173_, v_stop_174_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_array_uget_borrowed(v_as_172_, v_i_173_);
v___x_184_ = lean_array_get_size(v___x_183_);
v___x_185_ = lean_nat_dec_lt(v___x_182_, v___x_184_);
if (v___x_185_ == 0)
{
v___y_177_ = v_b_175_;
goto v___jp_176_;
}
else
{
uint8_t v___x_186_; 
v___x_186_ = lean_nat_dec_le(v___x_184_, v___x_184_);
if (v___x_186_ == 0)
{
if (v___x_185_ == 0)
{
v___y_177_ = v_b_175_;
goto v___jp_176_;
}
else
{
size_t v___x_187_; size_t v___x_188_; lean_object* v___x_189_; 
v___x_187_ = ((size_t)0ULL);
v___x_188_ = lean_usize_of_nat(v___x_184_);
v___x_189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v___x_183_, v___x_187_, v___x_188_, v_b_175_);
v___y_177_ = v___x_189_;
goto v___jp_176_;
}
}
else
{
size_t v___x_190_; size_t v___x_191_; lean_object* v___x_192_; 
v___x_190_ = ((size_t)0ULL);
v___x_191_ = lean_usize_of_nat(v___x_184_);
v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v___x_183_, v___x_190_, v___x_191_, v_b_175_);
v___y_177_ = v___x_192_;
goto v___jp_176_;
}
}
}
else
{
return v_b_175_;
}
v___jp_176_:
{
size_t v___x_178_; size_t v___x_179_; 
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_173_, v___x_178_);
v_i_173_ = v___x_179_;
v_b_175_ = v___y_177_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_172_ = stack[0].m_obj;
size_t v_i_173_ = stack[1].m_num;
size_t v_stop_174_ = stack[2].m_num;
lean_object* v_b_175_ = stack[3].m_obj;
lean_object* v_res_193_;
v_res_193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(v_as_172_, v_i_173_, v_stop_174_, v_b_175_);
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_194_, lean_object* v_i_195_, lean_object* v_stop_196_, lean_object* v_b_197_){
_start:
{
size_t v_i_boxed_198_; size_t v_stop_boxed_199_; lean_object* v_res_200_; 
v_i_boxed_198_ = lean_unbox_usize(v_i_195_);
lean_dec(v_i_195_);
v_stop_boxed_199_ = lean_unbox_usize(v_stop_196_);
lean_dec(v_stop_196_);
v_res_200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(v_as_194_, v_i_boxed_198_, v_stop_boxed_199_, v_b_197_);
lean_dec_ref(v_as_194_);
return v_res_200_;
}
}
lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v___x_201_, lean_object* v_ess_202_, lean_object* v___y_203_){
_start:
{
lean_object* v___x_205_; lean_object* v___y_207_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___y_214_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_205_ = lean_st_ref_get(v___x_201_);
v___x_211_ = lean_box(1);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_array_get_size(v___x_205_);
v___x_225_ = lean_nat_dec_lt(v___x_212_, v___x_224_);
if (v___x_225_ == 0)
{
lean_dec(v___x_205_);
v___y_214_ = v___x_211_;
goto v___jp_213_;
}
else
{
uint8_t v___x_226_; 
v___x_226_ = lean_nat_dec_le(v___x_224_, v___x_224_);
if (v___x_226_ == 0)
{
if (v___x_225_ == 0)
{
lean_dec(v___x_205_);
v___y_214_ = v___x_211_;
goto v___jp_213_;
}
else
{
size_t v___x_227_; size_t v___x_228_; lean_object* v___x_229_; 
v___x_227_ = ((size_t)0ULL);
v___x_228_ = lean_usize_of_nat(v___x_224_);
v___x_229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v___x_205_, v___x_227_, v___x_228_, v___x_211_);
lean_dec(v___x_205_);
v___y_214_ = v___x_229_;
goto v___jp_213_;
}
}
else
{
size_t v___x_230_; size_t v___x_231_; lean_object* v___x_232_; 
v___x_230_ = ((size_t)0ULL);
v___x_231_ = lean_usize_of_nat(v___x_224_);
v___x_232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v___x_205_, v___x_230_, v___x_231_, v___x_211_);
lean_dec(v___x_205_);
v___y_214_ = v___x_232_;
goto v___jp_213_;
}
}
v___jp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_208_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___y_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
v___jp_213_:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_array_get_size(v_ess_202_);
v___x_216_ = lean_nat_dec_lt(v___x_212_, v___x_215_);
if (v___x_216_ == 0)
{
v___y_207_ = v___y_214_;
goto v___jp_206_;
}
else
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_le(v___x_215_, v___x_215_);
if (v___x_217_ == 0)
{
if (v___x_216_ == 0)
{
v___y_207_ = v___y_214_;
goto v___jp_206_;
}
else
{
size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_215_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(v_ess_202_, v___x_218_, v___x_219_, v___y_214_);
v___y_207_ = v___x_220_;
goto v___jp_206_;
}
}
else
{
size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((size_t)0ULL);
v___x_222_ = lean_usize_of_nat(v___x_215_);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(v_ess_202_, v___x_221_, v___x_222_, v___y_214_);
v___y_207_ = v___x_223_;
goto v___jp_206_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_201_ = stack[0].m_obj;
lean_object* v_ess_202_ = stack[1].m_obj;
lean_object* v___y_203_ = stack[2].m_obj;
lean_object* v_res_233_;
v_res_233_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v___x_201_, v_ess_202_, v___y_203_);
stack->m_obj
 = v_res_233_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v___x_234_, lean_object* v_ess_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v___x_234_, v_ess_235_, v___y_236_);
lean_dec_ref(v___y_236_);
lean_dec_ref(v_ess_235_);
lean_dec(v___x_234_);
return v_res_238_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_250_; lean_object* v___f_251_; 
v___x_250_ = l_Lean_Linter_builtinLinterSetsRef;
v___f_251_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_251_, 0, v___x_250_);
return v___f_251_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_252_; lean_object* v___f_253_; 
v___x_252_ = l_Lean_Linter_builtinLinterSetsRef;
v___f_253_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_253_, 0, v___x_252_);
return v___f_253_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___f_257_; lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___f_260_; lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_254_ = 0;
v___x_255_ = lean_box(0);
v___x_256_ = lean_box(2);
v___f_257_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_258_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_259_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_260_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___f_261_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_262_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___x_263_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___f_261_);
lean_ctor_set(v___x_263_, 2, v___f_260_);
lean_ctor_set(v___x_263_, 3, v___f_259_);
lean_ctor_set(v___x_263_, 4, v___f_258_);
lean_ctor_set(v___x_263_, 5, v___f_257_);
lean_ctor_set(v___x_263_, 6, v___x_256_);
lean_ctor_set(v___x_263_, 7, v___x_255_);
lean_ctor_set_uint8(v___x_263_, sizeof(void*)*8, v___x_254_);
lean_ctor_set_uint8(v___x_263_, sizeof(void*)*8 + 1, v___x_254_);
return v___x_263_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___f_264_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___x_265_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v___f_264_);
return v___x_266_;
}
}
lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_269_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_270_;
v_res_270_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_();
stack->m_obj
 = v_res_270_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v_a_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_();
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg(lean_object* v_inst_273_, lean_object* v_o_274_, lean_object* v_k_275_, lean_object* v_defVal_276_){
_start:
{
lean_object* v_toOptions_277_; lean_object* v_map_278_; lean_object* v_ofDataValue_x3f_279_; lean_object* v___x_280_; 
v_toOptions_277_ = lean_ctor_get(v_o_274_, 0);
v_map_278_ = lean_ctor_get(v_toOptions_277_, 0);
v_ofDataValue_x3f_279_ = lean_ctor_get(v_inst_273_, 1);
lean_inc_ref(v_ofDataValue_x3f_279_);
lean_dec_ref(v_inst_273_);
v___x_280_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_278_, v_k_275_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_279_);
lean_inc(v_defVal_276_);
return v_defVal_276_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_282_; 
v_val_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_val_281_);
lean_dec_ref_known(v___x_280_, 1);
v___x_282_ = lean_apply_1(v_ofDataValue_x3f_279_, v_val_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_inc(v_defVal_276_);
return v_defVal_276_;
}
else
{
lean_object* v_val_283_; 
v_val_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_val_283_);
lean_dec_ref_known(v___x_282_, 1);
return v_val_283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg___boxed(lean_object* v_inst_284_, lean_object* v_o_285_, lean_object* v_k_286_, lean_object* v_defVal_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Linter_LinterOptions_get___redArg(v_inst_284_, v_o_285_, v_k_286_, v_defVal_287_);
lean_dec(v_defVal_287_);
lean_dec(v_k_286_);
lean_dec_ref(v_o_285_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get(lean_object* v_00_u03b1_289_, lean_object* v_inst_290_, lean_object* v_o_291_, lean_object* v_k_292_, lean_object* v_defVal_293_){
_start:
{
lean_object* v___x_294_; 
v___x_294_ = l_Lean_Linter_LinterOptions_get___redArg(v_inst_290_, v_o_291_, v_k_292_, v_defVal_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___boxed(lean_object* v_00_u03b1_295_, lean_object* v_inst_296_, lean_object* v_o_297_, lean_object* v_k_298_, lean_object* v_defVal_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Linter_LinterOptions_get(v_00_u03b1_295_, v_inst_296_, v_o_297_, v_k_298_, v_defVal_299_);
lean_dec(v_defVal_299_);
lean_dec(v_k_298_);
lean_dec_ref(v_o_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg(lean_object* v_inst_301_, lean_object* v_o_302_, lean_object* v_k_303_){
_start:
{
lean_object* v_toOptions_304_; lean_object* v_map_305_; lean_object* v_ofDataValue_x3f_306_; lean_object* v___x_307_; 
v_toOptions_304_ = lean_ctor_get(v_o_302_, 0);
v_map_305_ = lean_ctor_get(v_toOptions_304_, 0);
v_ofDataValue_x3f_306_ = lean_ctor_get(v_inst_301_, 1);
lean_inc_ref(v_ofDataValue_x3f_306_);
lean_dec_ref(v_inst_301_);
v___x_307_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_305_, v_k_303_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; 
lean_dec_ref(v_ofDataValue_x3f_306_);
v___x_308_ = lean_box(0);
return v___x_308_;
}
else
{
lean_object* v_val_309_; lean_object* v___x_310_; 
v_val_309_ = lean_ctor_get(v___x_307_, 0);
lean_inc(v_val_309_);
lean_dec_ref_known(v___x_307_, 1);
v___x_310_ = lean_apply_1(v_ofDataValue_x3f_306_, v_val_309_);
return v___x_310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg___boxed(lean_object* v_inst_311_, lean_object* v_o_312_, lean_object* v_k_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_311_, v_o_312_, v_k_313_);
lean_dec(v_k_313_);
lean_dec_ref(v_o_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f(lean_object* v_00_u03b1_315_, lean_object* v_inst_316_, lean_object* v_o_317_, lean_object* v_k_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_316_, v_o_317_, v_k_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___boxed(lean_object* v_00_u03b1_320_, lean_object* v_inst_321_, lean_object* v_o_322_, lean_object* v_k_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Linter_LinterOptions_get_x3f(v_00_u03b1_320_, v_inst_321_, v_o_322_, v_k_323_);
lean_dec(v_k_323_);
lean_dec_ref(v_o_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg___lam__0(lean_object* v___x_325_, lean_object* v_o_326_, lean_object* v_toPure_327_, lean_object* v_____do__lift_328_){
_start:
{
lean_object* v___x_329_; lean_object* v_toEnvExtension_330_; lean_object* v_asyncMode_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v_merged_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_343_; 
v___x_329_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_330_ = lean_ctor_get(v___x_329_, 0);
v_asyncMode_331_ = lean_ctor_get(v_toEnvExtension_330_, 2);
v___x_332_ = lean_box(0);
v___x_333_ = 0;
v___x_334_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_325_, v___x_329_, v_____do__lift_328_, v_asyncMode_331_, v___x_332_, v___x_333_);
v_merged_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v___x_334_, 1);
lean_dec(v_unused_344_);
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_merged_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_343_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 1, v_merged_335_);
lean_ctor_set(v___x_337_, 0, v_o_326_);
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_o_326_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_merged_335_);
v___x_340_ = v_reuseFailAlloc_342_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; 
v___x_341_ = lean_apply_2(v_toPure_327_, lean_box(0), v___x_340_);
return v___x_341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg(lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_o_347_){
_start:
{
lean_object* v_toApplicative_348_; lean_object* v_toBind_349_; lean_object* v_getEnv_350_; lean_object* v_toPure_351_; lean_object* v___x_352_; lean_object* v___f_353_; lean_object* v___x_354_; 
v_toApplicative_348_ = lean_ctor_get(v_inst_345_, 0);
lean_inc_ref(v_toApplicative_348_);
v_toBind_349_ = lean_ctor_get(v_inst_345_, 1);
lean_inc(v_toBind_349_);
lean_dec_ref(v_inst_345_);
v_getEnv_350_ = lean_ctor_get(v_inst_346_, 0);
lean_inc(v_getEnv_350_);
lean_dec_ref(v_inst_346_);
v_toPure_351_ = lean_ctor_get(v_toApplicative_348_, 1);
lean_inc(v_toPure_351_);
lean_dec_ref(v_toApplicative_348_);
v___x_352_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default));
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Options_toLinterOptions___redArg___lam__0), 4, 3);
lean_closure_set(v___f_353_, 0, v___x_352_);
lean_closure_set(v___f_353_, 1, v_o_347_);
lean_closure_set(v___f_353_, 2, v_toPure_351_);
v___x_354_ = lean_apply_4(v_toBind_349_, lean_box(0), lean_box(0), v_getEnv_350_, v___f_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions(lean_object* v_m_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_o_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Options_toLinterOptions___redArg(v_inst_356_, v_inst_357_, v_o_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg(lean_object* v_o_360_, lean_object* v_opt_361_){
_start:
{
lean_object* v_linterSets_362_; lean_object* v_name_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v_linterSets_362_ = lean_ctor_get(v_o_360_, 1);
v_name_363_ = lean_ctor_get(v_opt_361_, 0);
v___x_364_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_365_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_linterSets_362_, v_name_363_, v___x_364_);
return v___x_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg___boxed(lean_object* v_o_366_, lean_object* v_opt_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_366_, v_opt_367_);
lean_dec_ref(v_opt_367_);
lean_dec_ref(v_o_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet(lean_object* v_00_u03b1_369_, lean_object* v_o_370_, lean_object* v_opt_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_370_, v_opt_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___boxed(lean_object* v_00_u03b1_373_, lean_object* v_o_374_, lean_object* v_opt_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Linter_LinterOptions_getSet(v_00_u03b1_373_, v_o_374_, v_opt_375_);
lean_dec_ref(v_opt_375_);
lean_dec_ref(v_o_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg___lam__0(lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_____do__lift_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l_Lean_Options_toLinterOptions___redArg(v_inst_377_, v_inst_378_, v_____do__lift_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg(lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v_toBind_384_; lean_object* v_getOptions_385_; lean_object* v___f_386_; lean_object* v___x_387_; 
v_toBind_384_ = lean_ctor_get(v_inst_381_, 1);
lean_inc(v_toBind_384_);
v_getOptions_385_ = lean_ctor_get(v_inst_382_, 0);
lean_inc(v_getOptions_385_);
lean_dec_ref(v_inst_382_);
v___f_386_ = lean_alloc_closure((void*)(l_Lean_Linter_getLinterOptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_386_, 0, v_inst_381_);
lean_closure_set(v___f_386_, 1, v_inst_383_);
v___x_387_ = lean_apply_4(v_toBind_384_, lean_box(0), lean_box(0), v_getOptions_385_, v___f_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions(lean_object* v_m_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_inst_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_389_, v_inst_390_, v_inst_391_);
return v___x_392_;
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(lean_object* v_name_393_, lean_object* v_decl_394_, lean_object* v_ref_395_){
_start:
{
lean_object* v_defValue_397_; lean_object* v_descr_398_; lean_object* v_deprecation_x3f_399_; lean_object* v___x_400_; uint8_t v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v_defValue_397_ = lean_ctor_get(v_decl_394_, 0);
v_descr_398_ = lean_ctor_get(v_decl_394_, 1);
v_deprecation_x3f_399_ = lean_ctor_get(v_decl_394_, 2);
v___x_400_ = lean_alloc_ctor(1, 0, 1);
v___x_401_ = lean_unbox(v_defValue_397_);
lean_ctor_set_uint8(v___x_400_, 0, v___x_401_);
lean_inc(v_deprecation_x3f_399_);
lean_inc_ref(v_descr_398_);
lean_inc_n(v_name_393_, 2);
v___x_402_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_402_, 0, v_name_393_);
lean_ctor_set(v___x_402_, 1, v_ref_395_);
lean_ctor_set(v___x_402_, 2, v___x_400_);
lean_ctor_set(v___x_402_, 3, v_descr_398_);
lean_ctor_set(v___x_402_, 4, v_deprecation_x3f_399_);
v___x_403_ = lean_register_option(v_name_393_, v___x_402_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_411_; 
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_411_ == 0)
{
lean_object* v_unused_412_; 
v_unused_412_ = lean_ctor_get(v___x_403_, 0);
lean_dec(v_unused_412_);
v___x_405_ = v___x_403_;
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
else
{
lean_dec(v___x_403_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_411_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
lean_inc(v_defValue_397_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v_name_393_);
lean_ctor_set(v___x_407_, 1, v_defValue_397_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 0, v___x_407_);
v___x_409_ = v___x_405_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_407_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec(v_name_393_);
v_a_413_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_403_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_403_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_393_ = stack[0].m_obj;
lean_object* v_decl_394_ = stack[1].m_obj;
lean_object* v_ref_395_ = stack[2].m_obj;
lean_object* v_res_421_;
v_res_421_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v_name_393_, v_decl_394_, v_ref_395_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_422_, lean_object* v_decl_423_, lean_object* v_ref_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v_name_422_, v_decl_423_, v_ref_424_);
lean_dec_ref(v_decl_423_);
return v_res_426_;
}
}
lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_444_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_445_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_446_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_447_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_444_, v___x_445_, v___x_446_);
return v___x_447_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_448_;
v_res_448_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_();
stack->m_obj
 = v_res_448_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4____boxed(lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_();
return v_res_450_;
}
}
lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_467_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_468_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_469_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_470_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_467_, v___x_468_, v___x_469_);
return v___x_470_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_471_;
v_res_471_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_();
stack->m_obj
 = v_res_471_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4____boxed(lean_object* v_a_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_();
return v_res_473_;
}
}
lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_490_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_491_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_492_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_493_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_490_, v___x_491_, v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_494_;
v_res_494_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_();
stack->m_obj
 = v_res_494_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4____boxed(lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_();
return v_res_496_;
}
}
lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_500_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_));
v___x_501_ = lean_st_mk_ref(v___x_500_);
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_503_;
v_res_503_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_();
stack->m_obj
 = v_res_503_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2____boxed(lean_object* v_a_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_();
return v_res_505_;
}
}
lean_object* l_Lean_Linter_addEnvLinterOption(lean_object* v_opt_506_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_508_ = l_Lean_Linter_envLinterOptionsRef;
v___x_509_ = lean_st_ref_take(v___x_508_);
v___x_510_ = lean_array_push(v___x_509_, v_opt_506_);
v___x_511_ = lean_st_ref_put(v___x_508_, v___x_510_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
LEAN_EXPORT void l_Lean_Linter_addEnvLinterOption_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_506_ = stack[0].m_obj;
lean_object* v_res_513_;
v_res_513_ = l_Lean_Linter_addEnvLinterOption(v_opt_506_);
stack->m_obj
 = v_res_513_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_addEnvLinterOption___boxed(lean_object* v_opt_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_Linter_addEnvLinterOption(v_opt_514_);
return v_res_516_;
}
}
uint8_t l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(lean_object* v_o_517_, lean_object* v_k_518_, uint8_t v_defVal_519_){
_start:
{
lean_object* v_toOptions_520_; lean_object* v_map_521_; lean_object* v___x_522_; 
v_toOptions_520_ = lean_ctor_get(v_o_517_, 0);
v_map_521_ = lean_ctor_get(v_toOptions_520_, 0);
v___x_522_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_521_, v_k_518_);
if (lean_obj_tag(v___x_522_) == 0)
{
return v_defVal_519_;
}
else
{
lean_object* v_val_523_; 
v_val_523_ = lean_ctor_get(v___x_522_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v___x_522_, 1);
if (lean_obj_tag(v_val_523_) == 1)
{
uint8_t v_v_524_; 
v_v_524_ = lean_ctor_get_uint8(v_val_523_, 0);
lean_dec_ref_known(v_val_523_, 0);
return v_v_524_;
}
else
{
lean_dec(v_val_523_);
return v_defVal_519_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_517_ = stack[0].m_obj;
lean_object* v_k_518_ = stack[1].m_obj;
uint8_t v_defVal_519_ = stack[2].m_num;
uint8_t v_res_525_;
v_res_525_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_517_, v_k_518_, v_defVal_519_);
stack->m_num = v_res_525_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0___boxed(lean_object* v_o_526_, lean_object* v_k_527_, lean_object* v_defVal_528_){
_start:
{
uint8_t v_defVal_boxed_529_; uint8_t v_res_530_; lean_object* v_r_531_; 
v_defVal_boxed_529_ = lean_unbox(v_defVal_528_);
v_res_530_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_526_, v_k_527_, v_defVal_boxed_529_);
lean_dec(v_k_527_);
lean_dec_ref(v_o_526_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
uint8_t l_Lean_Linter_getLinterAll(lean_object* v_o_532_, uint8_t v_defValue_533_){
_start:
{
lean_object* v___x_534_; lean_object* v_name_535_; uint8_t v___x_536_; 
v___x_534_ = l_Lean_Linter_linter_all;
v_name_535_ = lean_ctor_get(v___x_534_, 0);
v___x_536_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_532_, v_name_535_, v_defValue_533_);
return v___x_536_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_532_ = stack[0].m_obj;
uint8_t v_defValue_533_ = stack[1].m_num;
uint8_t v_res_537_;
v_res_537_ = l_Lean_Linter_getLinterAll(v_o_532_, v_defValue_533_);
stack->m_num = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterAll___boxed(lean_object* v_o_538_, lean_object* v_defValue_539_){
_start:
{
uint8_t v_defValue_boxed_540_; uint8_t v_res_541_; lean_object* v_r_542_; 
v_defValue_boxed_540_ = lean_unbox(v_defValue_539_);
v_res_541_ = l_Lean_Linter_getLinterAll(v_o_538_, v_defValue_boxed_540_);
lean_dec_ref(v_o_538_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(lean_object* v_o_543_, lean_object* v_k_544_){
_start:
{
lean_object* v_toOptions_545_; lean_object* v_map_546_; lean_object* v___x_547_; 
v_toOptions_545_ = lean_ctor_get(v_o_543_, 0);
v_map_546_ = lean_ctor_get(v_toOptions_545_, 0);
v___x_547_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_546_, v_k_544_);
if (lean_obj_tag(v___x_547_) == 0)
{
lean_object* v___x_548_; 
v___x_548_ = lean_box(0);
return v___x_548_;
}
else
{
lean_object* v_val_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_559_; 
v_val_549_ = lean_ctor_get(v___x_547_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_547_);
if (v_isSharedCheck_559_ == 0)
{
v___x_551_ = v___x_547_;
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_val_549_);
lean_dec(v___x_547_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_559_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
if (lean_obj_tag(v_val_549_) == 1)
{
uint8_t v_v_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v_v_553_ = lean_ctor_get_uint8(v_val_549_, 0);
lean_dec_ref_known(v_val_549_, 0);
v___x_554_ = lean_box(v_v_553_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_554_);
v___x_556_ = v___x_551_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
else
{
lean_object* v___x_558_; 
lean_del_object(v___x_551_);
lean_dec(v_val_549_);
v___x_558_ = lean_box(0);
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0___boxed(lean_object* v_o_560_, lean_object* v_k_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_560_, v_k_561_);
lean_dec(v_k_561_);
lean_dec_ref(v_o_560_);
return v_res_562_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(lean_object* v_x_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
if (lean_obj_tag(v_x_564_) == 0)
{
uint8_t v___x_565_; 
v___x_565_ = 1;
return v___x_565_;
}
else
{
uint8_t v___x_566_; 
v___x_566_ = 0;
return v___x_566_;
}
}
else
{
if (lean_obj_tag(v_x_564_) == 0)
{
uint8_t v___x_567_; 
v___x_567_ = 0;
return v___x_567_;
}
else
{
lean_object* v_val_568_; uint8_t v___x_569_; 
v_val_568_ = lean_ctor_get(v_x_564_, 0);
v___x_569_ = lean_unbox(v_val_568_);
if (v___x_569_ == 0)
{
lean_object* v_val_570_; uint8_t v___x_571_; 
v_val_570_ = lean_ctor_get(v_x_563_, 0);
v___x_571_ = lean_unbox(v_val_570_);
if (v___x_571_ == 0)
{
uint8_t v___x_572_; 
v___x_572_ = 1;
return v___x_572_;
}
else
{
uint8_t v___x_573_; 
v___x_573_ = lean_unbox(v_val_568_);
return v___x_573_;
}
}
else
{
lean_object* v_val_574_; uint8_t v___x_575_; 
v_val_574_ = lean_ctor_get(v_x_563_, 0);
v___x_575_ = lean_unbox(v_val_574_);
return v___x_575_;
}
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_563_ = stack[0].m_obj;
lean_object* v_x_564_ = stack[1].m_obj;
uint8_t v_res_576_;
v_res_576_ = l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(v_x_563_, v_x_564_);
stack->m_num = v_res_576_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1___boxed(lean_object* v_x_577_, lean_object* v_x_578_){
_start:
{
uint8_t v_res_579_; lean_object* v_r_580_; 
v_res_579_ = l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(v_x_577_, v_x_578_);
lean_dec(v_x_578_);
lean_dec(v_x_577_);
v_r_580_ = lean_box(v_res_579_);
return v_r_580_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(lean_object* v_o_584_, lean_object* v_as_585_, size_t v_i_586_, size_t v_stop_587_){
_start:
{
uint8_t v___x_588_; 
v___x_588_ = lean_usize_dec_eq(v_i_586_, v_stop_587_);
if (v___x_588_ == 0)
{
uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_589_ = 1;
v___x_590_ = lean_array_uget_borrowed(v_as_585_, v_i_586_);
v___x_591_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_584_, v___x_590_);
v___x_592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0));
v___x_593_ = l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(v___x_591_, v___x_592_);
lean_dec(v___x_591_);
if (v___x_593_ == 0)
{
size_t v___x_594_; size_t v___x_595_; 
v___x_594_ = ((size_t)1ULL);
v___x_595_ = lean_usize_add(v_i_586_, v___x_594_);
v_i_586_ = v___x_595_;
goto _start;
}
else
{
return v___x_589_;
}
}
else
{
uint8_t v___x_597_; 
v___x_597_ = 0;
return v___x_597_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_584_ = stack[0].m_obj;
lean_object* v_as_585_ = stack[1].m_obj;
size_t v_i_586_ = stack[2].m_num;
size_t v_stop_587_ = stack[3].m_num;
uint8_t v_res_598_;
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_584_, v_as_585_, v_i_586_, v_stop_587_);
stack->m_num = v_res_598_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___boxed(lean_object* v_o_599_, lean_object* v_as_600_, lean_object* v_i_601_, lean_object* v_stop_602_){
_start:
{
size_t v_i_boxed_603_; size_t v_stop_boxed_604_; uint8_t v_res_605_; lean_object* v_r_606_; 
v_i_boxed_603_ = lean_unbox_usize(v_i_601_);
lean_dec(v_i_601_);
v_stop_boxed_604_ = lean_unbox_usize(v_stop_602_);
lean_dec(v_stop_602_);
v_res_605_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_599_, v_as_600_, v_i_boxed_603_, v_stop_boxed_604_);
lean_dec_ref(v_as_600_);
lean_dec_ref(v_o_599_);
v_r_606_ = lean_box(v_res_605_);
return v_r_606_;
}
}
uint8_t l_Lean_Linter_getLinterValue(lean_object* v_opt_607_, lean_object* v_o_608_){
_start:
{
lean_object* v_name_609_; lean_object* v_defValue_610_; uint8_t v___y_612_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_name_609_ = lean_ctor_get(v_opt_607_, 0);
v_defValue_610_ = lean_ctor_get(v_opt_607_, 1);
v___x_615_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_608_, v_opt_607_);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_array_get_size(v___x_615_);
v___x_618_ = lean_nat_dec_lt(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
uint8_t v___x_619_; 
lean_dec(v___x_615_);
v___x_619_ = lean_unbox(v_defValue_610_);
v___y_612_ = v___x_619_;
goto v___jp_611_;
}
else
{
if (v___x_618_ == 0)
{
uint8_t v___x_620_; 
lean_dec(v___x_615_);
v___x_620_ = lean_unbox(v_defValue_610_);
v___y_612_ = v___x_620_;
goto v___jp_611_;
}
else
{
size_t v___x_621_; size_t v___x_622_; uint8_t v___x_623_; 
v___x_621_ = ((size_t)0ULL);
v___x_622_ = lean_usize_of_nat(v___x_617_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_608_, v___x_615_, v___x_621_, v___x_622_);
lean_dec(v___x_615_);
if (v___x_623_ == 0)
{
uint8_t v___x_624_; 
v___x_624_ = lean_unbox(v_defValue_610_);
v___y_612_ = v___x_624_;
goto v___jp_611_;
}
else
{
v___y_612_ = v___x_623_;
goto v___jp_611_;
}
}
}
v___jp_611_:
{
uint8_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = l_Lean_Linter_getLinterAll(v_o_608_, v___y_612_);
v___x_614_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_608_, v_name_609_, v___x_613_);
return v___x_614_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_607_ = stack[0].m_obj;
lean_object* v_o_608_ = stack[1].m_obj;
uint8_t v_res_625_;
v_res_625_ = l_Lean_Linter_getLinterValue(v_opt_607_, v_o_608_);
stack->m_num = v_res_625_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterValue___boxed(lean_object* v_opt_626_, lean_object* v_o_627_){
_start:
{
uint8_t v_res_628_; lean_object* v_r_629_; 
v_res_628_ = l_Lean_Linter_getLinterValue(v_opt_626_, v_o_627_);
lean_dec_ref(v_o_627_);
lean_dec_ref(v_opt_626_);
v_r_629_ = lean_box(v_res_628_);
return v_r_629_;
}
}
uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object* v_name_630_, lean_object* v_o_631_){
_start:
{
uint8_t v___y_633_; lean_object* v_linterSets_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_linterSets_636_ = lean_ctor_get(v_o_631_, 1);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_639_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_linterSets_636_, v_name_630_, v___x_638_);
v___x_640_ = lean_array_get_size(v___x_639_);
v___x_641_ = lean_nat_dec_lt(v___x_637_, v___x_640_);
if (v___x_641_ == 0)
{
lean_dec(v___x_639_);
v___y_633_ = v___x_641_;
goto v___jp_632_;
}
else
{
if (v___x_641_ == 0)
{
lean_dec(v___x_639_);
v___y_633_ = v___x_641_;
goto v___jp_632_;
}
else
{
size_t v___x_642_; size_t v___x_643_; uint8_t v___x_644_; 
v___x_642_ = ((size_t)0ULL);
v___x_643_ = lean_usize_of_nat(v___x_640_);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_631_, v___x_639_, v___x_642_, v___x_643_);
lean_dec(v___x_639_);
v___y_633_ = v___x_644_;
goto v___jp_632_;
}
}
v___jp_632_:
{
uint8_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = l_Lean_Linter_getLinterAll(v_o_631_, v___y_633_);
v___x_635_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_631_, v_name_630_, v___x_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_isLinterEnabledByOptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_630_ = stack[0].m_obj;
lean_object* v_o_631_ = stack[1].m_obj;
uint8_t v_res_645_;
v_res_645_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_630_, v_o_631_);
stack->m_num = v_res_645_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_isLinterEnabledByOptions___boxed(lean_object* v_name_646_, lean_object* v_o_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_646_, v_o_647_);
lean_dec_ref(v_o_647_);
lean_dec(v_name_646_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___redArg___closed__1(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = ((lean_object*)(l_Lean_Linter_logLint___redArg___closed__0));
v___x_658_ = l_Lean_stringToMessageData(v___x_657_);
return v___x_658_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___redArg___closed__3(void){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_660_ = ((lean_object*)(l_Lean_Linter_logLint___redArg___closed__2));
v___x_661_ = l_Lean_stringToMessageData(v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___redArg(lean_object* v_inst_662_, lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_linterOption_666_, lean_object* v_stx_667_, lean_object* v_msg_668_){
_start:
{
lean_object* v_name_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_687_; 
v_name_669_ = lean_ctor_get(v_linterOption_666_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v_linterOption_666_);
if (v_isSharedCheck_687_ == 0)
{
lean_object* v_unused_688_; 
v_unused_688_ = lean_ctor_get(v_linterOption_666_, 1);
lean_dec(v_unused_688_);
v___x_671_ = v_linterOption_666_;
v_isShared_672_ = v_isSharedCheck_687_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_name_669_);
lean_dec(v_linterOption_666_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_687_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_673_ = lean_obj_once(&l_Lean_Linter_logLint___redArg___closed__1, &l_Lean_Linter_logLint___redArg___closed__1_once, _init_l_Lean_Linter_logLint___redArg___closed__1);
lean_inc(v_name_669_);
v___x_674_ = l_Lean_MessageData_ofName(v_name_669_);
if (v_isShared_672_ == 0)
{
lean_ctor_set_tag(v___x_671_, 7);
lean_ctor_set(v___x_671_, 1, v___x_674_);
lean_ctor_set(v___x_671_, 0, v___x_673_);
v___x_676_ = v___x_671_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_674_);
v___x_676_ = v_reuseFailAlloc_686_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v_disable_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_677_ = lean_obj_once(&l_Lean_Linter_logLint___redArg___closed__3, &l_Lean_Linter_logLint___redArg___closed__3_once, _init_l_Lean_Linter_logLint___redArg___closed__3);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v_disable_679_ = l_Lean_MessageData_note(v___x_678_);
v___x_680_ = ((lean_object*)(l_Lean_Linter_linterMessageTag));
v___x_681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_681_, 0, v_msg_668_);
lean_ctor_set(v___x_681_, 1, v_disable_679_);
v___x_682_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_683_, 0, v_name_669_);
lean_ctor_set(v___x_683_, 1, v___x_682_);
lean_inc(v_stx_667_);
v___x_684_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_684_, 0, v_stx_667_);
lean_ctor_set(v___x_684_, 1, v___x_683_);
v___x_685_ = l_Lean_logWarningAt___redArg(v_inst_662_, v_inst_663_, v_inst_664_, v_inst_665_, v_stx_667_, v___x_684_);
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint(lean_object* v_m_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_linterOption_694_, lean_object* v_stx_695_, lean_object* v_msg_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_Linter_logLint___redArg(v_inst_690_, v_inst_691_, v_inst_692_, v_inst_693_, v_linterOption_694_, v_stx_695_, v_msg_696_);
return v___x_697_;
}
}
uint8_t l_Lean_MessageData_isLinterMessage___lam__0(lean_object* v_x_698_){
_start:
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = ((lean_object*)(l_Lean_Linter_linterMessageTag));
v___x_700_ = lean_name_eq(v_x_698_, v___x_699_);
return v___x_700_;
}
}
LEAN_EXPORT void l_Lean_MessageData_isLinterMessage___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_698_ = stack[0].m_obj;
uint8_t v_res_701_;
v_res_701_ = l_Lean_MessageData_isLinterMessage___lam__0(v_x_698_);
stack->m_num = v_res_701_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isLinterMessage___lam__0___boxed(lean_object* v_x_702_){
_start:
{
uint8_t v_res_703_; lean_object* v_r_704_; 
v_res_703_ = l_Lean_MessageData_isLinterMessage___lam__0(v_x_702_);
lean_dec(v_x_702_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
uint8_t l_Lean_MessageData_isLinterMessage(lean_object* v_msg_706_){
_start:
{
lean_object* v___f_707_; uint8_t v___x_708_; 
v___f_707_ = ((lean_object*)(l_Lean_MessageData_isLinterMessage___closed__0));
v___x_708_ = l_Lean_MessageData_hasTag(v___f_707_, v_msg_706_);
return v___x_708_;
}
}
LEAN_EXPORT void l_Lean_MessageData_isLinterMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_706_ = stack[0].m_obj;
uint8_t v_res_709_;
v_res_709_ = l_Lean_MessageData_isLinterMessage(v_msg_706_);
stack->m_num = v_res_709_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isLinterMessage___boxed(lean_object* v_msg_710_){
_start:
{
uint8_t v_res_711_; lean_object* v_r_712_; 
v_res_711_ = l_Lean_MessageData_isLinterMessage(v_msg_710_);
v_r_712_ = lean_box(v_res_711_);
return v_r_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0(lean_object* v_linterOption_713_, lean_object* v_toPure_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_stx_719_, lean_object* v_msg_720_, lean_object* v_____do__lift_721_){
_start:
{
uint8_t v___x_722_; 
v___x_722_ = l_Lean_Linter_getLinterValue(v_linterOption_713_, v_____do__lift_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; 
lean_dec_ref(v_msg_720_);
lean_dec(v_stx_719_);
lean_dec_ref(v_inst_718_);
lean_dec(v_inst_717_);
lean_dec_ref(v_inst_716_);
lean_dec_ref(v_inst_715_);
lean_dec_ref(v_linterOption_713_);
v___x_723_ = lean_box(0);
v___x_724_ = lean_apply_2(v_toPure_714_, lean_box(0), v___x_723_);
return v___x_724_;
}
else
{
lean_object* v___x_725_; 
lean_dec(v_toPure_714_);
v___x_725_ = l_Lean_Linter_logLint___redArg(v_inst_715_, v_inst_716_, v_inst_717_, v_inst_718_, v_linterOption_713_, v_stx_719_, v_msg_720_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0___boxed(lean_object* v_linterOption_726_, lean_object* v_toPure_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_stx_732_, lean_object* v_msg_733_, lean_object* v_____do__lift_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Linter_logLintIf___redArg___lam__0(v_linterOption_726_, v_toPure_727_, v_inst_728_, v_inst_729_, v_inst_730_, v_inst_731_, v_stx_732_, v_msg_733_, v_____do__lift_734_);
lean_dec_ref(v_____do__lift_734_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg(lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_linterOption_741_, lean_object* v_stx_742_, lean_object* v_msg_743_){
_start:
{
lean_object* v_toApplicative_744_; lean_object* v_toBind_745_; lean_object* v_toPure_746_; lean_object* v___x_747_; lean_object* v___f_748_; lean_object* v___x_749_; 
v_toApplicative_744_ = lean_ctor_get(v_inst_736_, 0);
v_toBind_745_ = lean_ctor_get(v_inst_736_, 1);
lean_inc(v_toBind_745_);
v_toPure_746_ = lean_ctor_get(v_toApplicative_744_, 1);
lean_inc(v_toPure_746_);
lean_inc_ref(v_inst_739_);
lean_inc_ref(v_inst_736_);
v___x_747_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_736_, v_inst_739_, v_inst_740_);
v___f_748_ = lean_alloc_closure((void*)(l_Lean_Linter_logLintIf___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_748_, 0, v_linterOption_741_);
lean_closure_set(v___f_748_, 1, v_toPure_746_);
lean_closure_set(v___f_748_, 2, v_inst_736_);
lean_closure_set(v___f_748_, 3, v_inst_737_);
lean_closure_set(v___f_748_, 4, v_inst_738_);
lean_closure_set(v___f_748_, 5, v_inst_739_);
lean_closure_set(v___f_748_, 6, v_stx_742_);
lean_closure_set(v___f_748_, 7, v_msg_743_);
v___x_749_ = lean_apply_4(v_toBind_745_, lean_box(0), lean_box(0), v___x_747_, v___f_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf(lean_object* v_m_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_linterOption_756_, lean_object* v_stx_757_, lean_object* v_msg_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Linter_logLintIf___redArg(v_inst_751_, v_inst_752_, v_inst_753_, v_inst_754_, v_inst_755_, v_linterOption_756_, v_stx_757_, v_msg_758_);
return v___x_759_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2(lean_object* v_env_760_, lean_object* v_as_761_, size_t v_i_762_, size_t v_stop_763_, lean_object* v_b_764_){
_start:
{
lean_object* v___y_766_; uint8_t v___x_770_; 
v___x_770_ = lean_usize_dec_eq(v_i_762_, v_stop_763_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v_fst_772_; uint8_t v___x_773_; 
v___x_771_ = lean_array_uget_borrowed(v_as_761_, v_i_762_);
v_fst_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_fst_772_);
lean_inc_ref(v_env_760_);
v___x_773_ = l_Lean_Environment_contains(v_env_760_, v_fst_772_, v___x_770_);
if (v___x_773_ == 0)
{
v___y_766_ = v_b_764_;
goto v___jp_765_;
}
else
{
lean_object* v___x_774_; 
lean_inc(v___x_771_);
v___x_774_ = lean_array_push(v_b_764_, v___x_771_);
v___y_766_ = v___x_774_;
goto v___jp_765_;
}
}
else
{
lean_dec_ref(v_env_760_);
return v_b_764_;
}
v___jp_765_:
{
size_t v___x_767_; size_t v___x_768_; 
v___x_767_ = ((size_t)1ULL);
v___x_768_ = lean_usize_add(v_i_762_, v___x_767_);
v_i_762_ = v___x_768_;
v_b_764_ = v___y_766_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_760_ = stack[0].m_obj;
lean_object* v_as_761_ = stack[1].m_obj;
size_t v_i_762_ = stack[2].m_num;
size_t v_stop_763_ = stack[3].m_num;
lean_object* v_b_764_ = stack[4].m_obj;
lean_object* v_res_775_;
v_res_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2(v_env_760_, v_as_761_, v_i_762_, v_stop_763_, v_b_764_);
stack->m_obj
 = v_res_775_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_776_, lean_object* v_as_777_, lean_object* v_i_778_, lean_object* v_stop_779_, lean_object* v_b_780_){
_start:
{
size_t v_i_boxed_781_; size_t v_stop_boxed_782_; lean_object* v_res_783_; 
v_i_boxed_781_ = lean_unbox_usize(v_i_778_);
lean_dec(v_i_778_);
v_stop_boxed_782_ = lean_unbox_usize(v_stop_779_);
lean_dec(v_stop_779_);
v_res_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2(v_env_776_, v_as_777_, v_i_boxed_781_, v_stop_boxed_782_, v_b_780_);
lean_dec_ref(v_as_777_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_784_, lean_object* v_x_785_){
_start:
{
if (lean_obj_tag(v_x_785_) == 0)
{
lean_object* v_k_786_; lean_object* v_v_787_; lean_object* v_l_788_; lean_object* v_r_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_k_786_ = lean_ctor_get(v_x_785_, 1);
v_v_787_ = lean_ctor_get(v_x_785_, 2);
v_l_788_ = lean_ctor_get(v_x_785_, 3);
v_r_789_ = lean_ctor_get(v_x_785_, 4);
v___x_790_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_784_, v_l_788_);
lean_inc(v_v_787_);
lean_inc(v_k_786_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_k_786_);
lean_ctor_set(v___x_791_, 1, v_v_787_);
v___x_792_ = lean_array_push(v___x_790_, v___x_791_);
v_init_784_ = v___x_792_;
v_x_785_ = v_r_789_;
goto _start;
}
else
{
return v_init_784_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_794_, lean_object* v_x_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_794_, v_x_795_);
lean_dec(v_x_795_);
return v_res_796_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(lean_object* v_env_797_, lean_object* v_as_798_, size_t v_i_799_, size_t v_stop_800_, lean_object* v_b_801_){
_start:
{
lean_object* v___y_803_; uint8_t v___x_807_; 
v___x_807_ = lean_usize_dec_eq(v_i_799_, v_stop_800_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v_fst_809_; uint8_t v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_808_ = lean_array_uget_borrowed(v_as_798_, v_i_799_);
v_fst_809_ = lean_ctor_get(v___x_808_, 0);
v___x_810_ = 1;
lean_inc_ref(v_env_797_);
v___x_811_ = l_Lean_Environment_setExporting(v_env_797_, v___x_810_);
lean_inc(v_fst_809_);
v___x_812_ = l_Lean_Environment_contains(v___x_811_, v_fst_809_, v___x_810_);
if (v___x_812_ == 0)
{
v___y_803_ = v_b_801_;
goto v___jp_802_;
}
else
{
lean_object* v___x_813_; 
lean_inc(v___x_808_);
v___x_813_ = lean_array_push(v_b_801_, v___x_808_);
v___y_803_ = v___x_813_;
goto v___jp_802_;
}
}
else
{
lean_dec_ref(v_env_797_);
return v_b_801_;
}
v___jp_802_:
{
size_t v___x_804_; size_t v___x_805_; 
v___x_804_ = ((size_t)1ULL);
v___x_805_ = lean_usize_add(v_i_799_, v___x_804_);
v_i_799_ = v___x_805_;
v_b_801_ = v___y_803_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_797_ = stack[0].m_obj;
lean_object* v_as_798_ = stack[1].m_obj;
size_t v_i_799_ = stack[2].m_num;
size_t v_stop_800_ = stack[3].m_num;
lean_object* v_b_801_ = stack[4].m_obj;
lean_object* v_res_814_;
v_res_814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_797_, v_as_798_, v_i_799_, v_stop_800_, v_b_801_);
stack->m_obj
 = v_res_814_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_815_, lean_object* v_as_816_, lean_object* v_i_817_, lean_object* v_stop_818_, lean_object* v_b_819_){
_start:
{
size_t v_i_boxed_820_; size_t v_stop_boxed_821_; lean_object* v_res_822_; 
v_i_boxed_820_ = lean_unbox_usize(v_i_817_);
lean_dec(v_i_817_);
v_stop_boxed_821_ = lean_unbox_usize(v_stop_818_);
lean_dec(v_stop_818_);
v_res_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_815_, v_as_816_, v_i_boxed_820_, v_stop_boxed_821_, v_b_819_);
lean_dec_ref(v_as_816_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(lean_object* v_env_825_, lean_object* v_s_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___y_829_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_844_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_845_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v___x_844_, v_s_826_);
v___x_846_ = lean_array_get_size(v___x_845_);
v___x_847_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_848_ = lean_nat_dec_lt(v___x_827_, v___x_846_);
if (v___x_848_ == 0)
{
lean_dec_ref(v___x_845_);
v___y_829_ = v___x_847_;
goto v___jp_828_;
}
else
{
uint8_t v___x_849_; 
v___x_849_ = lean_nat_dec_le(v___x_846_, v___x_846_);
if (v___x_849_ == 0)
{
if (v___x_848_ == 0)
{
lean_dec_ref(v___x_845_);
v___y_829_ = v___x_847_;
goto v___jp_828_;
}
else
{
size_t v___x_850_; size_t v___x_851_; lean_object* v___x_852_; 
v___x_850_ = ((size_t)0ULL);
v___x_851_ = lean_usize_of_nat(v___x_846_);
lean_inc_ref(v_env_825_);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2(v_env_825_, v___x_845_, v___x_850_, v___x_851_, v___x_847_);
lean_dec_ref(v___x_845_);
v___y_829_ = v___x_852_;
goto v___jp_828_;
}
}
else
{
size_t v___x_853_; size_t v___x_854_; lean_object* v___x_855_; 
v___x_853_ = ((size_t)0ULL);
v___x_854_ = lean_usize_of_nat(v___x_846_);
lean_inc_ref(v_env_825_);
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2(v_env_825_, v___x_845_, v___x_853_, v___x_854_, v___x_847_);
lean_dec_ref(v___x_845_);
v___y_829_ = v___x_855_;
goto v___jp_828_;
}
}
v___jp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_830_ = lean_array_get_size(v___y_829_);
v___x_831_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_832_ = lean_nat_dec_lt(v___x_827_, v___x_830_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
lean_dec_ref(v_env_825_);
v___x_833_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_831_);
lean_ctor_set(v___x_833_, 2, v___y_829_);
return v___x_833_;
}
else
{
uint8_t v___x_834_; 
v___x_834_ = lean_nat_dec_le(v___x_830_, v___x_830_);
if (v___x_834_ == 0)
{
if (v___x_832_ == 0)
{
lean_object* v___x_835_; 
lean_dec_ref(v_env_825_);
v___x_835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_835_, 0, v___x_831_);
lean_ctor_set(v___x_835_, 1, v___x_831_);
lean_ctor_set(v___x_835_, 2, v___y_829_);
return v___x_835_;
}
else
{
size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_of_nat(v___x_830_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_825_, v___y_829_, v___x_836_, v___x_837_, v___x_831_);
lean_inc_ref(v___x_838_);
v___x_839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
lean_ctor_set(v___x_839_, 2, v___y_829_);
return v___x_839_;
}
}
else
{
size_t v___x_840_; size_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_840_ = ((size_t)0ULL);
v___x_841_ = lean_usize_of_nat(v___x_830_);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_825_, v___y_829_, v___x_840_, v___x_841_, v___x_831_);
lean_inc_ref(v___x_842_);
v___x_843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
lean_ctor_set(v___x_843_, 2, v___y_829_);
return v___x_843_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed(lean_object* v_env_856_, lean_object* v_s_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(v_env_856_, v_s_857_);
lean_dec(v_s_857_);
return v_res_858_;
}
}
lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; 
v___f_864_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_865_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_866_ = lean_box(0);
v___x_867_ = 0;
v___x_868_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_865_, v___x_866_, v___x_867_, v___f_864_);
return v___x_868_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_869_;
v_res_869_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_();
stack->m_obj
 = v_res_869_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed(lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_();
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0(lean_object* v_init_872_, lean_object* v_t_873_){
_start:
{
lean_object* v___x_874_; 
v___x_874_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_872_, v_t_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_875_, lean_object* v_t_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0(v_init_875_, v_t_876_);
lean_dec(v_t_876_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(lean_object* v_env_878_, lean_object* v_declName_879_, lean_object* v_optName_880_){
_start:
{
lean_object* v___x_881_; lean_object* v_toEnvExtension_882_; lean_object* v_asyncMode_883_; lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; 
v___x_881_ = l_Lean_Linter_envLinterSnapshotExt;
v_toEnvExtension_882_ = lean_ctor_get(v___x_881_, 0);
v_asyncMode_883_ = lean_ctor_get(v_toEnvExtension_882_, 2);
v___x_884_ = lean_box(1);
v___x_885_ = 0;
v___x_886_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_884_, v___x_881_, v_env_878_, v_declName_879_, v_asyncMode_883_, v___x_885_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v___x_887_; 
v___x_887_ = lean_box(0);
return v___x_887_;
}
else
{
lean_object* v_val_888_; lean_object* v___x_889_; 
v_val_888_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_val_888_);
lean_dec_ref_known(v___x_886_, 1);
v___x_889_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_888_, v_optName_880_);
lean_dec(v_val_888_);
return v___x_889_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f___boxed(lean_object* v_env_890_, lean_object* v_declName_891_, lean_object* v_optName_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(v_env_890_, v_declName_891_, v_optName_892_);
lean_dec(v_optName_892_);
return v_res_893_;
}
}
lean_object* runtime_initialize_Lean_MonadEnv(uint8_t builtin);
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Function(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Linter_instEmptyCollectionLinterSets___aux__1 = _init_l_Lean_Linter_instEmptyCollectionLinterSets___aux__1();
lean_mark_persistent(l_Lean_Linter_instEmptyCollectionLinterSets___aux__1);
l_Lean_Linter_instEmptyCollectionLinterSets = _init_l_Lean_Linter_instEmptyCollectionLinterSets();
lean_mark_persistent(l_Lean_Linter_instEmptyCollectionLinterSets);
l_Lean_Linter_instInhabitedLinterSets___aux__1 = _init_l_Lean_Linter_instInhabitedLinterSets___aux__1();
lean_mark_persistent(l_Lean_Linter_instInhabitedLinterSets___aux__1);
l_Lean_Linter_instInhabitedLinterSets = _init_l_Lean_Linter_instInhabitedLinterSets();
lean_mark_persistent(l_Lean_Linter_instInhabitedLinterSets);
res = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_builtinLinterSetsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_builtinLinterSetsRef);
lean_dec_ref(res);
res = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linterSetsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linterSetsExt);
lean_dec_ref(res);
res = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_all = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_all);
lean_dec_ref(res);
res = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_extra = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_extra);
lean_dec_ref(res);
res = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_coreInternal = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_coreInternal);
lean_dec_ref(res);
res = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_envLinterOptionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_envLinterOptionsRef);
lean_dec_ref(res);
res = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_envLinterSnapshotExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_envLinterSnapshotExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Init(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_MonadEnv(uint8_t builtin);
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
lean_object* initialize_Init_Data_Function(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Init(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Init(builtin);
}
#ifdef __cplusplus
}
#endif
