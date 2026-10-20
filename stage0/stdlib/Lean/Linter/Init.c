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
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2_(){
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
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_677559138____hygCtx___hyg_2_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_addBuiltinLinterSet(lean_object* v_setName_64_, lean_object* v_linterNames_65_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_67_ = l_Lean_Linter_builtinLinterSetsRef;
v___x_68_ = lean_st_ref_take(v___x_67_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v_setName_64_);
lean_ctor_set(v___x_69_, 1, v_linterNames_65_);
v___x_70_ = lean_array_push(v___x_68_, v___x_69_);
v___x_71_ = lean_st_ref_put(v___x_67_, v___x_70_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_addBuiltinLinterSet___boxed(lean_object* v_setName_73_, lean_object* v_linterNames_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lean_Linter_addBuiltinLinterSet(v_setName_73_, v_linterNames_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v_st_77_, lean_object* v_x_78_){
_start:
{
lean_object* v_fst_79_; lean_object* v_snd_80_; lean_object* v_merged_81_; lean_object* v_localEntries_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_91_; 
v_fst_79_ = lean_ctor_get(v_x_78_, 0);
v_snd_80_ = lean_ctor_get(v_x_78_, 1);
v_merged_81_ = lean_ctor_get(v_st_77_, 0);
v_localEntries_82_ = lean_ctor_get(v_st_77_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_st_77_);
if (v_isSharedCheck_91_ == 0)
{
v___x_84_ = v_st_77_;
v_isShared_85_ = v_isSharedCheck_91_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_localEntries_82_);
lean_inc(v_merged_81_);
lean_dec(v_st_77_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_91_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
lean_inc(v_snd_80_);
lean_inc(v_fst_79_);
v___x_86_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_79_, v_merged_81_, v_snd_80_);
v___x_87_ = lean_array_push(v_localEntries_82_, v_x_78_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v___x_87_);
lean_ctor_set(v___x_84_, 0, v___x_86_);
v___x_89_ = v___x_84_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v___x_87_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v_x_92_, lean_object* v_s_93_){
_start:
{
lean_object* v_localEntries_94_; lean_object* v___x_95_; 
v_localEntries_94_ = lean_ctor_get(v_s_93_, 1);
lean_inc_ref_n(v_localEntries_94_, 3);
v___x_95_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_95_, 0, v_localEntries_94_);
lean_ctor_set(v___x_95_, 1, v_localEntries_94_);
lean_ctor_set(v___x_95_, 2, v_localEntries_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v_x_96_, lean_object* v_s_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v_x_96_, v_s_97_);
lean_dec_ref(v_s_97_);
lean_dec_ref(v_x_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v_x_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(0);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v_x_101_);
lean_dec_ref(v_x_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v_st_103_){
_start:
{
lean_object* v_localEntries_104_; 
v_localEntries_104_ = lean_ctor_get(v_st_103_, 1);
lean_inc_ref(v_localEntries_104_);
return v_localEntries_104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v_st_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v_st_105_);
lean_dec_ref(v_st_105_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(lean_object* v_as_107_, size_t v_i_108_, size_t v_stop_109_, lean_object* v_b_110_){
_start:
{
uint8_t v___x_111_; 
v___x_111_ = lean_usize_dec_eq(v_i_108_, v_stop_109_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v_fst_113_; lean_object* v_snd_114_; lean_object* v___x_115_; size_t v___x_116_; size_t v___x_117_; 
v___x_112_ = lean_array_uget_borrowed(v_as_107_, v_i_108_);
v_fst_113_ = lean_ctor_get(v___x_112_, 0);
v_snd_114_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_snd_114_);
lean_inc(v_fst_113_);
v___x_115_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_113_, v_b_110_, v_snd_114_);
v___x_116_ = ((size_t)1ULL);
v___x_117_ = lean_usize_add(v_i_108_, v___x_116_);
v_i_108_ = v___x_117_;
v_b_110_ = v___x_115_;
goto _start;
}
else
{
return v_b_110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2___boxed(lean_object* v_as_119_, lean_object* v_i_120_, lean_object* v_stop_121_, lean_object* v_b_122_){
_start:
{
size_t v_i_boxed_123_; size_t v_stop_boxed_124_; lean_object* v_res_125_; 
v_i_boxed_123_ = lean_unbox_usize(v_i_120_);
lean_dec(v_i_120_);
v_stop_boxed_124_ = lean_unbox_usize(v_stop_121_);
lean_dec(v_stop_121_);
v_res_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v_as_119_, v_i_boxed_123_, v_stop_boxed_124_, v_b_122_);
lean_dec_ref(v_as_119_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v___x_126_){
_start:
{
lean_object* v___x_128_; lean_object* v___y_130_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_128_ = lean_st_ref_get(v___x_126_);
v___x_134_ = lean_box(1);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_array_get_size(v___x_128_);
v___x_137_ = lean_nat_dec_lt(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_dec(v___x_128_);
v___y_130_ = v___x_134_;
goto v___jp_129_;
}
else
{
size_t v___x_138_; size_t v___x_139_; lean_object* v___x_140_; 
v___x_138_ = ((size_t)0ULL);
v___x_139_ = lean_usize_of_nat(v___x_136_);
v___x_140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v___x_128_, v___x_138_, v___x_139_, v___x_134_);
lean_dec(v___x_128_);
v___y_130_ = v___x_140_;
goto v___jp_129_;
}
v___jp_129_:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___y_130_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v___x_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v___x_141_);
lean_dec(v___x_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(lean_object* v_as_144_, size_t v_i_145_, size_t v_stop_146_, lean_object* v_b_147_){
_start:
{
uint8_t v___x_148_; 
v___x_148_ = lean_usize_dec_eq(v_i_145_, v_stop_146_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v_fst_150_; lean_object* v_snd_151_; lean_object* v___x_152_; size_t v___x_153_; size_t v___x_154_; lean_object* v___x_155_; 
v___x_149_ = lean_array_uget_borrowed(v_as_144_, v_i_145_);
v_fst_150_ = lean_ctor_get(v___x_149_, 0);
v_snd_151_ = lean_ctor_get(v___x_149_, 1);
lean_inc(v_snd_151_);
lean_inc(v_fst_150_);
v___x_152_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_150_, v_b_147_, v_snd_151_);
v___x_153_ = ((size_t)1ULL);
v___x_154_ = lean_usize_add(v_i_145_, v___x_153_);
v___x_155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v_as_144_, v___x_154_, v_stop_146_, v___x_152_);
return v___x_155_;
}
else
{
return v_b_147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_156_, lean_object* v_i_157_, lean_object* v_stop_158_, lean_object* v_b_159_){
_start:
{
size_t v_i_boxed_160_; size_t v_stop_boxed_161_; lean_object* v_res_162_; 
v_i_boxed_160_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_stop_boxed_161_ = lean_unbox_usize(v_stop_158_);
lean_dec(v_stop_158_);
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v_as_156_, v_i_boxed_160_, v_stop_boxed_161_, v_b_159_);
lean_dec_ref(v_as_156_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(lean_object* v_as_163_, size_t v_i_164_, size_t v_stop_165_, lean_object* v_b_166_){
_start:
{
lean_object* v___y_168_; uint8_t v___x_172_; 
v___x_172_ = lean_usize_dec_eq(v_i_164_, v_stop_165_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = lean_array_uget_borrowed(v_as_163_, v_i_164_);
v___x_175_ = lean_array_get_size(v___x_174_);
v___x_176_ = lean_nat_dec_lt(v___x_173_, v___x_175_);
if (v___x_176_ == 0)
{
v___y_168_ = v_b_166_;
goto v___jp_167_;
}
else
{
size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((size_t)0ULL);
v___x_178_ = lean_usize_of_nat(v___x_175_);
v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v___x_174_, v___x_177_, v___x_178_, v_b_166_);
v___y_168_ = v___x_179_;
goto v___jp_167_;
}
}
else
{
return v_b_166_;
}
v___jp_167_:
{
size_t v___x_169_; size_t v___x_170_; 
v___x_169_ = ((size_t)1ULL);
v___x_170_ = lean_usize_add(v_i_164_, v___x_169_);
v_i_164_ = v___x_170_;
v_b_166_ = v___y_168_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_180_, lean_object* v_i_181_, lean_object* v_stop_182_, lean_object* v_b_183_){
_start:
{
size_t v_i_boxed_184_; size_t v_stop_boxed_185_; lean_object* v_res_186_; 
v_i_boxed_184_ = lean_unbox_usize(v_i_181_);
lean_dec(v_i_181_);
v_stop_boxed_185_ = lean_unbox_usize(v_stop_182_);
lean_dec(v_stop_182_);
v_res_186_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(v_as_180_, v_i_boxed_184_, v_stop_boxed_185_, v_b_183_);
lean_dec_ref(v_as_180_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v___x_187_, lean_object* v_ess_188_, lean_object* v___y_189_){
_start:
{
lean_object* v___x_191_; lean_object* v___y_193_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___y_200_; lean_object* v___x_206_; uint8_t v___x_207_; 
v___x_191_ = lean_st_ref_get(v___x_187_);
v___x_197_ = lean_box(1);
v___x_198_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_array_get_size(v___x_191_);
v___x_207_ = lean_nat_dec_lt(v___x_198_, v___x_206_);
if (v___x_207_ == 0)
{
lean_dec(v___x_191_);
v___y_200_ = v___x_197_;
goto v___jp_199_;
}
else
{
size_t v___x_208_; size_t v___x_209_; lean_object* v___x_210_; 
v___x_208_ = ((size_t)0ULL);
v___x_209_ = lean_usize_of_nat(v___x_206_);
v___x_210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v___x_191_, v___x_208_, v___x_209_, v___x_197_);
lean_dec(v___x_191_);
v___y_200_ = v___x_210_;
goto v___jp_199_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_195_, 0, v___y_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
return v___x_196_;
}
v___jp_199_:
{
lean_object* v___x_201_; uint8_t v___x_202_; 
v___x_201_ = lean_array_get_size(v_ess_188_);
v___x_202_ = lean_nat_dec_lt(v___x_198_, v___x_201_);
if (v___x_202_ == 0)
{
v___y_193_ = v___y_200_;
goto v___jp_192_;
}
else
{
size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; 
v___x_203_ = ((size_t)0ULL);
v___x_204_ = lean_usize_of_nat(v___x_201_);
v___x_205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(v_ess_188_, v___x_203_, v___x_204_, v___y_200_);
v___y_193_ = v___x_205_;
goto v___jp_192_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v___x_211_, lean_object* v_ess_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v___x_211_, v_ess_212_, v___y_213_);
lean_dec_ref(v___y_213_);
lean_dec_ref(v_ess_212_);
lean_dec(v___x_211_);
return v_res_215_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_227_; lean_object* v___f_228_; 
v___x_227_ = l_Lean_Linter_builtinLinterSetsRef;
v___f_228_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_228_, 0, v___x_227_);
return v___f_228_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_229_; lean_object* v___f_230_; 
v___x_229_ = l_Lean_Linter_builtinLinterSetsRef;
v___f_230_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_230_, 0, v___x_229_);
return v___f_230_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_231_ = 0;
v___x_232_ = lean_box(0);
v___x_233_ = lean_box(2);
v___f_234_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_235_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_236_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_237_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___f_238_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_239_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___x_240_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___f_238_);
lean_ctor_set(v___x_240_, 2, v___f_237_);
lean_ctor_set(v___x_240_, 3, v___f_236_);
lean_ctor_set(v___x_240_, 4, v___f_235_);
lean_ctor_set(v___x_240_, 5, v___f_234_);
lean_ctor_set(v___x_240_, 6, v___x_233_);
lean_ctor_set(v___x_240_, 7, v___x_232_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*8, v___x_231_);
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*8 + 1, v___x_231_);
return v___x_240_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___f_241_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___x_242_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___f_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_246_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_();
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg(lean_object* v_inst_249_, lean_object* v_o_250_, lean_object* v_k_251_, lean_object* v_defVal_252_){
_start:
{
lean_object* v_toOptions_253_; lean_object* v_map_254_; lean_object* v_ofDataValue_x3f_255_; lean_object* v___x_256_; 
v_toOptions_253_ = lean_ctor_get(v_o_250_, 0);
v_map_254_ = lean_ctor_get(v_toOptions_253_, 0);
v_ofDataValue_x3f_255_ = lean_ctor_get(v_inst_249_, 1);
lean_inc_ref(v_ofDataValue_x3f_255_);
lean_dec_ref(v_inst_249_);
v___x_256_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_254_, v_k_251_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_255_);
lean_inc(v_defVal_252_);
return v_defVal_252_;
}
else
{
lean_object* v_val_257_; lean_object* v___x_258_; 
v_val_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_val_257_);
lean_dec_ref_known(v___x_256_, 1);
v___x_258_ = lean_apply_1(v_ofDataValue_x3f_255_, v_val_257_);
if (lean_obj_tag(v___x_258_) == 0)
{
lean_inc(v_defVal_252_);
return v_defVal_252_;
}
else
{
lean_object* v_val_259_; 
v_val_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_val_259_);
lean_dec_ref_known(v___x_258_, 1);
return v_val_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg___boxed(lean_object* v_inst_260_, lean_object* v_o_261_, lean_object* v_k_262_, lean_object* v_defVal_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Linter_LinterOptions_get___redArg(v_inst_260_, v_o_261_, v_k_262_, v_defVal_263_);
lean_dec(v_defVal_263_);
lean_dec(v_k_262_);
lean_dec_ref(v_o_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get(lean_object* v_00_u03b1_265_, lean_object* v_inst_266_, lean_object* v_o_267_, lean_object* v_k_268_, lean_object* v_defVal_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Linter_LinterOptions_get___redArg(v_inst_266_, v_o_267_, v_k_268_, v_defVal_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___boxed(lean_object* v_00_u03b1_271_, lean_object* v_inst_272_, lean_object* v_o_273_, lean_object* v_k_274_, lean_object* v_defVal_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Linter_LinterOptions_get(v_00_u03b1_271_, v_inst_272_, v_o_273_, v_k_274_, v_defVal_275_);
lean_dec(v_defVal_275_);
lean_dec(v_k_274_);
lean_dec_ref(v_o_273_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg(lean_object* v_inst_277_, lean_object* v_o_278_, lean_object* v_k_279_){
_start:
{
lean_object* v_toOptions_280_; lean_object* v_map_281_; lean_object* v_ofDataValue_x3f_282_; lean_object* v___x_283_; 
v_toOptions_280_ = lean_ctor_get(v_o_278_, 0);
v_map_281_ = lean_ctor_get(v_toOptions_280_, 0);
v_ofDataValue_x3f_282_ = lean_ctor_get(v_inst_277_, 1);
lean_inc_ref(v_ofDataValue_x3f_282_);
lean_dec_ref(v_inst_277_);
v___x_283_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_281_, v_k_279_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v___x_284_; 
lean_dec_ref(v_ofDataValue_x3f_282_);
v___x_284_ = lean_box(0);
return v___x_284_;
}
else
{
lean_object* v_val_285_; lean_object* v___x_286_; 
v_val_285_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v___x_283_, 1);
v___x_286_ = lean_apply_1(v_ofDataValue_x3f_282_, v_val_285_);
return v___x_286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg___boxed(lean_object* v_inst_287_, lean_object* v_o_288_, lean_object* v_k_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_287_, v_o_288_, v_k_289_);
lean_dec(v_k_289_);
lean_dec_ref(v_o_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f(lean_object* v_00_u03b1_291_, lean_object* v_inst_292_, lean_object* v_o_293_, lean_object* v_k_294_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_292_, v_o_293_, v_k_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___boxed(lean_object* v_00_u03b1_296_, lean_object* v_inst_297_, lean_object* v_o_298_, lean_object* v_k_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Linter_LinterOptions_get_x3f(v_00_u03b1_296_, v_inst_297_, v_o_298_, v_k_299_);
lean_dec(v_k_299_);
lean_dec_ref(v_o_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg___lam__0(lean_object* v___x_301_, lean_object* v_o_302_, lean_object* v_toPure_303_, lean_object* v_____do__lift_304_){
_start:
{
lean_object* v___x_305_; lean_object* v_toEnvExtension_306_; lean_object* v_asyncMode_307_; lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; lean_object* v_merged_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_319_; 
v___x_305_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_306_ = lean_ctor_get(v___x_305_, 0);
v_asyncMode_307_ = lean_ctor_get(v_toEnvExtension_306_, 2);
v___x_308_ = lean_box(0);
v___x_309_ = 0;
v___x_310_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_301_, v___x_305_, v_____do__lift_304_, v_asyncMode_307_, v___x_308_, v___x_309_);
v_merged_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v___x_310_, 1);
lean_dec(v_unused_320_);
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_merged_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v_merged_311_);
lean_ctor_set(v___x_313_, 0, v_o_302_);
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_o_302_);
lean_ctor_set(v_reuseFailAlloc_318_, 1, v_merged_311_);
v___x_316_ = v_reuseFailAlloc_318_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; 
v___x_317_ = lean_apply_2(v_toPure_303_, lean_box(0), v___x_316_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg(lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_o_323_){
_start:
{
lean_object* v_toApplicative_324_; lean_object* v_toBind_325_; lean_object* v_getEnv_326_; lean_object* v_toPure_327_; lean_object* v___x_328_; lean_object* v___f_329_; lean_object* v___x_330_; 
v_toApplicative_324_ = lean_ctor_get(v_inst_321_, 0);
lean_inc_ref(v_toApplicative_324_);
v_toBind_325_ = lean_ctor_get(v_inst_321_, 1);
lean_inc(v_toBind_325_);
lean_dec_ref(v_inst_321_);
v_getEnv_326_ = lean_ctor_get(v_inst_322_, 0);
lean_inc(v_getEnv_326_);
lean_dec_ref(v_inst_322_);
v_toPure_327_ = lean_ctor_get(v_toApplicative_324_, 1);
lean_inc(v_toPure_327_);
lean_dec_ref(v_toApplicative_324_);
v___x_328_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default));
v___f_329_ = lean_alloc_closure((void*)(l_Lean_Options_toLinterOptions___redArg___lam__0), 4, 3);
lean_closure_set(v___f_329_, 0, v___x_328_);
lean_closure_set(v___f_329_, 1, v_o_323_);
lean_closure_set(v___f_329_, 2, v_toPure_327_);
v___x_330_ = lean_apply_4(v_toBind_325_, lean_box(0), lean_box(0), v_getEnv_326_, v___f_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions(lean_object* v_m_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_o_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Options_toLinterOptions___redArg(v_inst_332_, v_inst_333_, v_o_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg(lean_object* v_o_336_, lean_object* v_opt_337_){
_start:
{
lean_object* v_linterSets_338_; lean_object* v_name_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_linterSets_338_ = lean_ctor_get(v_o_336_, 1);
v_name_339_ = lean_ctor_get(v_opt_337_, 0);
v___x_340_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_341_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_linterSets_338_, v_name_339_, v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg___boxed(lean_object* v_o_342_, lean_object* v_opt_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_342_, v_opt_343_);
lean_dec_ref(v_opt_343_);
lean_dec_ref(v_o_342_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet(lean_object* v_00_u03b1_345_, lean_object* v_o_346_, lean_object* v_opt_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_346_, v_opt_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___boxed(lean_object* v_00_u03b1_349_, lean_object* v_o_350_, lean_object* v_opt_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Linter_LinterOptions_getSet(v_00_u03b1_349_, v_o_350_, v_opt_351_);
lean_dec_ref(v_opt_351_);
lean_dec_ref(v_o_350_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg___lam__0(lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_____do__lift_355_){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Options_toLinterOptions___redArg(v_inst_353_, v_inst_354_, v_____do__lift_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg(lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_){
_start:
{
lean_object* v_toBind_360_; lean_object* v_getOptions_361_; lean_object* v___f_362_; lean_object* v___x_363_; 
v_toBind_360_ = lean_ctor_get(v_inst_357_, 1);
lean_inc(v_toBind_360_);
v_getOptions_361_ = lean_ctor_get(v_inst_358_, 0);
lean_inc(v_getOptions_361_);
lean_dec_ref(v_inst_358_);
v___f_362_ = lean_alloc_closure((void*)(l_Lean_Linter_getLinterOptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_362_, 0, v_inst_357_);
lean_closure_set(v___f_362_, 1, v_inst_359_);
v___x_363_ = lean_apply_4(v_toBind_360_, lean_box(0), lean_box(0), v_getOptions_361_, v___f_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions(lean_object* v_m_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_365_, v_inst_366_, v_inst_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(lean_object* v_name_369_, lean_object* v_decl_370_, lean_object* v_ref_371_){
_start:
{
lean_object* v_defValue_373_; lean_object* v_descr_374_; lean_object* v_deprecation_x3f_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v_defValue_373_ = lean_ctor_get(v_decl_370_, 0);
v_descr_374_ = lean_ctor_get(v_decl_370_, 1);
v_deprecation_x3f_375_ = lean_ctor_get(v_decl_370_, 2);
v___x_376_ = lean_alloc_ctor(1, 0, 1);
v___x_377_ = lean_unbox(v_defValue_373_);
lean_ctor_set_uint8(v___x_376_, 0, v___x_377_);
lean_inc(v_deprecation_x3f_375_);
lean_inc_ref(v_descr_374_);
lean_inc_n(v_name_369_, 2);
v___x_378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_378_, 0, v_name_369_);
lean_ctor_set(v___x_378_, 1, v_ref_371_);
lean_ctor_set(v___x_378_, 2, v___x_376_);
lean_ctor_set(v___x_378_, 3, v_descr_374_);
lean_ctor_set(v___x_378_, 4, v_deprecation_x3f_375_);
v___x_379_ = lean_register_option(v_name_369_, v___x_378_);
if (lean_obj_tag(v___x_379_) == 0)
{
lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_387_; 
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v___x_379_, 0);
lean_dec(v_unused_388_);
v___x_381_ = v___x_379_;
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
else
{
lean_dec(v___x_379_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_385_; 
lean_inc(v_defValue_373_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v_name_369_);
lean_ctor_set(v___x_383_, 1, v_defValue_373_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_383_);
v___x_385_ = v___x_381_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v_name_369_);
v_a_389_ = lean_ctor_get(v___x_379_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_379_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_379_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_379_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_397_, lean_object* v_decl_398_, lean_object* v_ref_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v_name_397_, v_decl_398_, v_ref_399_);
lean_dec_ref(v_decl_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_420_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_421_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_422_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_419_, v___x_420_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4____boxed(lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_();
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_442_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_443_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_444_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_441_, v___x_442_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4____boxed(lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_();
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_463_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_464_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_465_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_466_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_463_, v___x_464_, v___x_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4____boxed(lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_();
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_));
v___x_473_ = lean_st_mk_ref(v___x_472_);
v___x_474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2____boxed(lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_();
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_addEnvLinterOption(lean_object* v_opt_477_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_479_ = l_Lean_Linter_envLinterOptionsRef;
v___x_480_ = lean_st_ref_take(v___x_479_);
v___x_481_ = lean_array_push(v___x_480_, v_opt_477_);
v___x_482_ = lean_st_ref_put(v___x_479_, v___x_481_);
v___x_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_addEnvLinterOption___boxed(lean_object* v_opt_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Linter_addEnvLinterOption(v_opt_484_);
return v_res_486_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(lean_object* v_o_487_, lean_object* v_k_488_, uint8_t v_defVal_489_){
_start:
{
lean_object* v_toOptions_490_; lean_object* v_map_491_; lean_object* v___x_492_; 
v_toOptions_490_ = lean_ctor_get(v_o_487_, 0);
v_map_491_ = lean_ctor_get(v_toOptions_490_, 0);
v___x_492_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_491_, v_k_488_);
if (lean_obj_tag(v___x_492_) == 0)
{
return v_defVal_489_;
}
else
{
lean_object* v_val_493_; 
v_val_493_ = lean_ctor_get(v___x_492_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v___x_492_, 1);
if (lean_obj_tag(v_val_493_) == 1)
{
uint8_t v_v_494_; 
v_v_494_ = lean_ctor_get_uint8(v_val_493_, 0);
lean_dec_ref_known(v_val_493_, 0);
return v_v_494_;
}
else
{
lean_dec(v_val_493_);
return v_defVal_489_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0___boxed(lean_object* v_o_495_, lean_object* v_k_496_, lean_object* v_defVal_497_){
_start:
{
uint8_t v_defVal_boxed_498_; uint8_t v_res_499_; lean_object* v_r_500_; 
v_defVal_boxed_498_ = lean_unbox(v_defVal_497_);
v_res_499_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_495_, v_k_496_, v_defVal_boxed_498_);
lean_dec(v_k_496_);
lean_dec_ref(v_o_495_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterAll(lean_object* v_o_501_, uint8_t v_defValue_502_){
_start:
{
lean_object* v___x_503_; lean_object* v_name_504_; uint8_t v___x_505_; 
v___x_503_ = l_Lean_Linter_linter_all;
v_name_504_ = lean_ctor_get(v___x_503_, 0);
v___x_505_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_501_, v_name_504_, v_defValue_502_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterAll___boxed(lean_object* v_o_506_, lean_object* v_defValue_507_){
_start:
{
uint8_t v_defValue_boxed_508_; uint8_t v_res_509_; lean_object* v_r_510_; 
v_defValue_boxed_508_ = lean_unbox(v_defValue_507_);
v_res_509_ = l_Lean_Linter_getLinterAll(v_o_506_, v_defValue_boxed_508_);
lean_dec_ref(v_o_506_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(lean_object* v_o_511_, lean_object* v_k_512_){
_start:
{
lean_object* v_toOptions_513_; lean_object* v_map_514_; lean_object* v___x_515_; 
v_toOptions_513_ = lean_ctor_get(v_o_511_, 0);
v_map_514_ = lean_ctor_get(v_toOptions_513_, 0);
v___x_515_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_514_, v_k_512_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_box(0);
return v___x_516_;
}
else
{
lean_object* v_val_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_527_; 
v_val_517_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_527_ == 0)
{
v___x_519_ = v___x_515_;
v_isShared_520_ = v_isSharedCheck_527_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_val_517_);
lean_dec(v___x_515_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_527_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
if (lean_obj_tag(v_val_517_) == 1)
{
uint8_t v_v_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v_v_521_ = lean_ctor_get_uint8(v_val_517_, 0);
lean_dec_ref_known(v_val_517_, 0);
v___x_522_ = lean_box(v_v_521_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_522_);
v___x_524_ = v___x_519_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_object* v___x_526_; 
lean_del_object(v___x_519_);
lean_dec(v_val_517_);
v___x_526_ = lean_box(0);
return v___x_526_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0___boxed(lean_object* v_o_528_, lean_object* v_k_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_528_, v_k_529_);
lean_dec(v_k_529_);
lean_dec_ref(v_o_528_);
return v_res_530_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
if (lean_obj_tag(v_x_532_) == 0)
{
uint8_t v___x_533_; 
v___x_533_ = 1;
return v___x_533_;
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
if (lean_obj_tag(v_x_532_) == 0)
{
uint8_t v___x_535_; 
v___x_535_ = 0;
return v___x_535_;
}
else
{
lean_object* v_val_536_; uint8_t v___x_537_; 
v_val_536_ = lean_ctor_get(v_x_532_, 0);
v___x_537_ = lean_unbox(v_val_536_);
if (v___x_537_ == 0)
{
lean_object* v_val_538_; uint8_t v___x_539_; 
v_val_538_ = lean_ctor_get(v_x_531_, 0);
v___x_539_ = lean_unbox(v_val_538_);
if (v___x_539_ == 0)
{
uint8_t v___x_540_; 
v___x_540_ = 1;
return v___x_540_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = lean_unbox(v_val_536_);
return v___x_541_;
}
}
else
{
lean_object* v_val_542_; uint8_t v___x_543_; 
v_val_542_ = lean_ctor_get(v_x_531_, 0);
v___x_543_ = lean_unbox(v_val_542_);
return v___x_543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1___boxed(lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
uint8_t v_res_546_; lean_object* v_r_547_; 
v_res_546_ = l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(v_x_544_, v_x_545_);
lean_dec(v_x_545_);
lean_dec(v_x_544_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(lean_object* v_o_551_, lean_object* v_as_552_, size_t v_i_553_, size_t v_stop_554_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = lean_usize_dec_eq(v_i_553_, v_stop_554_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_556_ = 1;
v___x_557_ = lean_array_uget_borrowed(v_as_552_, v_i_553_);
v___x_558_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_551_, v___x_557_);
v___x_559_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0));
v___x_560_ = l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(v___x_558_, v___x_559_);
lean_dec(v___x_558_);
if (v___x_560_ == 0)
{
size_t v___x_561_; size_t v___x_562_; 
v___x_561_ = ((size_t)1ULL);
v___x_562_ = lean_usize_add(v_i_553_, v___x_561_);
v_i_553_ = v___x_562_;
goto _start;
}
else
{
return v___x_556_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___boxed(lean_object* v_o_565_, lean_object* v_as_566_, lean_object* v_i_567_, lean_object* v_stop_568_){
_start:
{
size_t v_i_boxed_569_; size_t v_stop_boxed_570_; uint8_t v_res_571_; lean_object* v_r_572_; 
v_i_boxed_569_ = lean_unbox_usize(v_i_567_);
lean_dec(v_i_567_);
v_stop_boxed_570_ = lean_unbox_usize(v_stop_568_);
lean_dec(v_stop_568_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_565_, v_as_566_, v_i_boxed_569_, v_stop_boxed_570_);
lean_dec_ref(v_as_566_);
lean_dec_ref(v_o_565_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterValue(lean_object* v_opt_573_, lean_object* v_o_574_){
_start:
{
lean_object* v_name_575_; lean_object* v_defValue_576_; uint8_t v___y_578_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v_name_575_ = lean_ctor_get(v_opt_573_, 0);
v_defValue_576_ = lean_ctor_get(v_opt_573_, 1);
v___x_581_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_574_, v_opt_573_);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_array_get_size(v___x_581_);
v___x_584_ = lean_nat_dec_lt(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
uint8_t v___x_585_; 
lean_dec(v___x_581_);
v___x_585_ = lean_unbox(v_defValue_576_);
v___y_578_ = v___x_585_;
goto v___jp_577_;
}
else
{
if (v___x_584_ == 0)
{
uint8_t v___x_586_; 
lean_dec(v___x_581_);
v___x_586_ = lean_unbox(v_defValue_576_);
v___y_578_ = v___x_586_;
goto v___jp_577_;
}
else
{
size_t v___x_587_; size_t v___x_588_; uint8_t v___x_589_; 
v___x_587_ = ((size_t)0ULL);
v___x_588_ = lean_usize_of_nat(v___x_583_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_574_, v___x_581_, v___x_587_, v___x_588_);
lean_dec(v___x_581_);
if (v___x_589_ == 0)
{
uint8_t v___x_590_; 
v___x_590_ = lean_unbox(v_defValue_576_);
v___y_578_ = v___x_590_;
goto v___jp_577_;
}
else
{
v___y_578_ = v___x_589_;
goto v___jp_577_;
}
}
}
v___jp_577_:
{
uint8_t v___x_579_; uint8_t v___x_580_; 
v___x_579_ = l_Lean_Linter_getLinterAll(v_o_574_, v___y_578_);
v___x_580_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_574_, v_name_575_, v___x_579_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterValue___boxed(lean_object* v_opt_591_, lean_object* v_o_592_){
_start:
{
uint8_t v_res_593_; lean_object* v_r_594_; 
v_res_593_ = l_Lean_Linter_getLinterValue(v_opt_591_, v_o_592_);
lean_dec_ref(v_o_592_);
lean_dec_ref(v_opt_591_);
v_r_594_ = lean_box(v_res_593_);
return v_r_594_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object* v_name_595_, lean_object* v_o_596_){
_start:
{
uint8_t v___y_598_; lean_object* v_linterSets_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_linterSets_601_ = lean_ctor_get(v_o_596_, 1);
v___x_602_ = lean_unsigned_to_nat(0u);
v___x_603_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_604_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_linterSets_601_, v_name_595_, v___x_603_);
v___x_605_ = lean_array_get_size(v___x_604_);
v___x_606_ = lean_nat_dec_lt(v___x_602_, v___x_605_);
if (v___x_606_ == 0)
{
lean_dec(v___x_604_);
v___y_598_ = v___x_606_;
goto v___jp_597_;
}
else
{
if (v___x_606_ == 0)
{
lean_dec(v___x_604_);
v___y_598_ = v___x_606_;
goto v___jp_597_;
}
else
{
size_t v___x_607_; size_t v___x_608_; uint8_t v___x_609_; 
v___x_607_ = ((size_t)0ULL);
v___x_608_ = lean_usize_of_nat(v___x_605_);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_596_, v___x_604_, v___x_607_, v___x_608_);
lean_dec(v___x_604_);
v___y_598_ = v___x_609_;
goto v___jp_597_;
}
}
v___jp_597_:
{
uint8_t v___x_599_; uint8_t v___x_600_; 
v___x_599_ = l_Lean_Linter_getLinterAll(v_o_596_, v___y_598_);
v___x_600_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_596_, v_name_595_, v___x_599_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isLinterEnabledByOptions___boxed(lean_object* v_name_610_, lean_object* v_o_611_){
_start:
{
uint8_t v_res_612_; lean_object* v_r_613_; 
v_res_612_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_610_, v_o_611_);
lean_dec_ref(v_o_611_);
lean_dec(v_name_610_);
v_r_613_ = lean_box(v_res_612_);
return v_r_613_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___redArg___closed__1(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Linter_logLint___redArg___closed__0));
v___x_622_ = l_Lean_stringToMessageData(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___redArg___closed__3(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_Linter_logLint___redArg___closed__2));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___redArg(lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_inst_629_, lean_object* v_linterOption_630_, lean_object* v_stx_631_, lean_object* v_msg_632_){
_start:
{
lean_object* v_name_633_; lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_651_; 
v_name_633_ = lean_ctor_get(v_linterOption_630_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v_linterOption_630_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v_linterOption_630_, 1);
lean_dec(v_unused_652_);
v___x_635_ = v_linterOption_630_;
v_isShared_636_ = v_isSharedCheck_651_;
goto v_resetjp_634_;
}
else
{
lean_inc(v_name_633_);
lean_dec(v_linterOption_630_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_651_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_637_ = lean_obj_once(&l_Lean_Linter_logLint___redArg___closed__1, &l_Lean_Linter_logLint___redArg___closed__1_once, _init_l_Lean_Linter_logLint___redArg___closed__1);
lean_inc(v_name_633_);
v___x_638_ = l_Lean_MessageData_ofName(v_name_633_);
if (v_isShared_636_ == 0)
{
lean_ctor_set_tag(v___x_635_, 7);
lean_ctor_set(v___x_635_, 1, v___x_638_);
lean_ctor_set(v___x_635_, 0, v___x_637_);
v___x_640_ = v___x_635_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_638_);
v___x_640_ = v_reuseFailAlloc_650_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v_disable_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_641_ = lean_obj_once(&l_Lean_Linter_logLint___redArg___closed__3, &l_Lean_Linter_logLint___redArg___closed__3_once, _init_l_Lean_Linter_logLint___redArg___closed__3);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v_disable_643_ = l_Lean_MessageData_note(v___x_642_);
v___x_644_ = ((lean_object*)(l_Lean_Linter_linterMessageTag));
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v_msg_632_);
lean_ctor_set(v___x_645_, 1, v_disable_643_);
v___x_646_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_647_, 0, v_name_633_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
lean_inc(v_stx_631_);
v___x_648_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_648_, 0, v_stx_631_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_logWarningAt___redArg(v_inst_626_, v_inst_627_, v_inst_628_, v_inst_629_, v_stx_631_, v___x_648_);
return v___x_649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint(lean_object* v_m_653_, lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_inst_657_, lean_object* v_linterOption_658_, lean_object* v_stx_659_, lean_object* v_msg_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_Linter_logLint___redArg(v_inst_654_, v_inst_655_, v_inst_656_, v_inst_657_, v_linterOption_658_, v_stx_659_, v_msg_660_);
return v___x_661_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isLinterMessage___lam__0(lean_object* v_x_662_){
_start:
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = ((lean_object*)(l_Lean_Linter_linterMessageTag));
v___x_664_ = lean_name_eq(v_x_662_, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isLinterMessage___lam__0___boxed(lean_object* v_x_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l_Lean_MessageData_isLinterMessage___lam__0(v_x_665_);
lean_dec(v_x_665_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isLinterMessage(lean_object* v_msg_669_){
_start:
{
lean_object* v___f_670_; uint8_t v___x_671_; 
v___f_670_ = ((lean_object*)(l_Lean_MessageData_isLinterMessage___closed__0));
v___x_671_ = l_Lean_MessageData_hasTag(v___f_670_, v_msg_669_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isLinterMessage___boxed(lean_object* v_msg_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_MessageData_isLinterMessage(v_msg_672_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0(lean_object* v_linterOption_675_, lean_object* v_toPure_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_stx_681_, lean_object* v_msg_682_, lean_object* v_____do__lift_683_){
_start:
{
uint8_t v___x_684_; 
v___x_684_ = l_Lean_Linter_getLinterValue(v_linterOption_675_, v_____do__lift_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; 
lean_dec_ref(v_msg_682_);
lean_dec(v_stx_681_);
lean_dec_ref(v_inst_680_);
lean_dec(v_inst_679_);
lean_dec_ref(v_inst_678_);
lean_dec_ref(v_inst_677_);
lean_dec_ref(v_linterOption_675_);
v___x_685_ = lean_box(0);
v___x_686_ = lean_apply_2(v_toPure_676_, lean_box(0), v___x_685_);
return v___x_686_;
}
else
{
lean_object* v___x_687_; 
lean_dec(v_toPure_676_);
v___x_687_ = l_Lean_Linter_logLint___redArg(v_inst_677_, v_inst_678_, v_inst_679_, v_inst_680_, v_linterOption_675_, v_stx_681_, v_msg_682_);
return v___x_687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0___boxed(lean_object* v_linterOption_688_, lean_object* v_toPure_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_stx_694_, lean_object* v_msg_695_, lean_object* v_____do__lift_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Linter_logLintIf___redArg___lam__0(v_linterOption_688_, v_toPure_689_, v_inst_690_, v_inst_691_, v_inst_692_, v_inst_693_, v_stx_694_, v_msg_695_, v_____do__lift_696_);
lean_dec_ref(v_____do__lift_696_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg(lean_object* v_inst_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_linterOption_703_, lean_object* v_stx_704_, lean_object* v_msg_705_){
_start:
{
lean_object* v_toApplicative_706_; lean_object* v_toBind_707_; lean_object* v_toPure_708_; lean_object* v___x_709_; lean_object* v___f_710_; lean_object* v___x_711_; 
v_toApplicative_706_ = lean_ctor_get(v_inst_698_, 0);
v_toBind_707_ = lean_ctor_get(v_inst_698_, 1);
lean_inc(v_toBind_707_);
v_toPure_708_ = lean_ctor_get(v_toApplicative_706_, 1);
lean_inc(v_toPure_708_);
lean_inc_ref(v_inst_701_);
lean_inc_ref(v_inst_698_);
v___x_709_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_698_, v_inst_701_, v_inst_702_);
v___f_710_ = lean_alloc_closure((void*)(l_Lean_Linter_logLintIf___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_710_, 0, v_linterOption_703_);
lean_closure_set(v___f_710_, 1, v_toPure_708_);
lean_closure_set(v___f_710_, 2, v_inst_698_);
lean_closure_set(v___f_710_, 3, v_inst_699_);
lean_closure_set(v___f_710_, 4, v_inst_700_);
lean_closure_set(v___f_710_, 5, v_inst_701_);
lean_closure_set(v___f_710_, 6, v_stx_704_);
lean_closure_set(v___f_710_, 7, v_msg_705_);
v___x_711_ = lean_apply_4(v_toBind_707_, lean_box(0), lean_box(0), v___x_709_, v___f_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf(lean_object* v_m_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_linterOption_718_, lean_object* v_stx_719_, lean_object* v_msg_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_Linter_logLintIf___redArg(v_inst_713_, v_inst_714_, v_inst_715_, v_inst_716_, v_inst_717_, v_linterOption_718_, v_stx_719_, v_msg_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2(lean_object* v_env_722_, lean_object* v_as_723_, size_t v_i_724_, size_t v_stop_725_, lean_object* v_b_726_){
_start:
{
lean_object* v___y_728_; uint8_t v___x_732_; 
v___x_732_ = lean_usize_dec_eq(v_i_724_, v_stop_725_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v_fst_734_; uint8_t v___x_735_; 
v___x_733_ = lean_array_uget_borrowed(v_as_723_, v_i_724_);
v_fst_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_fst_734_);
lean_inc_ref(v_env_722_);
v___x_735_ = l_Lean_Environment_contains(v_env_722_, v_fst_734_, v___x_732_);
if (v___x_735_ == 0)
{
v___y_728_ = v_b_726_;
goto v___jp_727_;
}
else
{
lean_object* v___x_736_; 
lean_inc(v___x_733_);
v___x_736_ = lean_array_push(v_b_726_, v___x_733_);
v___y_728_ = v___x_736_;
goto v___jp_727_;
}
}
else
{
lean_dec_ref(v_env_722_);
return v_b_726_;
}
v___jp_727_:
{
size_t v___x_729_; size_t v___x_730_; 
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_i_724_, v___x_729_);
v_i_724_ = v___x_730_;
v_b_726_ = v___y_728_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_737_, lean_object* v_as_738_, lean_object* v_i_739_, lean_object* v_stop_740_, lean_object* v_b_741_){
_start:
{
size_t v_i_boxed_742_; size_t v_stop_boxed_743_; lean_object* v_res_744_; 
v_i_boxed_742_ = lean_unbox_usize(v_i_739_);
lean_dec(v_i_739_);
v_stop_boxed_743_ = lean_unbox_usize(v_stop_740_);
lean_dec(v_stop_740_);
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2(v_env_737_, v_as_738_, v_i_boxed_742_, v_stop_boxed_743_, v_b_741_);
lean_dec_ref(v_as_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_745_, lean_object* v_x_746_){
_start:
{
if (lean_obj_tag(v_x_746_) == 0)
{
lean_object* v_k_747_; lean_object* v_v_748_; lean_object* v_l_749_; lean_object* v_r_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_k_747_ = lean_ctor_get(v_x_746_, 1);
v_v_748_ = lean_ctor_get(v_x_746_, 2);
v_l_749_ = lean_ctor_get(v_x_746_, 3);
v_r_750_ = lean_ctor_get(v_x_746_, 4);
v___x_751_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_745_, v_l_749_);
lean_inc(v_v_748_);
lean_inc(v_k_747_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_k_747_);
lean_ctor_set(v___x_752_, 1, v_v_748_);
v___x_753_ = lean_array_push(v___x_751_, v___x_752_);
v_init_745_ = v___x_753_;
v_x_746_ = v_r_750_;
goto _start;
}
else
{
return v_init_745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_755_, lean_object* v_x_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_755_, v_x_756_);
lean_dec(v_x_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(lean_object* v_env_758_, lean_object* v_as_759_, size_t v_i_760_, size_t v_stop_761_, lean_object* v_b_762_){
_start:
{
lean_object* v___y_764_; uint8_t v___x_768_; 
v___x_768_ = lean_usize_dec_eq(v_i_760_, v_stop_761_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v_fst_770_; uint8_t v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_769_ = lean_array_uget_borrowed(v_as_759_, v_i_760_);
v_fst_770_ = lean_ctor_get(v___x_769_, 0);
v___x_771_ = 1;
lean_inc_ref(v_env_758_);
v___x_772_ = l_Lean_Environment_setExporting(v_env_758_, v___x_771_);
lean_inc(v_fst_770_);
v___x_773_ = l_Lean_Environment_contains(v___x_772_, v_fst_770_, v___x_768_);
if (v___x_773_ == 0)
{
v___y_764_ = v_b_762_;
goto v___jp_763_;
}
else
{
lean_object* v___x_774_; 
lean_inc(v___x_769_);
v___x_774_ = lean_array_push(v_b_762_, v___x_769_);
v___y_764_ = v___x_774_;
goto v___jp_763_;
}
}
else
{
lean_dec_ref(v_env_758_);
return v_b_762_;
}
v___jp_763_:
{
size_t v___x_765_; size_t v___x_766_; 
v___x_765_ = ((size_t)1ULL);
v___x_766_ = lean_usize_add(v_i_760_, v___x_765_);
v_i_760_ = v___x_766_;
v_b_762_ = v___y_764_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_775_, lean_object* v_as_776_, lean_object* v_i_777_, lean_object* v_stop_778_, lean_object* v_b_779_){
_start:
{
size_t v_i_boxed_780_; size_t v_stop_boxed_781_; lean_object* v_res_782_; 
v_i_boxed_780_ = lean_unbox_usize(v_i_777_);
lean_dec(v_i_777_);
v_stop_boxed_781_ = lean_unbox_usize(v_stop_778_);
lean_dec(v_stop_778_);
v_res_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_775_, v_as_776_, v_i_boxed_780_, v_stop_boxed_781_, v_b_779_);
lean_dec_ref(v_as_776_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(lean_object* v_env_785_, lean_object* v_s_786_){
_start:
{
lean_object* v___x_787_; lean_object* v___y_789_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_798_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_799_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v___x_798_, v_s_786_);
v___x_800_ = lean_array_get_size(v___x_799_);
v___x_801_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_802_ = lean_nat_dec_lt(v___x_787_, v___x_800_);
if (v___x_802_ == 0)
{
lean_dec_ref(v___x_799_);
v___y_789_ = v___x_801_;
goto v___jp_788_;
}
else
{
size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
v___x_803_ = ((size_t)0ULL);
v___x_804_ = lean_usize_of_nat(v___x_800_);
lean_inc_ref(v_env_785_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__2(v_env_785_, v___x_799_, v___x_803_, v___x_804_, v___x_801_);
lean_dec_ref(v___x_799_);
v___y_789_ = v___x_805_;
goto v___jp_788_;
}
v___jp_788_:
{
lean_object* v___x_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v___x_790_ = lean_array_get_size(v___y_789_);
v___x_791_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_792_ = lean_nat_dec_lt(v___x_787_, v___x_790_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; 
lean_dec_ref(v_env_785_);
v___x_793_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_793_, 0, v___x_791_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
lean_ctor_set(v___x_793_, 2, v___y_789_);
return v___x_793_;
}
else
{
size_t v___x_794_; size_t v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_794_ = ((size_t)0ULL);
v___x_795_ = lean_usize_of_nat(v___x_790_);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_785_, v___y_789_, v___x_794_, v___x_795_, v___x_791_);
lean_inc_ref(v___x_796_);
v___x_797_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
lean_ctor_set(v___x_797_, 2, v___y_789_);
return v___x_797_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed(lean_object* v_env_806_, lean_object* v_s_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(v_env_806_, v_s_807_);
lean_dec(v_s_807_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_814_; lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; lean_object* v___x_818_; 
v___f_814_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_815_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_816_ = lean_box(0);
v___x_817_ = 0;
v___x_818_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_815_, v___x_816_, v___x_817_, v___f_814_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed(lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_();
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0(lean_object* v_init_821_, lean_object* v_t_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_821_, v_t_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_824_, lean_object* v_t_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0(v_init_824_, v_t_825_);
lean_dec(v_t_825_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(lean_object* v_env_827_, lean_object* v_declName_828_, lean_object* v_optName_829_){
_start:
{
lean_object* v___x_830_; lean_object* v_toEnvExtension_831_; lean_object* v_asyncMode_832_; lean_object* v___x_833_; uint8_t v___x_834_; lean_object* v___x_835_; 
v___x_830_ = l_Lean_Linter_envLinterSnapshotExt;
v_toEnvExtension_831_ = lean_ctor_get(v___x_830_, 0);
v_asyncMode_832_ = lean_ctor_get(v_toEnvExtension_831_, 2);
v___x_833_ = lean_box(1);
v___x_834_ = 0;
v___x_835_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_833_, v___x_830_, v_env_827_, v_declName_828_, v_asyncMode_832_, v___x_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_836_; 
v___x_836_ = lean_box(0);
return v___x_836_;
}
else
{
lean_object* v_val_837_; lean_object* v___x_838_; 
v_val_837_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_val_837_);
lean_dec_ref_known(v___x_835_, 1);
v___x_838_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_837_, v_optName_829_);
lean_dec(v_val_837_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f___boxed(lean_object* v_env_839_, lean_object* v_declName_840_, lean_object* v_optName_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(v_env_839_, v_declName_840_, v_optName_841_);
lean_dec(v_optName_841_);
return v_res_842_;
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
