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
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0_value),((lean_object*)&l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0_value),((lean_object*)&l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0_value)}};
static const lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__value;
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
uint8_t v___x_138_; 
v___x_138_ = lean_nat_dec_le(v___x_136_, v___x_136_);
if (v___x_138_ == 0)
{
if (v___x_137_ == 0)
{
lean_dec(v___x_128_);
v___y_130_ = v___x_134_;
goto v___jp_129_;
}
else
{
size_t v___x_139_; size_t v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((size_t)0ULL);
v___x_140_ = lean_usize_of_nat(v___x_136_);
v___x_141_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v___x_128_, v___x_139_, v___x_140_, v___x_134_);
lean_dec(v___x_128_);
v___y_130_ = v___x_141_;
goto v___jp_129_;
}
}
else
{
size_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; 
v___x_142_ = ((size_t)0ULL);
v___x_143_ = lean_usize_of_nat(v___x_136_);
v___x_144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v___x_128_, v___x_142_, v___x_143_, v___x_134_);
lean_dec(v___x_128_);
v___y_130_ = v___x_144_;
goto v___jp_129_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v___x_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v___x_145_);
lean_dec(v___x_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(lean_object* v_as_148_, size_t v_i_149_, size_t v_stop_150_, lean_object* v_b_151_){
_start:
{
uint8_t v___x_152_; 
v___x_152_ = lean_usize_dec_eq(v_i_149_, v_stop_150_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v_fst_154_; lean_object* v_snd_155_; lean_object* v___x_156_; size_t v___x_157_; size_t v___x_158_; lean_object* v___x_159_; 
v___x_153_ = lean_array_uget_borrowed(v_as_148_, v_i_149_);
v_fst_154_ = lean_ctor_get(v___x_153_, 0);
v_snd_155_ = lean_ctor_get(v___x_153_, 1);
lean_inc(v_snd_155_);
lean_inc(v_fst_154_);
v___x_156_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_154_, v_b_151_, v_snd_155_);
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_add(v_i_149_, v___x_157_);
v___x_159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__2(v_as_148_, v___x_158_, v_stop_150_, v___x_156_);
return v___x_159_;
}
else
{
return v_b_151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_160_, lean_object* v_i_161_, lean_object* v_stop_162_, lean_object* v_b_163_){
_start:
{
size_t v_i_boxed_164_; size_t v_stop_boxed_165_; lean_object* v_res_166_; 
v_i_boxed_164_ = lean_unbox_usize(v_i_161_);
lean_dec(v_i_161_);
v_stop_boxed_165_ = lean_unbox_usize(v_stop_162_);
lean_dec(v_stop_162_);
v_res_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v_as_160_, v_i_boxed_164_, v_stop_boxed_165_, v_b_163_);
lean_dec_ref(v_as_160_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(lean_object* v_as_167_, size_t v_i_168_, size_t v_stop_169_, lean_object* v_b_170_){
_start:
{
lean_object* v___y_172_; uint8_t v___x_176_; 
v___x_176_ = lean_usize_dec_eq(v_i_168_, v_stop_169_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_array_uget_borrowed(v_as_167_, v_i_168_);
v___x_179_ = lean_array_get_size(v___x_178_);
v___x_180_ = lean_nat_dec_lt(v___x_177_, v___x_179_);
if (v___x_180_ == 0)
{
v___y_172_ = v_b_170_;
goto v___jp_171_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = lean_nat_dec_le(v___x_179_, v___x_179_);
if (v___x_181_ == 0)
{
if (v___x_180_ == 0)
{
v___y_172_ = v_b_170_;
goto v___jp_171_;
}
else
{
size_t v___x_182_; size_t v___x_183_; lean_object* v___x_184_; 
v___x_182_ = ((size_t)0ULL);
v___x_183_ = lean_usize_of_nat(v___x_179_);
v___x_184_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v___x_178_, v___x_182_, v___x_183_, v_b_170_);
v___y_172_ = v___x_184_;
goto v___jp_171_;
}
}
else
{
size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; 
v___x_185_ = ((size_t)0ULL);
v___x_186_ = lean_usize_of_nat(v___x_179_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v___x_178_, v___x_185_, v___x_186_, v_b_170_);
v___y_172_ = v___x_187_;
goto v___jp_171_;
}
}
}
else
{
return v_b_170_;
}
v___jp_171_:
{
size_t v___x_173_; size_t v___x_174_; 
v___x_173_ = ((size_t)1ULL);
v___x_174_ = lean_usize_add(v_i_168_, v___x_173_);
v_i_168_ = v___x_174_;
v_b_170_ = v___y_172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_188_, lean_object* v_i_189_, lean_object* v_stop_190_, lean_object* v_b_191_){
_start:
{
size_t v_i_boxed_192_; size_t v_stop_boxed_193_; lean_object* v_res_194_; 
v_i_boxed_192_ = lean_unbox_usize(v_i_189_);
lean_dec(v_i_189_);
v_stop_boxed_193_ = lean_unbox_usize(v_stop_190_);
lean_dec(v_stop_190_);
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(v_as_188_, v_i_boxed_192_, v_stop_boxed_193_, v_b_191_);
lean_dec_ref(v_as_188_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(lean_object* v___x_195_, lean_object* v_ess_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v___y_201_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___y_208_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_199_ = lean_st_ref_get(v___x_195_);
v___x_205_ = lean_box(1);
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_array_get_size(v___x_199_);
v___x_219_ = lean_nat_dec_lt(v___x_206_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec(v___x_199_);
v___y_208_ = v___x_205_;
goto v___jp_207_;
}
else
{
uint8_t v___x_220_; 
v___x_220_ = lean_nat_dec_le(v___x_218_, v___x_218_);
if (v___x_220_ == 0)
{
if (v___x_219_ == 0)
{
lean_dec(v___x_199_);
v___y_208_ = v___x_205_;
goto v___jp_207_;
}
else
{
size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((size_t)0ULL);
v___x_222_ = lean_usize_of_nat(v___x_218_);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v___x_199_, v___x_221_, v___x_222_, v___x_205_);
lean_dec(v___x_199_);
v___y_208_ = v___x_223_;
goto v___jp_207_;
}
}
else
{
size_t v___x_224_; size_t v___x_225_; lean_object* v___x_226_; 
v___x_224_ = ((size_t)0ULL);
v___x_225_ = lean_usize_of_nat(v___x_218_);
v___x_226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__0(v___x_199_, v___x_224_, v___x_225_, v___x_205_);
lean_dec(v___x_199_);
v___y_208_ = v___x_226_;
goto v___jp_207_;
}
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_203_, 0, v___y_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
v___jp_207_:
{
lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_209_ = lean_array_get_size(v_ess_196_);
v___x_210_ = lean_nat_dec_lt(v___x_206_, v___x_209_);
if (v___x_210_ == 0)
{
v___y_201_ = v___y_208_;
goto v___jp_200_;
}
else
{
uint8_t v___x_211_; 
v___x_211_ = lean_nat_dec_le(v___x_209_, v___x_209_);
if (v___x_211_ == 0)
{
if (v___x_210_ == 0)
{
v___y_201_ = v___y_208_;
goto v___jp_200_;
}
else
{
size_t v___x_212_; size_t v___x_213_; lean_object* v___x_214_; 
v___x_212_ = ((size_t)0ULL);
v___x_213_ = lean_usize_of_nat(v___x_209_);
v___x_214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(v_ess_196_, v___x_212_, v___x_213_, v___y_208_);
v___y_201_ = v___x_214_;
goto v___jp_200_;
}
}
else
{
size_t v___x_215_; size_t v___x_216_; lean_object* v___x_217_; 
v___x_215_ = ((size_t)0ULL);
v___x_216_ = lean_usize_of_nat(v___x_209_);
v___x_217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__spec__1(v_ess_196_, v___x_215_, v___x_216_, v___y_208_);
v___y_201_ = v___x_217_;
goto v___jp_200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v___x_227_, lean_object* v_ess_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(v___x_227_, v_ess_228_, v___y_229_);
lean_dec_ref(v___y_229_);
lean_dec_ref(v_ess_228_);
lean_dec(v___x_227_);
return v_res_231_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_243_; lean_object* v___f_244_; 
v___x_243_ = l_Lean_Linter_builtinLinterSetsRef;
v___f_244_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__4_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_244_, 0, v___x_243_);
return v___f_244_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_245_; lean_object* v___f_246_; 
v___x_245_ = l_Lean_Linter_builtinLinterSetsRef;
v___f_246_ = lean_alloc_closure((void*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__5_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed), 4, 1);
lean_closure_set(v___f_246_, 0, v___x_245_);
return v___f_246_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___f_249_; lean_object* v___f_250_; lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_box(2);
v___f_249_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_250_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_251_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_252_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___f_253_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_254_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___x_255_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___f_253_);
lean_ctor_set(v___x_255_, 2, v___f_252_);
lean_ctor_set(v___x_255_, 3, v___f_251_);
lean_ctor_set(v___x_255_, 4, v___f_250_);
lean_ctor_set(v___x_255_, 5, v___f_249_);
lean_ctor_set(v___x_255_, 6, v___x_248_);
lean_ctor_set(v___x_255_, 7, v___x_247_);
return v___x_255_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___f_256_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___x_257_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v___f_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_261_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_();
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg(lean_object* v_inst_264_, lean_object* v_o_265_, lean_object* v_k_266_, lean_object* v_defVal_267_){
_start:
{
lean_object* v_toOptions_268_; lean_object* v_map_269_; lean_object* v_ofDataValue_x3f_270_; lean_object* v___x_271_; 
v_toOptions_268_ = lean_ctor_get(v_o_265_, 0);
v_map_269_ = lean_ctor_get(v_toOptions_268_, 0);
v_ofDataValue_x3f_270_ = lean_ctor_get(v_inst_264_, 1);
lean_inc_ref(v_ofDataValue_x3f_270_);
lean_dec_ref(v_inst_264_);
v___x_271_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_269_, v_k_266_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_270_);
lean_inc(v_defVal_267_);
return v_defVal_267_;
}
else
{
lean_object* v_val_272_; lean_object* v___x_273_; 
v_val_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_val_272_);
lean_dec_ref_known(v___x_271_, 1);
v___x_273_ = lean_apply_1(v_ofDataValue_x3f_270_, v_val_272_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_inc(v_defVal_267_);
return v_defVal_267_;
}
else
{
lean_object* v_val_274_; 
v_val_274_ = lean_ctor_get(v___x_273_, 0);
lean_inc(v_val_274_);
lean_dec_ref_known(v___x_273_, 1);
return v_val_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg___boxed(lean_object* v_inst_275_, lean_object* v_o_276_, lean_object* v_k_277_, lean_object* v_defVal_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Linter_LinterOptions_get___redArg(v_inst_275_, v_o_276_, v_k_277_, v_defVal_278_);
lean_dec(v_defVal_278_);
lean_dec(v_k_277_);
lean_dec_ref(v_o_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get(lean_object* v_00_u03b1_280_, lean_object* v_inst_281_, lean_object* v_o_282_, lean_object* v_k_283_, lean_object* v_defVal_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_Linter_LinterOptions_get___redArg(v_inst_281_, v_o_282_, v_k_283_, v_defVal_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___boxed(lean_object* v_00_u03b1_286_, lean_object* v_inst_287_, lean_object* v_o_288_, lean_object* v_k_289_, lean_object* v_defVal_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Linter_LinterOptions_get(v_00_u03b1_286_, v_inst_287_, v_o_288_, v_k_289_, v_defVal_290_);
lean_dec(v_defVal_290_);
lean_dec(v_k_289_);
lean_dec_ref(v_o_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg(lean_object* v_inst_292_, lean_object* v_o_293_, lean_object* v_k_294_){
_start:
{
lean_object* v_toOptions_295_; lean_object* v_map_296_; lean_object* v_ofDataValue_x3f_297_; lean_object* v___x_298_; 
v_toOptions_295_ = lean_ctor_get(v_o_293_, 0);
v_map_296_ = lean_ctor_get(v_toOptions_295_, 0);
v_ofDataValue_x3f_297_ = lean_ctor_get(v_inst_292_, 1);
lean_inc_ref(v_ofDataValue_x3f_297_);
lean_dec_ref(v_inst_292_);
v___x_298_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_296_, v_k_294_);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v___x_299_; 
lean_dec_ref(v_ofDataValue_x3f_297_);
v___x_299_ = lean_box(0);
return v___x_299_;
}
else
{
lean_object* v_val_300_; lean_object* v___x_301_; 
v_val_300_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_val_300_);
lean_dec_ref_known(v___x_298_, 1);
v___x_301_ = lean_apply_1(v_ofDataValue_x3f_297_, v_val_300_);
return v___x_301_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg___boxed(lean_object* v_inst_302_, lean_object* v_o_303_, lean_object* v_k_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_302_, v_o_303_, v_k_304_);
lean_dec(v_k_304_);
lean_dec_ref(v_o_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f(lean_object* v_00_u03b1_306_, lean_object* v_inst_307_, lean_object* v_o_308_, lean_object* v_k_309_){
_start:
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_307_, v_o_308_, v_k_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___boxed(lean_object* v_00_u03b1_311_, lean_object* v_inst_312_, lean_object* v_o_313_, lean_object* v_k_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_Linter_LinterOptions_get_x3f(v_00_u03b1_311_, v_inst_312_, v_o_313_, v_k_314_);
lean_dec(v_k_314_);
lean_dec_ref(v_o_313_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg___lam__0(lean_object* v___x_316_, lean_object* v_o_317_, lean_object* v_toPure_318_, lean_object* v_____do__lift_319_){
_start:
{
lean_object* v___x_320_; lean_object* v_toEnvExtension_321_; lean_object* v_asyncMode_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_merged_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_333_; 
v___x_320_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_321_ = lean_ctor_get(v___x_320_, 0);
v_asyncMode_322_ = lean_ctor_get(v_toEnvExtension_321_, 2);
v___x_323_ = lean_box(0);
v___x_324_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_316_, v___x_320_, v_____do__lift_319_, v_asyncMode_322_, v___x_323_);
v_merged_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; 
v_unused_334_ = lean_ctor_get(v___x_324_, 1);
lean_dec(v_unused_334_);
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_merged_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v_merged_325_);
lean_ctor_set(v___x_327_, 0, v_o_317_);
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_o_317_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_merged_325_);
v___x_330_ = v_reuseFailAlloc_332_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; 
v___x_331_ = lean_apply_2(v_toPure_318_, lean_box(0), v___x_330_);
return v___x_331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg(lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_o_337_){
_start:
{
lean_object* v_toApplicative_338_; lean_object* v_toBind_339_; lean_object* v_getEnv_340_; lean_object* v_toPure_341_; lean_object* v___x_342_; lean_object* v___f_343_; lean_object* v___x_344_; 
v_toApplicative_338_ = lean_ctor_get(v_inst_335_, 0);
lean_inc_ref(v_toApplicative_338_);
v_toBind_339_ = lean_ctor_get(v_inst_335_, 1);
lean_inc(v_toBind_339_);
lean_dec_ref(v_inst_335_);
v_getEnv_340_ = lean_ctor_get(v_inst_336_, 0);
lean_inc(v_getEnv_340_);
lean_dec_ref(v_inst_336_);
v_toPure_341_ = lean_ctor_get(v_toApplicative_338_, 1);
lean_inc(v_toPure_341_);
lean_dec_ref(v_toApplicative_338_);
v___x_342_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default));
v___f_343_ = lean_alloc_closure((void*)(l_Lean_Options_toLinterOptions___redArg___lam__0), 4, 3);
lean_closure_set(v___f_343_, 0, v___x_342_);
lean_closure_set(v___f_343_, 1, v_o_337_);
lean_closure_set(v___f_343_, 2, v_toPure_341_);
v___x_344_ = lean_apply_4(v_toBind_339_, lean_box(0), lean_box(0), v_getEnv_340_, v___f_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions(lean_object* v_m_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_o_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Lean_Options_toLinterOptions___redArg(v_inst_346_, v_inst_347_, v_o_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg(lean_object* v_o_350_, lean_object* v_opt_351_){
_start:
{
lean_object* v_linterSets_352_; lean_object* v_name_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_linterSets_352_ = lean_ctor_get(v_o_350_, 1);
v_name_353_ = lean_ctor_get(v_opt_351_, 0);
v___x_354_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_355_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_linterSets_352_, v_name_353_, v___x_354_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg___boxed(lean_object* v_o_356_, lean_object* v_opt_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_356_, v_opt_357_);
lean_dec_ref(v_opt_357_);
lean_dec_ref(v_o_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet(lean_object* v_00_u03b1_359_, lean_object* v_o_360_, lean_object* v_opt_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_360_, v_opt_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___boxed(lean_object* v_00_u03b1_363_, lean_object* v_o_364_, lean_object* v_opt_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Lean_Linter_LinterOptions_getSet(v_00_u03b1_363_, v_o_364_, v_opt_365_);
lean_dec_ref(v_opt_365_);
lean_dec_ref(v_o_364_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg___lam__0(lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_____do__lift_369_){
_start:
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_Options_toLinterOptions___redArg(v_inst_367_, v_inst_368_, v_____do__lift_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg(lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_){
_start:
{
lean_object* v_toBind_374_; lean_object* v_getOptions_375_; lean_object* v___f_376_; lean_object* v___x_377_; 
v_toBind_374_ = lean_ctor_get(v_inst_371_, 1);
lean_inc(v_toBind_374_);
v_getOptions_375_ = lean_ctor_get(v_inst_372_, 0);
lean_inc(v_getOptions_375_);
lean_dec_ref(v_inst_372_);
v___f_376_ = lean_alloc_closure((void*)(l_Lean_Linter_getLinterOptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_376_, 0, v_inst_371_);
lean_closure_set(v___f_376_, 1, v_inst_373_);
v___x_377_ = lean_apply_4(v_toBind_374_, lean_box(0), lean_box(0), v_getOptions_375_, v___f_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions(lean_object* v_m_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_inst_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_379_, v_inst_380_, v_inst_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(lean_object* v_name_383_, lean_object* v_decl_384_, lean_object* v_ref_385_){
_start:
{
lean_object* v_defValue_387_; lean_object* v_descr_388_; lean_object* v_deprecation_x3f_389_; lean_object* v___x_390_; uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_defValue_387_ = lean_ctor_get(v_decl_384_, 0);
v_descr_388_ = lean_ctor_get(v_decl_384_, 1);
v_deprecation_x3f_389_ = lean_ctor_get(v_decl_384_, 2);
v___x_390_ = lean_alloc_ctor(1, 0, 1);
v___x_391_ = lean_unbox(v_defValue_387_);
lean_ctor_set_uint8(v___x_390_, 0, v___x_391_);
lean_inc(v_deprecation_x3f_389_);
lean_inc_ref(v_descr_388_);
lean_inc_n(v_name_383_, 2);
v___x_392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_392_, 0, v_name_383_);
lean_ctor_set(v___x_392_, 1, v_ref_385_);
lean_ctor_set(v___x_392_, 2, v___x_390_);
lean_ctor_set(v___x_392_, 3, v_descr_388_);
lean_ctor_set(v___x_392_, 4, v_deprecation_x3f_389_);
v___x_393_ = lean_register_option(v_name_383_, v___x_392_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_401_; 
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_401_ == 0)
{
lean_object* v_unused_402_; 
v_unused_402_ = lean_ctor_get(v___x_393_, 0);
lean_dec(v_unused_402_);
v___x_395_ = v___x_393_;
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
else
{
lean_dec(v___x_393_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_401_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_399_; 
lean_inc(v_defValue_387_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_name_383_);
lean_ctor_set(v___x_397_, 1, v_defValue_387_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_397_);
v___x_399_ = v___x_395_;
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
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
lean_dec(v_name_383_);
v_a_403_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_393_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_393_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_411_, lean_object* v_decl_412_, lean_object* v_ref_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v_name_411_, v_decl_412_, v_ref_413_);
lean_dec_ref(v_decl_412_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_433_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_434_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_435_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_436_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_433_, v___x_434_, v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4____boxed(lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_();
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_455_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_456_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_457_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_458_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_455_, v___x_456_, v___x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4____boxed(lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_();
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_477_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_478_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_479_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_480_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_477_, v___x_478_, v___x_479_);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4____boxed(lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_();
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_));
v___x_487_ = lean_st_mk_ref(v___x_486_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2____boxed(lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_();
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_addEnvLinterOption(lean_object* v_opt_491_){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_493_ = l_Lean_Linter_envLinterOptionsRef;
v___x_494_ = lean_st_ref_take(v___x_493_);
v___x_495_ = lean_array_push(v___x_494_, v_opt_491_);
v___x_496_ = lean_st_ref_put(v___x_493_, v___x_495_);
v___x_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_addEnvLinterOption___boxed(lean_object* v_opt_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Linter_addEnvLinterOption(v_opt_498_);
return v_res_500_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(lean_object* v_o_501_, lean_object* v_k_502_, uint8_t v_defVal_503_){
_start:
{
lean_object* v_toOptions_504_; lean_object* v_map_505_; lean_object* v___x_506_; 
v_toOptions_504_ = lean_ctor_get(v_o_501_, 0);
v_map_505_ = lean_ctor_get(v_toOptions_504_, 0);
v___x_506_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_505_, v_k_502_);
if (lean_obj_tag(v___x_506_) == 0)
{
return v_defVal_503_;
}
else
{
lean_object* v_val_507_; 
v_val_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_val_507_);
lean_dec_ref_known(v___x_506_, 1);
if (lean_obj_tag(v_val_507_) == 1)
{
uint8_t v_v_508_; 
v_v_508_ = lean_ctor_get_uint8(v_val_507_, 0);
lean_dec_ref_known(v_val_507_, 0);
return v_v_508_;
}
else
{
lean_dec(v_val_507_);
return v_defVal_503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0___boxed(lean_object* v_o_509_, lean_object* v_k_510_, lean_object* v_defVal_511_){
_start:
{
uint8_t v_defVal_boxed_512_; uint8_t v_res_513_; lean_object* v_r_514_; 
v_defVal_boxed_512_ = lean_unbox(v_defVal_511_);
v_res_513_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_509_, v_k_510_, v_defVal_boxed_512_);
lean_dec(v_k_510_);
lean_dec_ref(v_o_509_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterAll(lean_object* v_o_515_, uint8_t v_defValue_516_){
_start:
{
lean_object* v___x_517_; lean_object* v_name_518_; uint8_t v___x_519_; 
v___x_517_ = l_Lean_Linter_linter_all;
v_name_518_ = lean_ctor_get(v___x_517_, 0);
v___x_519_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_515_, v_name_518_, v_defValue_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterAll___boxed(lean_object* v_o_520_, lean_object* v_defValue_521_){
_start:
{
uint8_t v_defValue_boxed_522_; uint8_t v_res_523_; lean_object* v_r_524_; 
v_defValue_boxed_522_ = lean_unbox(v_defValue_521_);
v_res_523_ = l_Lean_Linter_getLinterAll(v_o_520_, v_defValue_boxed_522_);
lean_dec_ref(v_o_520_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(lean_object* v_o_525_, lean_object* v_k_526_){
_start:
{
lean_object* v_toOptions_527_; lean_object* v_map_528_; lean_object* v___x_529_; 
v_toOptions_527_ = lean_ctor_get(v_o_525_, 0);
v_map_528_ = lean_ctor_get(v_toOptions_527_, 0);
v___x_529_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_528_, v_k_526_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v___x_530_; 
v___x_530_ = lean_box(0);
return v___x_530_;
}
else
{
lean_object* v_val_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_541_; 
v_val_531_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_541_ == 0)
{
v___x_533_ = v___x_529_;
v_isShared_534_ = v_isSharedCheck_541_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_val_531_);
lean_dec(v___x_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_541_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
if (lean_obj_tag(v_val_531_) == 1)
{
uint8_t v_v_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v_v_535_ = lean_ctor_get_uint8(v_val_531_, 0);
lean_dec_ref_known(v_val_531_, 0);
v___x_536_ = lean_box(v_v_535_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_536_);
v___x_538_ = v___x_533_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
else
{
lean_object* v___x_540_; 
lean_del_object(v___x_533_);
lean_dec(v_val_531_);
v___x_540_ = lean_box(0);
return v___x_540_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0___boxed(lean_object* v_o_542_, lean_object* v_k_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_542_, v_k_543_);
lean_dec(v_k_543_);
lean_dec_ref(v_o_542_);
return v_res_544_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
if (lean_obj_tag(v_x_546_) == 0)
{
uint8_t v___x_547_; 
v___x_547_ = 1;
return v___x_547_;
}
else
{
uint8_t v___x_548_; 
v___x_548_ = 0;
return v___x_548_;
}
}
else
{
if (lean_obj_tag(v_x_546_) == 0)
{
uint8_t v___x_549_; 
v___x_549_ = 0;
return v___x_549_;
}
else
{
lean_object* v_val_550_; uint8_t v___x_551_; 
v_val_550_ = lean_ctor_get(v_x_546_, 0);
v___x_551_ = lean_unbox(v_val_550_);
if (v___x_551_ == 0)
{
lean_object* v_val_552_; uint8_t v___x_553_; 
v_val_552_ = lean_ctor_get(v_x_545_, 0);
v___x_553_ = lean_unbox(v_val_552_);
if (v___x_553_ == 0)
{
uint8_t v___x_554_; 
v___x_554_ = 1;
return v___x_554_;
}
else
{
uint8_t v___x_555_; 
v___x_555_ = lean_unbox(v_val_550_);
return v___x_555_;
}
}
else
{
lean_object* v_val_556_; uint8_t v___x_557_; 
v_val_556_ = lean_ctor_get(v_x_545_, 0);
v___x_557_ = lean_unbox(v_val_556_);
return v___x_557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1___boxed(lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(v_x_558_, v_x_559_);
lean_dec(v_x_559_);
lean_dec(v_x_558_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(lean_object* v_o_565_, lean_object* v_as_566_, size_t v_i_567_, size_t v_stop_568_){
_start:
{
uint8_t v___x_569_; 
v___x_569_ = lean_usize_dec_eq(v_i_567_, v_stop_568_);
if (v___x_569_ == 0)
{
uint8_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_570_ = 1;
v___x_571_ = lean_array_uget_borrowed(v_as_566_, v_i_567_);
v___x_572_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_565_, v___x_571_);
v___x_573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0));
v___x_574_ = l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(v___x_572_, v___x_573_);
lean_dec(v___x_572_);
if (v___x_574_ == 0)
{
size_t v___x_575_; size_t v___x_576_; 
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_add(v_i_567_, v___x_575_);
v_i_567_ = v___x_576_;
goto _start;
}
else
{
return v___x_570_;
}
}
else
{
uint8_t v___x_578_; 
v___x_578_ = 0;
return v___x_578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___boxed(lean_object* v_o_579_, lean_object* v_as_580_, lean_object* v_i_581_, lean_object* v_stop_582_){
_start:
{
size_t v_i_boxed_583_; size_t v_stop_boxed_584_; uint8_t v_res_585_; lean_object* v_r_586_; 
v_i_boxed_583_ = lean_unbox_usize(v_i_581_);
lean_dec(v_i_581_);
v_stop_boxed_584_ = lean_unbox_usize(v_stop_582_);
lean_dec(v_stop_582_);
v_res_585_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_579_, v_as_580_, v_i_boxed_583_, v_stop_boxed_584_);
lean_dec_ref(v_as_580_);
lean_dec_ref(v_o_579_);
v_r_586_ = lean_box(v_res_585_);
return v_r_586_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterValue(lean_object* v_opt_587_, lean_object* v_o_588_){
_start:
{
lean_object* v_name_589_; lean_object* v_defValue_590_; uint8_t v___y_592_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_name_589_ = lean_ctor_get(v_opt_587_, 0);
v_defValue_590_ = lean_ctor_get(v_opt_587_, 1);
v___x_595_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_588_, v_opt_587_);
v___x_596_ = lean_unsigned_to_nat(0u);
v___x_597_ = lean_array_get_size(v___x_595_);
v___x_598_ = lean_nat_dec_lt(v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
uint8_t v___x_599_; 
lean_dec(v___x_595_);
v___x_599_ = lean_unbox(v_defValue_590_);
v___y_592_ = v___x_599_;
goto v___jp_591_;
}
else
{
if (v___x_598_ == 0)
{
uint8_t v___x_600_; 
lean_dec(v___x_595_);
v___x_600_ = lean_unbox(v_defValue_590_);
v___y_592_ = v___x_600_;
goto v___jp_591_;
}
else
{
size_t v___x_601_; size_t v___x_602_; uint8_t v___x_603_; 
v___x_601_ = ((size_t)0ULL);
v___x_602_ = lean_usize_of_nat(v___x_597_);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_588_, v___x_595_, v___x_601_, v___x_602_);
lean_dec(v___x_595_);
if (v___x_603_ == 0)
{
uint8_t v___x_604_; 
v___x_604_ = lean_unbox(v_defValue_590_);
v___y_592_ = v___x_604_;
goto v___jp_591_;
}
else
{
v___y_592_ = v___x_603_;
goto v___jp_591_;
}
}
}
v___jp_591_:
{
uint8_t v___x_593_; uint8_t v___x_594_; 
v___x_593_ = l_Lean_Linter_getLinterAll(v_o_588_, v___y_592_);
v___x_594_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_588_, v_name_589_, v___x_593_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterValue___boxed(lean_object* v_opt_605_, lean_object* v_o_606_){
_start:
{
uint8_t v_res_607_; lean_object* v_r_608_; 
v_res_607_ = l_Lean_Linter_getLinterValue(v_opt_605_, v_o_606_);
lean_dec_ref(v_o_606_);
lean_dec_ref(v_opt_605_);
v_r_608_ = lean_box(v_res_607_);
return v_r_608_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object* v_name_609_, lean_object* v_o_610_){
_start:
{
uint8_t v___y_612_; lean_object* v_linterSets_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_linterSets_615_ = lean_ctor_get(v_o_610_, 1);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_618_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_linterSets_615_, v_name_609_, v___x_617_);
v___x_619_ = lean_array_get_size(v___x_618_);
v___x_620_ = lean_nat_dec_lt(v___x_616_, v___x_619_);
if (v___x_620_ == 0)
{
lean_dec(v___x_618_);
v___y_612_ = v___x_620_;
goto v___jp_611_;
}
else
{
if (v___x_620_ == 0)
{
lean_dec(v___x_618_);
v___y_612_ = v___x_620_;
goto v___jp_611_;
}
else
{
size_t v___x_621_; size_t v___x_622_; uint8_t v___x_623_; 
v___x_621_ = ((size_t)0ULL);
v___x_622_ = lean_usize_of_nat(v___x_619_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_610_, v___x_618_, v___x_621_, v___x_622_);
lean_dec(v___x_618_);
v___y_612_ = v___x_623_;
goto v___jp_611_;
}
}
v___jp_611_:
{
uint8_t v___x_613_; uint8_t v___x_614_; 
v___x_613_ = l_Lean_Linter_getLinterAll(v_o_610_, v___y_612_);
v___x_614_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_610_, v_name_609_, v___x_613_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isLinterEnabledByOptions___boxed(lean_object* v_name_624_, lean_object* v_o_625_){
_start:
{
uint8_t v_res_626_; lean_object* v_r_627_; 
v_res_626_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_624_, v_o_625_);
lean_dec_ref(v_o_625_);
lean_dec(v_name_624_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___redArg___closed__1(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l_Lean_Linter_logLint___redArg___closed__0));
v___x_636_ = l_Lean_stringToMessageData(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___redArg___closed__3(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_638_ = ((lean_object*)(l_Lean_Linter_logLint___redArg___closed__2));
v___x_639_ = l_Lean_stringToMessageData(v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___redArg(lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_linterOption_644_, lean_object* v_stx_645_, lean_object* v_msg_646_){
_start:
{
lean_object* v_name_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_665_; 
v_name_647_ = lean_ctor_get(v_linterOption_644_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_linterOption_644_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v_linterOption_644_, 1);
lean_dec(v_unused_666_);
v___x_649_ = v_linterOption_644_;
v_isShared_650_ = v_isSharedCheck_665_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_name_647_);
lean_dec(v_linterOption_644_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_665_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_651_ = lean_obj_once(&l_Lean_Linter_logLint___redArg___closed__1, &l_Lean_Linter_logLint___redArg___closed__1_once, _init_l_Lean_Linter_logLint___redArg___closed__1);
lean_inc(v_name_647_);
v___x_652_ = l_Lean_MessageData_ofName(v_name_647_);
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 7);
lean_ctor_set(v___x_649_, 1, v___x_652_);
lean_ctor_set(v___x_649_, 0, v___x_651_);
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_652_);
v___x_654_ = v_reuseFailAlloc_664_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v_disable_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_655_ = lean_obj_once(&l_Lean_Linter_logLint___redArg___closed__3, &l_Lean_Linter_logLint___redArg___closed__3_once, _init_l_Lean_Linter_logLint___redArg___closed__3);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v_disable_657_ = l_Lean_MessageData_note(v___x_656_);
v___x_658_ = ((lean_object*)(l_Lean_Linter_linterMessageTag));
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v_msg_646_);
lean_ctor_set(v___x_659_, 1, v_disable_657_);
v___x_660_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_661_, 0, v_name_647_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
lean_inc(v_stx_645_);
v___x_662_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_662_, 0, v_stx_645_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = l_Lean_logWarningAt___redArg(v_inst_640_, v_inst_641_, v_inst_642_, v_inst_643_, v_stx_645_, v___x_662_);
return v___x_663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint(lean_object* v_m_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_linterOption_672_, lean_object* v_stx_673_, lean_object* v_msg_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Linter_logLint___redArg(v_inst_668_, v_inst_669_, v_inst_670_, v_inst_671_, v_linterOption_672_, v_stx_673_, v_msg_674_);
return v___x_675_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isLinterMessage___lam__0(lean_object* v_x_676_){
_start:
{
lean_object* v___x_677_; uint8_t v___x_678_; 
v___x_677_ = ((lean_object*)(l_Lean_Linter_linterMessageTag));
v___x_678_ = lean_name_eq(v_x_676_, v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isLinterMessage___lam__0___boxed(lean_object* v_x_679_){
_start:
{
uint8_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l_Lean_MessageData_isLinterMessage___lam__0(v_x_679_);
lean_dec(v_x_679_);
v_r_681_ = lean_box(v_res_680_);
return v_r_681_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isLinterMessage(lean_object* v_msg_683_){
_start:
{
lean_object* v___f_684_; uint8_t v___x_685_; 
v___f_684_ = ((lean_object*)(l_Lean_MessageData_isLinterMessage___closed__0));
v___x_685_ = l_Lean_MessageData_hasTag(v___f_684_, v_msg_683_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isLinterMessage___boxed(lean_object* v_msg_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l_Lean_MessageData_isLinterMessage(v_msg_686_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0(lean_object* v_linterOption_689_, lean_object* v_toPure_690_, lean_object* v_inst_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_stx_695_, lean_object* v_msg_696_, lean_object* v_____do__lift_697_){
_start:
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_Linter_getLinterValue(v_linterOption_689_, v_____do__lift_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec_ref(v_msg_696_);
lean_dec(v_stx_695_);
lean_dec_ref(v_inst_694_);
lean_dec(v_inst_693_);
lean_dec_ref(v_inst_692_);
lean_dec_ref(v_inst_691_);
lean_dec_ref(v_linterOption_689_);
v___x_699_ = lean_box(0);
v___x_700_ = lean_apply_2(v_toPure_690_, lean_box(0), v___x_699_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; 
lean_dec(v_toPure_690_);
v___x_701_ = l_Lean_Linter_logLint___redArg(v_inst_691_, v_inst_692_, v_inst_693_, v_inst_694_, v_linterOption_689_, v_stx_695_, v_msg_696_);
return v___x_701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0___boxed(lean_object* v_linterOption_702_, lean_object* v_toPure_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_stx_708_, lean_object* v_msg_709_, lean_object* v_____do__lift_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Linter_logLintIf___redArg___lam__0(v_linterOption_702_, v_toPure_703_, v_inst_704_, v_inst_705_, v_inst_706_, v_inst_707_, v_stx_708_, v_msg_709_, v_____do__lift_710_);
lean_dec_ref(v_____do__lift_710_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg(lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_linterOption_717_, lean_object* v_stx_718_, lean_object* v_msg_719_){
_start:
{
lean_object* v_toApplicative_720_; lean_object* v_toBind_721_; lean_object* v_toPure_722_; lean_object* v___x_723_; lean_object* v___f_724_; lean_object* v___x_725_; 
v_toApplicative_720_ = lean_ctor_get(v_inst_712_, 0);
v_toBind_721_ = lean_ctor_get(v_inst_712_, 1);
lean_inc(v_toBind_721_);
v_toPure_722_ = lean_ctor_get(v_toApplicative_720_, 1);
lean_inc(v_toPure_722_);
lean_inc_ref(v_inst_715_);
lean_inc_ref(v_inst_712_);
v___x_723_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_712_, v_inst_715_, v_inst_716_);
v___f_724_ = lean_alloc_closure((void*)(l_Lean_Linter_logLintIf___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_724_, 0, v_linterOption_717_);
lean_closure_set(v___f_724_, 1, v_toPure_722_);
lean_closure_set(v___f_724_, 2, v_inst_712_);
lean_closure_set(v___f_724_, 3, v_inst_713_);
lean_closure_set(v___f_724_, 4, v_inst_714_);
lean_closure_set(v___f_724_, 5, v_inst_715_);
lean_closure_set(v___f_724_, 6, v_stx_718_);
lean_closure_set(v___f_724_, 7, v_msg_719_);
v___x_725_ = lean_apply_4(v_toBind_721_, lean_box(0), lean_box(0), v___x_723_, v___f_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf(lean_object* v_m_726_, lean_object* v_inst_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_linterOption_732_, lean_object* v_stx_733_, lean_object* v_msg_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Linter_logLintIf___redArg(v_inst_727_, v_inst_728_, v_inst_729_, v_inst_730_, v_inst_731_, v_linterOption_732_, v_stx_733_, v_msg_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(lean_object* v_env_736_, lean_object* v_as_737_, size_t v_i_738_, size_t v_stop_739_, lean_object* v_b_740_){
_start:
{
lean_object* v___y_742_; uint8_t v___x_746_; 
v___x_746_ = lean_usize_dec_eq(v_i_738_, v_stop_739_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; lean_object* v_fst_748_; uint8_t v___x_749_; 
v___x_747_ = lean_array_uget_borrowed(v_as_737_, v_i_738_);
v_fst_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_fst_748_);
lean_inc_ref(v_env_736_);
v___x_749_ = l_Lean_Environment_contains(v_env_736_, v_fst_748_, v___x_746_);
if (v___x_749_ == 0)
{
v___y_742_ = v_b_740_;
goto v___jp_741_;
}
else
{
lean_object* v___x_750_; 
lean_inc(v___x_747_);
v___x_750_ = lean_array_push(v_b_740_, v___x_747_);
v___y_742_ = v___x_750_;
goto v___jp_741_;
}
}
else
{
lean_dec_ref(v_env_736_);
return v_b_740_;
}
v___jp_741_:
{
size_t v___x_743_; size_t v___x_744_; 
v___x_743_ = ((size_t)1ULL);
v___x_744_ = lean_usize_add(v_i_738_, v___x_743_);
v_i_738_ = v___x_744_;
v_b_740_ = v___y_742_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_751_, lean_object* v_as_752_, lean_object* v_i_753_, lean_object* v_stop_754_, lean_object* v_b_755_){
_start:
{
size_t v_i_boxed_756_; size_t v_stop_boxed_757_; lean_object* v_res_758_; 
v_i_boxed_756_ = lean_unbox_usize(v_i_753_);
lean_dec(v_i_753_);
v_stop_boxed_757_ = lean_unbox_usize(v_stop_754_);
lean_dec(v_stop_754_);
v_res_758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_751_, v_as_752_, v_i_boxed_756_, v_stop_boxed_757_, v_b_755_);
lean_dec_ref(v_as_752_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_759_, lean_object* v_x_760_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
lean_object* v_k_761_; lean_object* v_v_762_; lean_object* v_l_763_; lean_object* v_r_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_k_761_ = lean_ctor_get(v_x_760_, 1);
v_v_762_ = lean_ctor_get(v_x_760_, 2);
v_l_763_ = lean_ctor_get(v_x_760_, 3);
v_r_764_ = lean_ctor_get(v_x_760_, 4);
v___x_765_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_759_, v_l_763_);
lean_inc(v_v_762_);
lean_inc(v_k_761_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v_k_761_);
lean_ctor_set(v___x_766_, 1, v_v_762_);
v___x_767_ = lean_array_push(v___x_765_, v___x_766_);
v_init_759_ = v___x_767_;
v_x_760_ = v_r_764_;
goto _start;
}
else
{
return v_init_759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_769_, lean_object* v_x_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_769_, v_x_770_);
lean_dec(v_x_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(lean_object* v_env_776_, lean_object* v_s_777_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_780_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v___x_779_, v_s_777_);
v___x_781_ = lean_array_get_size(v___x_780_);
v___x_782_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_783_ = lean_nat_dec_lt(v___x_778_, v___x_781_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; 
lean_dec_ref(v___x_780_);
lean_dec_ref(v_env_776_);
v___x_784_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
return v___x_784_;
}
else
{
uint8_t v___x_785_; 
v___x_785_ = lean_nat_dec_le(v___x_781_, v___x_781_);
if (v___x_785_ == 0)
{
if (v___x_783_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v___x_780_);
lean_dec_ref(v_env_776_);
v___x_786_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
return v___x_786_;
}
else
{
size_t v___x_787_; size_t v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_787_ = ((size_t)0ULL);
v___x_788_ = lean_usize_of_nat(v___x_781_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_776_, v___x_780_, v___x_787_, v___x_788_, v___x_782_);
lean_dec_ref(v___x_780_);
lean_inc_ref_n(v___x_789_, 2);
v___x_790_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___x_789_);
lean_ctor_set(v___x_790_, 2, v___x_789_);
return v___x_790_;
}
}
else
{
size_t v___x_791_; size_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_791_ = ((size_t)0ULL);
v___x_792_ = lean_usize_of_nat(v___x_781_);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_776_, v___x_780_, v___x_791_, v___x_792_, v___x_782_);
lean_dec_ref(v___x_780_);
lean_inc_ref_n(v___x_793_, 2);
v___x_794_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
lean_ctor_set(v___x_794_, 2, v___x_793_);
return v___x_794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed(lean_object* v_env_795_, lean_object* v_s_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(v_env_795_, v_s_796_);
lean_dec(v_s_796_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___f_803_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_804_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_805_ = lean_box(0);
v___x_806_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_804_, v___x_805_, v___f_803_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed(lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_();
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0(lean_object* v_init_809_, lean_object* v_t_810_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_809_, v_t_810_);
return v___x_811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_812_, lean_object* v_t_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0(v_init_812_, v_t_813_);
lean_dec(v_t_813_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(lean_object* v_env_815_, lean_object* v_declName_816_, lean_object* v_optName_817_){
_start:
{
lean_object* v___x_818_; lean_object* v_toEnvExtension_819_; lean_object* v_asyncMode_820_; lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; 
v___x_818_ = l_Lean_Linter_envLinterSnapshotExt;
v_toEnvExtension_819_ = lean_ctor_get(v___x_818_, 0);
v_asyncMode_820_ = lean_ctor_get(v_toEnvExtension_819_, 2);
v___x_821_ = lean_box(1);
v___x_822_ = 0;
v___x_823_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_821_, v___x_818_, v_env_815_, v_declName_816_, v_asyncMode_820_, v___x_822_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v___x_824_; 
v___x_824_ = lean_box(0);
return v___x_824_;
}
else
{
lean_object* v_val_825_; lean_object* v___x_826_; 
v_val_825_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_val_825_);
lean_dec_ref_known(v___x_823_, 1);
v___x_826_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_825_, v_optName_817_);
lean_dec(v_val_825_);
return v___x_826_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f___boxed(lean_object* v_env_827_, lean_object* v_declName_828_, lean_object* v_optName_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(v_env_827_, v_declName_828_, v_optName_829_);
lean_dec(v_optName_829_);
return v_res_830_;
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
