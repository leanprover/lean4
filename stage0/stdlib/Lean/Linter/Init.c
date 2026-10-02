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
uint8_t v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___f_250_; lean_object* v___f_251_; lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_247_ = 0;
v___x_248_ = lean_box(0);
v___x_249_ = lean_box(2);
v___f_250_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_251_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_252_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___f_253_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___f_254_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_255_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___x_256_ = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___f_254_);
lean_ctor_set(v___x_256_, 2, v___f_253_);
lean_ctor_set(v___x_256_, 3, v___f_252_);
lean_ctor_set(v___x_256_, 4, v___f_251_);
lean_ctor_set(v___x_256_, 5, v___f_250_);
lean_ctor_set(v___x_256_, 6, v___x_249_);
lean_ctor_set(v___x_256_, 7, v___x_248_);
lean_ctor_set_uint8(v___x_256_, sizeof(void*)*8, v___x_247_);
return v___x_256_;
}
}
static lean_object* _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___f_257_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_));
v___x_258_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___f_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = lean_obj_once(&l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_, &l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_);
v___x_262_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2____boxed(lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_426764049____hygCtx___hyg_2_();
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg(lean_object* v_inst_265_, lean_object* v_o_266_, lean_object* v_k_267_, lean_object* v_defVal_268_){
_start:
{
lean_object* v_toOptions_269_; lean_object* v_map_270_; lean_object* v_ofDataValue_x3f_271_; lean_object* v___x_272_; 
v_toOptions_269_ = lean_ctor_get(v_o_266_, 0);
v_map_270_ = lean_ctor_get(v_toOptions_269_, 0);
v_ofDataValue_x3f_271_ = lean_ctor_get(v_inst_265_, 1);
lean_inc_ref(v_ofDataValue_x3f_271_);
lean_dec_ref(v_inst_265_);
v___x_272_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_270_, v_k_267_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_271_);
lean_inc(v_defVal_268_);
return v_defVal_268_;
}
else
{
lean_object* v_val_273_; lean_object* v___x_274_; 
v_val_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_val_273_);
lean_dec_ref_known(v___x_272_, 1);
v___x_274_ = lean_apply_1(v_ofDataValue_x3f_271_, v_val_273_);
if (lean_obj_tag(v___x_274_) == 0)
{
lean_inc(v_defVal_268_);
return v_defVal_268_;
}
else
{
lean_object* v_val_275_; 
v_val_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_val_275_);
lean_dec_ref_known(v___x_274_, 1);
return v_val_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg___boxed(lean_object* v_inst_276_, lean_object* v_o_277_, lean_object* v_k_278_, lean_object* v_defVal_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Linter_LinterOptions_get___redArg(v_inst_276_, v_o_277_, v_k_278_, v_defVal_279_);
lean_dec(v_defVal_279_);
lean_dec(v_k_278_);
lean_dec_ref(v_o_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get(lean_object* v_00_u03b1_281_, lean_object* v_inst_282_, lean_object* v_o_283_, lean_object* v_k_284_, lean_object* v_defVal_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_Linter_LinterOptions_get___redArg(v_inst_282_, v_o_283_, v_k_284_, v_defVal_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___boxed(lean_object* v_00_u03b1_287_, lean_object* v_inst_288_, lean_object* v_o_289_, lean_object* v_k_290_, lean_object* v_defVal_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_Linter_LinterOptions_get(v_00_u03b1_287_, v_inst_288_, v_o_289_, v_k_290_, v_defVal_291_);
lean_dec(v_defVal_291_);
lean_dec(v_k_290_);
lean_dec_ref(v_o_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg(lean_object* v_inst_293_, lean_object* v_o_294_, lean_object* v_k_295_){
_start:
{
lean_object* v_toOptions_296_; lean_object* v_map_297_; lean_object* v_ofDataValue_x3f_298_; lean_object* v___x_299_; 
v_toOptions_296_ = lean_ctor_get(v_o_294_, 0);
v_map_297_ = lean_ctor_get(v_toOptions_296_, 0);
v_ofDataValue_x3f_298_ = lean_ctor_get(v_inst_293_, 1);
lean_inc_ref(v_ofDataValue_x3f_298_);
lean_dec_ref(v_inst_293_);
v___x_299_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_297_, v_k_295_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v___x_300_; 
lean_dec_ref(v_ofDataValue_x3f_298_);
v___x_300_ = lean_box(0);
return v___x_300_;
}
else
{
lean_object* v_val_301_; lean_object* v___x_302_; 
v_val_301_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_val_301_);
lean_dec_ref_known(v___x_299_, 1);
v___x_302_ = lean_apply_1(v_ofDataValue_x3f_298_, v_val_301_);
return v___x_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg___boxed(lean_object* v_inst_303_, lean_object* v_o_304_, lean_object* v_k_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_303_, v_o_304_, v_k_305_);
lean_dec(v_k_305_);
lean_dec_ref(v_o_304_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f(lean_object* v_00_u03b1_307_, lean_object* v_inst_308_, lean_object* v_o_309_, lean_object* v_k_310_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_308_, v_o_309_, v_k_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___boxed(lean_object* v_00_u03b1_312_, lean_object* v_inst_313_, lean_object* v_o_314_, lean_object* v_k_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Linter_LinterOptions_get_x3f(v_00_u03b1_312_, v_inst_313_, v_o_314_, v_k_315_);
lean_dec(v_k_315_);
lean_dec_ref(v_o_314_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg___lam__0(lean_object* v___x_317_, lean_object* v_o_318_, lean_object* v_toPure_319_, lean_object* v_____do__lift_320_){
_start:
{
lean_object* v___x_321_; lean_object* v_toEnvExtension_322_; lean_object* v_asyncMode_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_merged_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
v___x_321_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_322_ = lean_ctor_get(v___x_321_, 0);
v_asyncMode_323_ = lean_ctor_get(v_toEnvExtension_322_, 2);
v___x_324_ = lean_box(0);
v___x_325_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_317_, v___x_321_, v_____do__lift_320_, v_asyncMode_323_, v___x_324_);
v_merged_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_334_ == 0)
{
lean_object* v_unused_335_; 
v_unused_335_ = lean_ctor_get(v___x_325_, 1);
lean_dec(v_unused_335_);
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_merged_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 1, v_merged_326_);
lean_ctor_set(v___x_328_, 0, v_o_318_);
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_o_318_);
lean_ctor_set(v_reuseFailAlloc_333_, 1, v_merged_326_);
v___x_331_ = v_reuseFailAlloc_333_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; 
v___x_332_ = lean_apply_2(v_toPure_319_, lean_box(0), v___x_331_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg(lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_o_338_){
_start:
{
lean_object* v_toApplicative_339_; lean_object* v_toBind_340_; lean_object* v_getEnv_341_; lean_object* v_toPure_342_; lean_object* v___x_343_; lean_object* v___f_344_; lean_object* v___x_345_; 
v_toApplicative_339_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toApplicative_339_);
v_toBind_340_ = lean_ctor_get(v_inst_336_, 1);
lean_inc(v_toBind_340_);
lean_dec_ref(v_inst_336_);
v_getEnv_341_ = lean_ctor_get(v_inst_337_, 0);
lean_inc(v_getEnv_341_);
lean_dec_ref(v_inst_337_);
v_toPure_342_ = lean_ctor_get(v_toApplicative_339_, 1);
lean_inc(v_toPure_342_);
lean_dec_ref(v_toApplicative_339_);
v___x_343_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default));
v___f_344_ = lean_alloc_closure((void*)(l_Lean_Options_toLinterOptions___redArg___lam__0), 4, 3);
lean_closure_set(v___f_344_, 0, v___x_343_);
lean_closure_set(v___f_344_, 1, v_o_338_);
lean_closure_set(v___f_344_, 2, v_toPure_342_);
v___x_345_ = lean_apply_4(v_toBind_340_, lean_box(0), lean_box(0), v_getEnv_341_, v___f_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions(lean_object* v_m_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_o_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Options_toLinterOptions___redArg(v_inst_347_, v_inst_348_, v_o_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg(lean_object* v_o_351_, lean_object* v_opt_352_){
_start:
{
lean_object* v_linterSets_353_; lean_object* v_name_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_linterSets_353_ = lean_ctor_get(v_o_351_, 1);
v_name_354_ = lean_ctor_get(v_opt_352_, 0);
v___x_355_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_356_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_linterSets_353_, v_name_354_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg___boxed(lean_object* v_o_357_, lean_object* v_opt_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_357_, v_opt_358_);
lean_dec_ref(v_opt_358_);
lean_dec_ref(v_o_357_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet(lean_object* v_00_u03b1_360_, lean_object* v_o_361_, lean_object* v_opt_362_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_361_, v_opt_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___boxed(lean_object* v_00_u03b1_364_, lean_object* v_o_365_, lean_object* v_opt_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Lean_Linter_LinterOptions_getSet(v_00_u03b1_364_, v_o_365_, v_opt_366_);
lean_dec_ref(v_opt_366_);
lean_dec_ref(v_o_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg___lam__0(lean_object* v_inst_368_, lean_object* v_inst_369_, lean_object* v_____do__lift_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Options_toLinterOptions___redArg(v_inst_368_, v_inst_369_, v_____do__lift_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg(lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_){
_start:
{
lean_object* v_toBind_375_; lean_object* v_getOptions_376_; lean_object* v___f_377_; lean_object* v___x_378_; 
v_toBind_375_ = lean_ctor_get(v_inst_372_, 1);
lean_inc(v_toBind_375_);
v_getOptions_376_ = lean_ctor_get(v_inst_373_, 0);
lean_inc(v_getOptions_376_);
lean_dec_ref(v_inst_373_);
v___f_377_ = lean_alloc_closure((void*)(l_Lean_Linter_getLinterOptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_377_, 0, v_inst_372_);
lean_closure_set(v___f_377_, 1, v_inst_374_);
v___x_378_ = lean_apply_4(v_toBind_375_, lean_box(0), lean_box(0), v_getOptions_376_, v___f_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions(lean_object* v_m_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_inst_382_){
_start:
{
lean_object* v___x_383_; 
v___x_383_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_380_, v_inst_381_, v_inst_382_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(lean_object* v_name_384_, lean_object* v_decl_385_, lean_object* v_ref_386_){
_start:
{
lean_object* v_defValue_388_; lean_object* v_descr_389_; lean_object* v_deprecation_x3f_390_; lean_object* v___x_391_; uint8_t v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_defValue_388_ = lean_ctor_get(v_decl_385_, 0);
v_descr_389_ = lean_ctor_get(v_decl_385_, 1);
v_deprecation_x3f_390_ = lean_ctor_get(v_decl_385_, 2);
v___x_391_ = lean_alloc_ctor(1, 0, 1);
v___x_392_ = lean_unbox(v_defValue_388_);
lean_ctor_set_uint8(v___x_391_, 0, v___x_392_);
lean_inc(v_deprecation_x3f_390_);
lean_inc_ref(v_descr_389_);
lean_inc_n(v_name_384_, 2);
v___x_393_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_393_, 0, v_name_384_);
lean_ctor_set(v___x_393_, 1, v_ref_386_);
lean_ctor_set(v___x_393_, 2, v___x_391_);
lean_ctor_set(v___x_393_, 3, v_descr_389_);
lean_ctor_set(v___x_393_, 4, v_deprecation_x3f_390_);
v___x_394_ = lean_register_option(v_name_384_, v___x_393_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_402_; 
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; 
v_unused_403_ = lean_ctor_get(v___x_394_, 0);
lean_dec(v_unused_403_);
v___x_396_ = v___x_394_;
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
else
{
lean_dec(v___x_394_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_402_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
lean_inc(v_defValue_388_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v_name_384_);
lean_ctor_set(v___x_398_, 1, v_defValue_388_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_398_);
v___x_400_ = v___x_396_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec(v_name_384_);
v_a_404_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_394_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_394_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_412_, lean_object* v_decl_413_, lean_object* v_ref_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v_name_412_, v_decl_413_, v_ref_414_);
lean_dec_ref(v_decl_413_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_434_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_435_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_436_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_));
v___x_437_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_434_, v___x_435_, v___x_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4____boxed(lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4_();
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_456_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_457_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_458_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_));
v___x_459_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_456_, v___x_457_, v___x_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4____boxed(lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3810413623____hygCtx___hyg_4_();
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_478_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_479_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_480_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_));
v___x_481_ = l_Lean_Option_register___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_3413348210____hygCtx___hyg_4__spec__0(v___x_478_, v___x_479_, v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4____boxed(lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_1194077636____hygCtx___hyg_4_();
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_));
v___x_488_ = lean_st_mk_ref(v___x_487_);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2____boxed(lean_object* v_a_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_2175836875____hygCtx___hyg_2_();
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_addEnvLinterOption(lean_object* v_opt_492_){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_494_ = l_Lean_Linter_envLinterOptionsRef;
v___x_495_ = lean_st_ref_take(v___x_494_);
v___x_496_ = lean_array_push(v___x_495_, v_opt_492_);
v___x_497_ = lean_st_ref_put(v___x_494_, v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_addEnvLinterOption___boxed(lean_object* v_opt_499_, lean_object* v_a_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Linter_addEnvLinterOption(v_opt_499_);
return v_res_501_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(lean_object* v_o_502_, lean_object* v_k_503_, uint8_t v_defVal_504_){
_start:
{
lean_object* v_toOptions_505_; lean_object* v_map_506_; lean_object* v___x_507_; 
v_toOptions_505_ = lean_ctor_get(v_o_502_, 0);
v_map_506_ = lean_ctor_get(v_toOptions_505_, 0);
v___x_507_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_506_, v_k_503_);
if (lean_obj_tag(v___x_507_) == 0)
{
return v_defVal_504_;
}
else
{
lean_object* v_val_508_; 
v_val_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v___x_507_, 1);
if (lean_obj_tag(v_val_508_) == 1)
{
uint8_t v_v_509_; 
v_v_509_ = lean_ctor_get_uint8(v_val_508_, 0);
lean_dec_ref_known(v_val_508_, 0);
return v_v_509_;
}
else
{
lean_dec(v_val_508_);
return v_defVal_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0___boxed(lean_object* v_o_510_, lean_object* v_k_511_, lean_object* v_defVal_512_){
_start:
{
uint8_t v_defVal_boxed_513_; uint8_t v_res_514_; lean_object* v_r_515_; 
v_defVal_boxed_513_ = lean_unbox(v_defVal_512_);
v_res_514_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_510_, v_k_511_, v_defVal_boxed_513_);
lean_dec(v_k_511_);
lean_dec_ref(v_o_510_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterAll(lean_object* v_o_516_, uint8_t v_defValue_517_){
_start:
{
lean_object* v___x_518_; lean_object* v_name_519_; uint8_t v___x_520_; 
v___x_518_ = l_Lean_Linter_linter_all;
v_name_519_ = lean_ctor_get(v___x_518_, 0);
v___x_520_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_516_, v_name_519_, v_defValue_517_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterAll___boxed(lean_object* v_o_521_, lean_object* v_defValue_522_){
_start:
{
uint8_t v_defValue_boxed_523_; uint8_t v_res_524_; lean_object* v_r_525_; 
v_defValue_boxed_523_ = lean_unbox(v_defValue_522_);
v_res_524_ = l_Lean_Linter_getLinterAll(v_o_521_, v_defValue_boxed_523_);
lean_dec_ref(v_o_521_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(lean_object* v_o_526_, lean_object* v_k_527_){
_start:
{
lean_object* v_toOptions_528_; lean_object* v_map_529_; lean_object* v___x_530_; 
v_toOptions_528_ = lean_ctor_get(v_o_526_, 0);
v_map_529_ = lean_ctor_get(v_toOptions_528_, 0);
v___x_530_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_529_, v_k_527_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v___x_531_; 
v___x_531_ = lean_box(0);
return v___x_531_;
}
else
{
lean_object* v_val_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_542_; 
v_val_532_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_542_ == 0)
{
v___x_534_ = v___x_530_;
v_isShared_535_ = v_isSharedCheck_542_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_val_532_);
lean_dec(v___x_530_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_542_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
if (lean_obj_tag(v_val_532_) == 1)
{
uint8_t v_v_536_; lean_object* v___x_537_; lean_object* v___x_539_; 
v_v_536_ = lean_ctor_get_uint8(v_val_532_, 0);
lean_dec_ref_known(v_val_532_, 0);
v___x_537_ = lean_box(v_v_536_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v___x_537_);
v___x_539_ = v___x_534_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
else
{
lean_object* v___x_541_; 
lean_del_object(v___x_534_);
lean_dec(v_val_532_);
v___x_541_ = lean_box(0);
return v___x_541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0___boxed(lean_object* v_o_543_, lean_object* v_k_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_543_, v_k_544_);
lean_dec(v_k_544_);
lean_dec_ref(v_o_543_);
return v_res_545_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
if (lean_obj_tag(v_x_547_) == 0)
{
uint8_t v___x_548_; 
v___x_548_ = 1;
return v___x_548_;
}
else
{
uint8_t v___x_549_; 
v___x_549_ = 0;
return v___x_549_;
}
}
else
{
if (lean_obj_tag(v_x_547_) == 0)
{
uint8_t v___x_550_; 
v___x_550_ = 0;
return v___x_550_;
}
else
{
lean_object* v_val_551_; uint8_t v___x_552_; 
v_val_551_ = lean_ctor_get(v_x_547_, 0);
v___x_552_ = lean_unbox(v_val_551_);
if (v___x_552_ == 0)
{
lean_object* v_val_553_; uint8_t v___x_554_; 
v_val_553_ = lean_ctor_get(v_x_546_, 0);
v___x_554_ = lean_unbox(v_val_553_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; 
v___x_555_ = 1;
return v___x_555_;
}
else
{
uint8_t v___x_556_; 
v___x_556_ = lean_unbox(v_val_551_);
return v___x_556_;
}
}
else
{
lean_object* v_val_557_; uint8_t v___x_558_; 
v_val_557_ = lean_ctor_get(v_x_546_, 0);
v___x_558_ = lean_unbox(v_val_557_);
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1___boxed(lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
uint8_t v_res_561_; lean_object* v_r_562_; 
v_res_561_ = l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(v_x_559_, v_x_560_);
lean_dec(v_x_560_);
lean_dec(v_x_559_);
v_r_562_ = lean_box(v_res_561_);
return v_r_562_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(lean_object* v_o_566_, lean_object* v_as_567_, size_t v_i_568_, size_t v_stop_569_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = lean_usize_dec_eq(v_i_568_, v_stop_569_);
if (v___x_570_ == 0)
{
uint8_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_571_ = 1;
v___x_572_ = lean_array_uget_borrowed(v_as_567_, v_i_568_);
v___x_573_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_566_, v___x_572_);
v___x_574_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0));
v___x_575_ = l_instBEqOption_beq___at___00Lean_Linter_getLinterValue_spec__1(v___x_573_, v___x_574_);
lean_dec(v___x_573_);
if (v___x_575_ == 0)
{
size_t v___x_576_; size_t v___x_577_; 
v___x_576_ = ((size_t)1ULL);
v___x_577_ = lean_usize_add(v_i_568_, v___x_576_);
v_i_568_ = v___x_577_;
goto _start;
}
else
{
return v___x_571_;
}
}
else
{
uint8_t v___x_579_; 
v___x_579_ = 0;
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___boxed(lean_object* v_o_580_, lean_object* v_as_581_, lean_object* v_i_582_, lean_object* v_stop_583_){
_start:
{
size_t v_i_boxed_584_; size_t v_stop_boxed_585_; uint8_t v_res_586_; lean_object* v_r_587_; 
v_i_boxed_584_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_stop_boxed_585_ = lean_unbox_usize(v_stop_583_);
lean_dec(v_stop_583_);
v_res_586_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_580_, v_as_581_, v_i_boxed_584_, v_stop_boxed_585_);
lean_dec_ref(v_as_581_);
lean_dec_ref(v_o_580_);
v_r_587_ = lean_box(v_res_586_);
return v_r_587_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterValue(lean_object* v_opt_588_, lean_object* v_o_589_){
_start:
{
lean_object* v_name_590_; lean_object* v_defValue_591_; uint8_t v___y_593_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_name_590_ = lean_ctor_get(v_opt_588_, 0);
v_defValue_591_ = lean_ctor_get(v_opt_588_, 1);
v___x_596_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_589_, v_opt_588_);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_array_get_size(v___x_596_);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
uint8_t v___x_600_; 
lean_dec(v___x_596_);
v___x_600_ = lean_unbox(v_defValue_591_);
v___y_593_ = v___x_600_;
goto v___jp_592_;
}
else
{
if (v___x_599_ == 0)
{
uint8_t v___x_601_; 
lean_dec(v___x_596_);
v___x_601_ = lean_unbox(v_defValue_591_);
v___y_593_ = v___x_601_;
goto v___jp_592_;
}
else
{
size_t v___x_602_; size_t v___x_603_; uint8_t v___x_604_; 
v___x_602_ = ((size_t)0ULL);
v___x_603_ = lean_usize_of_nat(v___x_598_);
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_589_, v___x_596_, v___x_602_, v___x_603_);
lean_dec(v___x_596_);
if (v___x_604_ == 0)
{
uint8_t v___x_605_; 
v___x_605_ = lean_unbox(v_defValue_591_);
v___y_593_ = v___x_605_;
goto v___jp_592_;
}
else
{
v___y_593_ = v___x_604_;
goto v___jp_592_;
}
}
}
v___jp_592_:
{
uint8_t v___x_594_; uint8_t v___x_595_; 
v___x_594_ = l_Lean_Linter_getLinterAll(v_o_589_, v___y_593_);
v___x_595_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_589_, v_name_590_, v___x_594_);
return v___x_595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterValue___boxed(lean_object* v_opt_606_, lean_object* v_o_607_){
_start:
{
uint8_t v_res_608_; lean_object* v_r_609_; 
v_res_608_ = l_Lean_Linter_getLinterValue(v_opt_606_, v_o_607_);
lean_dec_ref(v_o_607_);
lean_dec_ref(v_opt_606_);
v_r_609_ = lean_box(v_res_608_);
return v_r_609_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_isLinterEnabledByOptions(lean_object* v_name_610_, lean_object* v_o_611_){
_start:
{
uint8_t v___y_613_; lean_object* v_linterSets_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v_linterSets_616_ = lean_ctor_get(v_o_611_, 1);
v___x_617_ = lean_unsigned_to_nat(0u);
v___x_618_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_619_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_linterSets_616_, v_name_610_, v___x_618_);
v___x_620_ = lean_array_get_size(v___x_619_);
v___x_621_ = lean_nat_dec_lt(v___x_617_, v___x_620_);
if (v___x_621_ == 0)
{
lean_dec(v___x_619_);
v___y_613_ = v___x_621_;
goto v___jp_612_;
}
else
{
if (v___x_621_ == 0)
{
lean_dec(v___x_619_);
v___y_613_ = v___x_621_;
goto v___jp_612_;
}
else
{
size_t v___x_622_; size_t v___x_623_; uint8_t v___x_624_; 
v___x_622_ = ((size_t)0ULL);
v___x_623_ = lean_usize_of_nat(v___x_620_);
v___x_624_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_611_, v___x_619_, v___x_622_, v___x_623_);
lean_dec(v___x_619_);
v___y_613_ = v___x_624_;
goto v___jp_612_;
}
}
v___jp_612_:
{
uint8_t v___x_614_; uint8_t v___x_615_; 
v___x_614_ = l_Lean_Linter_getLinterAll(v_o_611_, v___y_613_);
v___x_615_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_611_, v_name_610_, v___x_614_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_isLinterEnabledByOptions___boxed(lean_object* v_name_625_, lean_object* v_o_626_){
_start:
{
uint8_t v_res_627_; lean_object* v_r_628_; 
v_res_627_ = l_Lean_Linter_isLinterEnabledByOptions(v_name_625_, v_o_626_);
lean_dec_ref(v_o_626_);
lean_dec(v_name_625_);
v_r_628_ = lean_box(v_res_627_);
return v_r_628_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___redArg___closed__1(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = ((lean_object*)(l_Lean_Linter_logLint___redArg___closed__0));
v___x_637_ = l_Lean_stringToMessageData(v___x_636_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___redArg___closed__3(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_Linter_logLint___redArg___closed__2));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___redArg(lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_inst_644_, lean_object* v_linterOption_645_, lean_object* v_stx_646_, lean_object* v_msg_647_){
_start:
{
lean_object* v_name_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_666_; 
v_name_648_ = lean_ctor_get(v_linterOption_645_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v_linterOption_645_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v_linterOption_645_, 1);
lean_dec(v_unused_667_);
v___x_650_ = v_linterOption_645_;
v_isShared_651_ = v_isSharedCheck_666_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_name_648_);
lean_dec(v_linterOption_645_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_666_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_652_ = lean_obj_once(&l_Lean_Linter_logLint___redArg___closed__1, &l_Lean_Linter_logLint___redArg___closed__1_once, _init_l_Lean_Linter_logLint___redArg___closed__1);
lean_inc(v_name_648_);
v___x_653_ = l_Lean_MessageData_ofName(v_name_648_);
if (v_isShared_651_ == 0)
{
lean_ctor_set_tag(v___x_650_, 7);
lean_ctor_set(v___x_650_, 1, v___x_653_);
lean_ctor_set(v___x_650_, 0, v___x_652_);
v___x_655_ = v___x_650_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v___x_653_);
v___x_655_ = v_reuseFailAlloc_665_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_disable_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_656_ = lean_obj_once(&l_Lean_Linter_logLint___redArg___closed__3, &l_Lean_Linter_logLint___redArg___closed__3_once, _init_l_Lean_Linter_logLint___redArg___closed__3);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_655_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v_disable_658_ = l_Lean_MessageData_note(v___x_657_);
v___x_659_ = ((lean_object*)(l_Lean_Linter_linterMessageTag));
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v_msg_647_);
lean_ctor_set(v___x_660_, 1, v_disable_658_);
v___x_661_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
v___x_662_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_662_, 0, v_name_648_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
lean_inc(v_stx_646_);
v___x_663_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_663_, 0, v_stx_646_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = l_Lean_logWarningAt___redArg(v_inst_641_, v_inst_642_, v_inst_643_, v_inst_644_, v_stx_646_, v___x_663_);
return v___x_664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint(lean_object* v_m_668_, lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_linterOption_673_, lean_object* v_stx_674_, lean_object* v_msg_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_Linter_logLint___redArg(v_inst_669_, v_inst_670_, v_inst_671_, v_inst_672_, v_linterOption_673_, v_stx_674_, v_msg_675_);
return v___x_676_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isLinterMessage___lam__0(lean_object* v_x_677_){
_start:
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = ((lean_object*)(l_Lean_Linter_linterMessageTag));
v___x_679_ = lean_name_eq(v_x_677_, v___x_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isLinterMessage___lam__0___boxed(lean_object* v_x_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Lean_MessageData_isLinterMessage___lam__0(v_x_680_);
lean_dec(v_x_680_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT uint8_t l_Lean_MessageData_isLinterMessage(lean_object* v_msg_684_){
_start:
{
lean_object* v___f_685_; uint8_t v___x_686_; 
v___f_685_ = ((lean_object*)(l_Lean_MessageData_isLinterMessage___closed__0));
v___x_686_ = l_Lean_MessageData_hasTag(v___f_685_, v_msg_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_isLinterMessage___boxed(lean_object* v_msg_687_){
_start:
{
uint8_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_Lean_MessageData_isLinterMessage(v_msg_687_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0(lean_object* v_linterOption_690_, lean_object* v_toPure_691_, lean_object* v_inst_692_, lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_inst_695_, lean_object* v_stx_696_, lean_object* v_msg_697_, lean_object* v_____do__lift_698_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_Linter_getLinterValue(v_linterOption_690_, v_____do__lift_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec_ref(v_msg_697_);
lean_dec(v_stx_696_);
lean_dec_ref(v_inst_695_);
lean_dec(v_inst_694_);
lean_dec_ref(v_inst_693_);
lean_dec_ref(v_inst_692_);
lean_dec_ref(v_linterOption_690_);
v___x_700_ = lean_box(0);
v___x_701_ = lean_apply_2(v_toPure_691_, lean_box(0), v___x_700_);
return v___x_701_;
}
else
{
lean_object* v___x_702_; 
lean_dec(v_toPure_691_);
v___x_702_ = l_Lean_Linter_logLint___redArg(v_inst_692_, v_inst_693_, v_inst_694_, v_inst_695_, v_linterOption_690_, v_stx_696_, v_msg_697_);
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0___boxed(lean_object* v_linterOption_703_, lean_object* v_toPure_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_stx_709_, lean_object* v_msg_710_, lean_object* v_____do__lift_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Linter_logLintIf___redArg___lam__0(v_linterOption_703_, v_toPure_704_, v_inst_705_, v_inst_706_, v_inst_707_, v_inst_708_, v_stx_709_, v_msg_710_, v_____do__lift_711_);
lean_dec_ref(v_____do__lift_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg(lean_object* v_inst_713_, lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_inst_717_, lean_object* v_linterOption_718_, lean_object* v_stx_719_, lean_object* v_msg_720_){
_start:
{
lean_object* v_toApplicative_721_; lean_object* v_toBind_722_; lean_object* v_toPure_723_; lean_object* v___x_724_; lean_object* v___f_725_; lean_object* v___x_726_; 
v_toApplicative_721_ = lean_ctor_get(v_inst_713_, 0);
v_toBind_722_ = lean_ctor_get(v_inst_713_, 1);
lean_inc(v_toBind_722_);
v_toPure_723_ = lean_ctor_get(v_toApplicative_721_, 1);
lean_inc(v_toPure_723_);
lean_inc_ref(v_inst_716_);
lean_inc_ref(v_inst_713_);
v___x_724_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_713_, v_inst_716_, v_inst_717_);
v___f_725_ = lean_alloc_closure((void*)(l_Lean_Linter_logLintIf___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_725_, 0, v_linterOption_718_);
lean_closure_set(v___f_725_, 1, v_toPure_723_);
lean_closure_set(v___f_725_, 2, v_inst_713_);
lean_closure_set(v___f_725_, 3, v_inst_714_);
lean_closure_set(v___f_725_, 4, v_inst_715_);
lean_closure_set(v___f_725_, 5, v_inst_716_);
lean_closure_set(v___f_725_, 6, v_stx_719_);
lean_closure_set(v___f_725_, 7, v_msg_720_);
v___x_726_ = lean_apply_4(v_toBind_722_, lean_box(0), lean_box(0), v___x_724_, v___f_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf(lean_object* v_m_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_linterOption_733_, lean_object* v_stx_734_, lean_object* v_msg_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Linter_logLintIf___redArg(v_inst_728_, v_inst_729_, v_inst_730_, v_inst_731_, v_inst_732_, v_linterOption_733_, v_stx_734_, v_msg_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(lean_object* v_env_737_, lean_object* v_as_738_, size_t v_i_739_, size_t v_stop_740_, lean_object* v_b_741_){
_start:
{
lean_object* v___y_743_; uint8_t v___x_747_; 
v___x_747_ = lean_usize_dec_eq(v_i_739_, v_stop_740_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; lean_object* v_fst_749_; uint8_t v___x_750_; 
v___x_748_ = lean_array_uget_borrowed(v_as_738_, v_i_739_);
v_fst_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_fst_749_);
lean_inc_ref(v_env_737_);
v___x_750_ = l_Lean_Environment_contains(v_env_737_, v_fst_749_, v___x_747_);
if (v___x_750_ == 0)
{
v___y_743_ = v_b_741_;
goto v___jp_742_;
}
else
{
lean_object* v___x_751_; 
lean_inc(v___x_748_);
v___x_751_ = lean_array_push(v_b_741_, v___x_748_);
v___y_743_ = v___x_751_;
goto v___jp_742_;
}
}
else
{
lean_dec_ref(v_env_737_);
return v_b_741_;
}
v___jp_742_:
{
size_t v___x_744_; size_t v___x_745_; 
v___x_744_ = ((size_t)1ULL);
v___x_745_ = lean_usize_add(v_i_739_, v___x_744_);
v_i_739_ = v___x_745_;
v_b_741_ = v___y_743_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_752_, lean_object* v_as_753_, lean_object* v_i_754_, lean_object* v_stop_755_, lean_object* v_b_756_){
_start:
{
size_t v_i_boxed_757_; size_t v_stop_boxed_758_; lean_object* v_res_759_; 
v_i_boxed_757_ = lean_unbox_usize(v_i_754_);
lean_dec(v_i_754_);
v_stop_boxed_758_ = lean_unbox_usize(v_stop_755_);
lean_dec(v_stop_755_);
v_res_759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_752_, v_as_753_, v_i_boxed_757_, v_stop_boxed_758_, v_b_756_);
lean_dec_ref(v_as_753_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_760_, lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_object* v_k_762_; lean_object* v_v_763_; lean_object* v_l_764_; lean_object* v_r_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_k_762_ = lean_ctor_get(v_x_761_, 1);
v_v_763_ = lean_ctor_get(v_x_761_, 2);
v_l_764_ = lean_ctor_get(v_x_761_, 3);
v_r_765_ = lean_ctor_get(v_x_761_, 4);
v___x_766_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_760_, v_l_764_);
lean_inc(v_v_763_);
lean_inc(v_k_762_);
v___x_767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_767_, 0, v_k_762_);
lean_ctor_set(v___x_767_, 1, v_v_763_);
v___x_768_ = lean_array_push(v___x_766_, v___x_767_);
v_init_760_ = v___x_768_;
v_x_761_ = v_r_765_;
goto _start;
}
else
{
return v_init_760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_770_, lean_object* v_x_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_770_, v_x_771_);
lean_dec(v_x_771_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(lean_object* v_env_777_, lean_object* v_s_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_781_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v___x_780_, v_s_778_);
v___x_782_ = lean_array_get_size(v___x_781_);
v___x_783_ = ((lean_object*)(l_Lean_Linter_instInhabitedLinterSetsState_default___closed__0));
v___x_784_ = lean_nat_dec_lt(v___x_779_, v___x_782_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec_ref(v___x_781_);
lean_dec_ref(v_env_777_);
v___x_785_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
return v___x_785_;
}
else
{
uint8_t v___x_786_; 
v___x_786_ = lean_nat_dec_le(v___x_782_, v___x_782_);
if (v___x_786_ == 0)
{
if (v___x_784_ == 0)
{
lean_object* v___x_787_; 
lean_dec_ref(v___x_781_);
lean_dec_ref(v_env_777_);
v___x_787_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0___closed__1_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
return v___x_787_;
}
else
{
size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_788_ = ((size_t)0ULL);
v___x_789_ = lean_usize_of_nat(v___x_782_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_777_, v___x_781_, v___x_788_, v___x_789_, v___x_783_);
lean_dec_ref(v___x_781_);
lean_inc_ref_n(v___x_790_, 2);
v___x_791_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
lean_ctor_set(v___x_791_, 2, v___x_790_);
return v___x_791_;
}
}
else
{
size_t v___x_792_; size_t v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_792_ = ((size_t)0ULL);
v___x_793_ = lean_usize_of_nat(v___x_782_);
v___x_794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__1(v_env_777_, v___x_781_, v___x_792_, v___x_793_, v___x_783_);
lean_dec_ref(v___x_781_);
lean_inc_ref_n(v___x_794_, 2);
v___x_795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
lean_ctor_set(v___x_795_, 2, v___x_794_);
return v___x_795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed(lean_object* v_env_796_, lean_object* v_s_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(v_env_796_, v_s_797_);
lean_dec(v_s_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___f_804_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_805_ = ((lean_object*)(l___private_Lean_Linter_Init_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_));
v___x_806_ = lean_box(0);
v___x_807_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_805_, v___x_806_, v___f_804_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2____boxed(lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l___private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2_();
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0(lean_object* v_init_810_, lean_object* v_t_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0_spec__0(v_init_810_, v_t_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_813_, lean_object* v_t_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Linter_Init_0__Lean_Linter_initFn_00___x40_Lean_Linter_Init_4120500210____hygCtx___hyg_2__spec__0(v_init_813_, v_t_814_);
lean_dec(v_t_814_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(lean_object* v_env_816_, lean_object* v_declName_817_, lean_object* v_optName_818_){
_start:
{
lean_object* v___x_819_; lean_object* v_toEnvExtension_820_; lean_object* v_asyncMode_821_; lean_object* v___x_822_; uint8_t v___x_823_; lean_object* v___x_824_; 
v___x_819_ = l_Lean_Linter_envLinterSnapshotExt;
v_toEnvExtension_820_ = lean_ctor_get(v___x_819_, 0);
v_asyncMode_821_ = lean_ctor_get(v_toEnvExtension_820_, 2);
v___x_822_ = lean_box(1);
v___x_823_ = 0;
v___x_824_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_822_, v___x_819_, v_env_816_, v_declName_817_, v_asyncMode_821_, v___x_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v___x_825_; 
v___x_825_ = lean_box(0);
return v___x_825_;
}
else
{
lean_object* v_val_826_; lean_object* v___x_827_; 
v_val_826_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_val_826_);
lean_dec_ref_known(v___x_824_, 1);
v___x_827_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_826_, v_optName_818_);
lean_dec(v_val_826_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getEnvLinterSnapshotEntry_x3f___boxed(lean_object* v_env_828_, lean_object* v_declName_829_, lean_object* v_optName_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Linter_getEnvLinterSnapshotEntry_x3f(v_env_828_, v_declName_829_, v_optName_830_);
lean_dec(v_optName_830_);
return v_res_831_;
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
