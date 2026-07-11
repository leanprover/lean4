// Lean compiler output
// Module: Lean.Linter.EnvLinter.Basic
// Imports: public import Lean.Elab.InfoTree.Main public import Lean.AutoDecl
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
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(44, 32, 157, 0, 199, 45, 83, 147)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "envLinterExt"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 34, 157, 198, 119, 92, 66, 12)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_envLinterExt;
static const lean_string_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "builtin_env_linter"};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_2),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 180, 153, 91, 141, 98, 2, 80)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value;
static const lean_string_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3_value;
static const lean_string_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "builtin_env_linter "};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5_value;
static const lean_string_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__3_value),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__5_value),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__8_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__9_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` must have type `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "`, got `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " but is only marked `meta`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "invalid attribute `builtin_env_linter`, declaration `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "` must be marked as `public` and `meta`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " but is only marked `public`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "invalid attribute `builtin_env_linter`, linter `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "invalid attribute `builtin_env_linter`, no constant named `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`; did you forget `register_builtin_option "};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " : Bool := ...`\?"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "invalid `builtin_env_linter` syntax: expected an option name argument"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__33_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "invalid attribute `builtin_env_linter`, must be global"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__33_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__33_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__34_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__34_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(196, 60, 89, 104, 222, 184, 104, 61)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(255, 77, 64, 120, 151, 50, 41, 244)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 75, 158, 206, 205, 238, 69, 21)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(137, 12, 34, 233, 215, 60, 102, 16)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 210, 128, 199, 109, 85, 222, 11)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(202, 197, 79, 202, 254, 40, 158, 224)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(209, 170, 47, 185, 53, 142, 137, 13)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 191, 200, 41, 134, 97, 182, 145)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 137, 166, 37, 185, 248, 93, 214)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 129, 252, 190, 49, 60, 207)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(186, 162, 40, 223, 118, 24, 158, 134)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(129, 50, 203, 113, 71, 15, 125, 124)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 43, 132, 57, 147, 43, 102, 84)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed, .m_arity = 14, .m_num_fixed = 8, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value)} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 8, 91, 236, 76, 189, 200, 47)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Use this declaration as a linting test in `lake builtin-lint`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_abortCommandExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
return v_res_8_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_9_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_13_ = lean_unsigned_to_nat(0u);
v___x_14_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
lean_ctor_set(v___x_14_, 2, v___x_13_);
lean_ctor_set(v___x_14_, 3, v___x_13_);
lean_ctor_set(v___x_14_, 4, v___x_12_);
lean_ctor_set(v___x_14_, 5, v___x_12_);
lean_ctor_set(v___x_14_, 6, v___x_12_);
lean_ctor_set(v___x_14_, 7, v___x_12_);
lean_ctor_set(v___x_14_, 8, v___x_12_);
lean_ctor_set(v___x_14_, 9, v___x_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_unsigned_to_nat(32u);
v___x_16_ = lean_mk_empty_array_with_capacity(v___x_15_);
v___x_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_18_ = ((size_t)5ULL);
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = lean_unsigned_to_nat(32u);
v___x_21_ = lean_mk_empty_array_with_capacity(v___x_20_);
v___x_22_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_23_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v___x_21_);
lean_ctor_set(v___x_23_, 2, v___x_19_);
lean_ctor_set(v___x_23_, 3, v___x_19_);
lean_ctor_set_usize(v___x_23_, 4, v___x_18_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_24_ = lean_box(1);
v___x_25_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_26_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_27_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v___x_25_);
lean_ctor_set(v___x_27_, 2, v___x_24_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v___x_32_; lean_object* v_env_33_; lean_object* v_options_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_32_ = lean_st_ref_get(v___y_30_);
v_env_33_ = lean_ctor_get(v___x_32_, 0);
lean_inc_ref(v_env_33_);
lean_dec(v___x_32_);
v_options_34_ = lean_ctor_get(v___y_29_, 2);
v___x_35_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_36_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_34_);
v___x_37_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_37_, 0, v_env_33_);
lean_ctor_set(v___x_37_, 1, v___x_35_);
lean_ctor_set(v___x_37_, 2, v___x_36_);
lean_ctor_set(v___x_37_, 3, v_options_34_);
v___x_38_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v_msgData_28_);
v___x_39_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msgData_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_ref_49_; lean_object* v___x_50_; lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_59_; 
v_ref_49_ = lean_ctor_get(v___y_46_, 5);
v___x_50_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3(v_msg_45_, v___y_46_, v___y_47_);
v_a_51_ = lean_ctor_get(v___x_50_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_59_ == 0)
{
v___x_53_ = v___x_50_;
v_isShared_54_ = v_isSharedCheck_59_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_50_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_59_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_55_; lean_object* v___x_57_; 
lean_inc(v_ref_49_);
v___x_55_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_55_, 0, v_ref_49_);
lean_ctor_set(v___x_55_, 1, v_a_51_);
if (v_isShared_54_ == 0)
{
lean_ctor_set_tag(v___x_53_, 1);
lean_ctor_set(v___x_53_, 0, v___x_55_);
v___x_57_ = v___x_53_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_60_, v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(lean_object* v_x_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v_a_69_ = lean_ctor_get(v_x_65_, 0);
lean_inc(v_a_69_);
lean_dec_ref_known(v_x_65_, 1);
v___x_70_ = l_Lean_stringToMessageData(v_a_69_);
v___x_71_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_70_, v___y_66_, v___y_67_);
return v___x_71_;
}
else
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
v_a_72_ = lean_ctor_get(v_x_65_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v_x_65_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v_x_65_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v_x_65_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
lean_ctor_set_tag(v___x_74_, 0);
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg___boxed(lean_object* v_x_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v_x_80_, v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(lean_object* v_typeName_85_, lean_object* v_constName_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; lean_object* v_env_91_; uint8_t v___x_92_; 
v___x_90_ = lean_st_ref_get(v___y_88_);
v_env_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_env_91_);
lean_dec(v___x_90_);
lean_inc(v_constName_86_);
v___x_92_ = lean_has_compile_error(v_env_91_, v_constName_86_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; lean_object* v_env_94_; lean_object* v_options_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_93_ = lean_st_ref_get(v___y_88_);
v_env_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_env_94_);
lean_dec(v___x_93_);
v_options_95_ = lean_ctor_get(v___y_87_, 2);
v___x_96_ = l_Lean_Environment_evalConstCheck___redArg(v_env_94_, v_options_95_, v_typeName_85_, v_constName_86_);
v___x_97_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v___x_96_, v___y_87_, v___y_88_);
return v___x_97_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v___x_99_; lean_object* v_env_100_; lean_object* v_options_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec_ref_known(v___x_98_, 1);
v___x_99_ = lean_st_ref_get(v___y_88_);
v_env_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc_ref(v_env_100_);
lean_dec(v___x_99_);
v_options_101_ = lean_ctor_get(v___y_87_, 2);
v___x_102_ = l_Lean_Environment_evalConstCheck___redArg(v_env_100_, v_options_101_, v_typeName_85_, v_constName_86_);
v___x_103_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v___x_102_, v___y_87_, v___y_88_);
return v___x_103_;
}
else
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_111_; 
lean_dec(v_constName_86_);
lean_dec(v_typeName_85_);
v_a_104_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_111_ == 0)
{
v___x_106_ = v___x_98_;
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v___x_98_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_111_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_a_104_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg___boxed(lean_object* v_typeName_112_, lean_object* v_constName_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(v_typeName_112_, v_constName_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(lean_object* v_optName_125_, lean_object* v_declName_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3));
lean_inc(v_declName_126_);
v___x_131_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(v___x_130_, v_declName_126_, v_a_127_, v_a_128_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_140_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_140_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_140_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_136_, 0, v_a_132_);
lean_ctor_set(v___x_136_, 1, v_optName_125_);
lean_ctor_set(v___x_136_, 2, v_declName_126_);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_136_);
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v___x_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec(v_declName_126_);
lean_dec(v_optName_125_);
v_a_141_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_131_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_131_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___boxed(lean_object* v_optName_149_, lean_object* v_declName_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(v_optName_149_, v_declName_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1(lean_object* v_00_u03b1_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___redArg();
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1___boxed(lean_object* v_00_u03b1_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__1(v_00_u03b1_160_, v___y_161_, v___y_162_);
lean_dec(v___y_162_);
lean_dec_ref(v___y_161_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0(lean_object* v_00_u03b1_165_, lean_object* v_typeName_166_, lean_object* v_constName_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___redArg(v_typeName_166_, v_constName_167_, v___y_168_, v___y_169_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0___boxed(lean_object* v_00_u03b1_172_, lean_object* v_typeName_173_, lean_object* v_constName_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0(v_00_u03b1_172_, v_typeName_173_, v_constName_174_, v___y_175_, v___y_176_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0(lean_object* v_00_u03b1_179_, lean_object* v_x_180_, lean_object* v___y_181_, lean_object* v___y_182_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___redArg(v_x_180_, v___y_181_, v___y_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0___boxed(lean_object* v_00_u03b1_185_, lean_object* v_x_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0(v_00_u03b1_185_, v_x_186_, v___y_187_, v___y_188_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_191_, lean_object* v_msg_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_192_, v___y_193_, v___y_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_197_, lean_object* v_msg_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1(v_00_u03b1_197_, v_msg_198_, v___y_199_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v___y_199_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter(lean_object* v_optName_203_, lean_object* v_declName_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(v_optName_203_, v_declName_204_, v_a_205_, v_a_206_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter___boxed(lean_object* v_optName_209_, lean_object* v_declName_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Linter_EnvLinter_getEnvLinter(v_optName_209_, v_declName_210_, v_a_211_, v_a_212_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object* v_m_215_, lean_object* v_x_216_){
_start:
{
lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v___x_219_; 
v_fst_217_ = lean_ctor_get(v_x_216_, 0);
lean_inc(v_fst_217_);
v_snd_218_ = lean_ctor_get(v_x_216_, 1);
lean_inc(v_snd_218_);
lean_dec_ref(v_x_216_);
v___x_219_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_217_, v_snd_218_, v_m_215_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_220_, size_t v_i_221_, size_t v_stop_222_, lean_object* v_b_223_){
_start:
{
uint8_t v___x_224_; 
v___x_224_ = lean_usize_dec_eq(v_i_221_, v_stop_222_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v_fst_226_; lean_object* v_snd_227_; lean_object* v___x_228_; size_t v___x_229_; size_t v___x_230_; 
v___x_225_ = lean_array_uget_borrowed(v_as_220_, v_i_221_);
v_fst_226_ = lean_ctor_get(v___x_225_, 0);
v_snd_227_ = lean_ctor_get(v___x_225_, 1);
lean_inc(v_snd_227_);
lean_inc(v_fst_226_);
v___x_228_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_226_, v_snd_227_, v_b_223_);
v___x_229_ = ((size_t)1ULL);
v___x_230_ = lean_usize_add(v_i_221_, v___x_229_);
v_i_221_ = v___x_230_;
v_b_223_ = v___x_228_;
goto _start;
}
else
{
return v_b_223_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_232_, lean_object* v_i_233_, lean_object* v_stop_234_, lean_object* v_b_235_){
_start:
{
size_t v_i_boxed_236_; size_t v_stop_boxed_237_; lean_object* v_res_238_; 
v_i_boxed_236_ = lean_unbox_usize(v_i_233_);
lean_dec(v_i_233_);
v_stop_boxed_237_ = lean_unbox_usize(v_stop_234_);
lean_dec(v_stop_234_);
v_res_238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0_spec__0(v_as_232_, v_i_boxed_236_, v_stop_boxed_237_, v_b_235_);
lean_dec_ref(v_as_232_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0(lean_object* v_as_239_, size_t v_i_240_, size_t v_stop_241_, lean_object* v_b_242_){
_start:
{
uint8_t v___x_243_; 
v___x_243_ = lean_usize_dec_eq(v_i_240_, v_stop_241_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v_fst_245_; lean_object* v_snd_246_; lean_object* v___x_247_; size_t v___x_248_; size_t v___x_249_; lean_object* v___x_250_; 
v___x_244_ = lean_array_uget_borrowed(v_as_239_, v_i_240_);
v_fst_245_ = lean_ctor_get(v___x_244_, 0);
v_snd_246_ = lean_ctor_get(v___x_244_, 1);
lean_inc(v_snd_246_);
lean_inc(v_fst_245_);
v___x_247_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_245_, v_snd_246_, v_b_242_);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_add(v_i_240_, v___x_248_);
v___x_250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0_spec__0(v_as_239_, v___x_249_, v_stop_241_, v___x_247_);
return v___x_250_;
}
else
{
return v_b_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_251_, lean_object* v_i_252_, lean_object* v_stop_253_, lean_object* v_b_254_){
_start:
{
size_t v_i_boxed_255_; size_t v_stop_boxed_256_; lean_object* v_res_257_; 
v_i_boxed_255_ = lean_unbox_usize(v_i_252_);
lean_dec(v_i_252_);
v_stop_boxed_256_ = lean_unbox_usize(v_stop_253_);
lean_dec(v_stop_253_);
v_res_257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0(v_as_251_, v_i_boxed_255_, v_stop_boxed_256_, v_b_254_);
lean_dec_ref(v_as_251_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(lean_object* v_as_258_, size_t v_i_259_, size_t v_stop_260_, lean_object* v_b_261_){
_start:
{
lean_object* v___y_263_; uint8_t v___x_267_; 
v___x_267_ = lean_usize_dec_eq(v_i_259_, v_stop_260_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v___x_268_ = lean_array_uget_borrowed(v_as_258_, v_i_259_);
v___x_269_ = lean_unsigned_to_nat(0u);
v___x_270_ = lean_array_get_size(v___x_268_);
v___x_271_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
v___y_263_ = v_b_261_;
goto v___jp_262_;
}
else
{
uint8_t v___x_272_; 
v___x_272_ = lean_nat_dec_le(v___x_270_, v___x_270_);
if (v___x_272_ == 0)
{
if (v___x_271_ == 0)
{
v___y_263_ = v_b_261_;
goto v___jp_262_;
}
else
{
size_t v___x_273_; size_t v___x_274_; lean_object* v___x_275_; 
v___x_273_ = ((size_t)0ULL);
v___x_274_ = lean_usize_of_nat(v___x_270_);
v___x_275_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0(v___x_268_, v___x_273_, v___x_274_, v_b_261_);
v___y_263_ = v___x_275_;
goto v___jp_262_;
}
}
else
{
size_t v___x_276_; size_t v___x_277_; lean_object* v___x_278_; 
v___x_276_ = ((size_t)0ULL);
v___x_277_ = lean_usize_of_nat(v___x_270_);
v___x_278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0(v___x_268_, v___x_276_, v___x_277_, v_b_261_);
v___y_263_ = v___x_278_;
goto v___jp_262_;
}
}
}
else
{
return v_b_261_;
}
v___jp_262_:
{
size_t v___x_264_; size_t v___x_265_; 
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_add(v_i_259_, v___x_264_);
v_i_259_ = v___x_265_;
v_b_261_ = v___y_263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_279_, lean_object* v_i_280_, lean_object* v_stop_281_, lean_object* v_b_282_){
_start:
{
size_t v_i_boxed_283_; size_t v_stop_boxed_284_; lean_object* v_res_285_; 
v_i_boxed_283_ = lean_unbox_usize(v_i_280_);
lean_dec(v_i_280_);
v_stop_boxed_284_ = lean_unbox_usize(v_stop_281_);
lean_dec(v_stop_281_);
v_res_285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(v_as_279_, v_i_boxed_283_, v_stop_boxed_284_, v_b_282_);
lean_dec_ref(v_as_279_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object* v_nss_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_287_ = lean_box(1);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_array_get_size(v_nss_286_);
v___x_290_ = lean_nat_dec_lt(v___x_288_, v___x_289_);
if (v___x_290_ == 0)
{
return v___x_287_;
}
else
{
uint8_t v___x_291_; 
v___x_291_ = lean_nat_dec_le(v___x_289_, v___x_289_);
if (v___x_291_ == 0)
{
if (v___x_290_ == 0)
{
return v___x_287_;
}
else
{
size_t v___x_292_; size_t v___x_293_; lean_object* v___x_294_; 
v___x_292_ = ((size_t)0ULL);
v___x_293_ = lean_usize_of_nat(v___x_289_);
v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(v_nss_286_, v___x_292_, v___x_293_, v___x_287_);
return v___x_294_;
}
}
else
{
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; 
v___x_295_ = ((size_t)0ULL);
v___x_296_ = lean_usize_of_nat(v___x_289_);
v___x_297_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(v_nss_286_, v___x_295_, v___x_296_, v___x_287_);
return v___x_297_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2____boxed(lean_object* v_nss_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(v_nss_298_);
lean_dec_ref(v_nss_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object* v_es_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = lean_array_mk(v_es_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_));
v___x_320_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2____boxed(lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_();
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_ref_350_, lean_object* v_msg_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_fileName_355_; lean_object* v_fileMap_356_; lean_object* v_options_357_; lean_object* v_currRecDepth_358_; lean_object* v_maxRecDepth_359_; lean_object* v_ref_360_; lean_object* v_currNamespace_361_; lean_object* v_openDecls_362_; lean_object* v_initHeartbeats_363_; lean_object* v_maxHeartbeats_364_; lean_object* v_quotContext_365_; lean_object* v_currMacroScope_366_; uint8_t v_diag_367_; lean_object* v_cancelTk_x3f_368_; uint8_t v_suppressElabErrors_369_; lean_object* v_inheritedTraceOptions_370_; lean_object* v_ref_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_fileName_355_ = lean_ctor_get(v___y_352_, 0);
v_fileMap_356_ = lean_ctor_get(v___y_352_, 1);
v_options_357_ = lean_ctor_get(v___y_352_, 2);
v_currRecDepth_358_ = lean_ctor_get(v___y_352_, 3);
v_maxRecDepth_359_ = lean_ctor_get(v___y_352_, 4);
v_ref_360_ = lean_ctor_get(v___y_352_, 5);
v_currNamespace_361_ = lean_ctor_get(v___y_352_, 6);
v_openDecls_362_ = lean_ctor_get(v___y_352_, 7);
v_initHeartbeats_363_ = lean_ctor_get(v___y_352_, 8);
v_maxHeartbeats_364_ = lean_ctor_get(v___y_352_, 9);
v_quotContext_365_ = lean_ctor_get(v___y_352_, 10);
v_currMacroScope_366_ = lean_ctor_get(v___y_352_, 11);
v_diag_367_ = lean_ctor_get_uint8(v___y_352_, sizeof(void*)*14);
v_cancelTk_x3f_368_ = lean_ctor_get(v___y_352_, 12);
v_suppressElabErrors_369_ = lean_ctor_get_uint8(v___y_352_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_370_ = lean_ctor_get(v___y_352_, 13);
v_ref_371_ = l_Lean_replaceRef(v_ref_350_, v_ref_360_);
lean_inc_ref(v_inheritedTraceOptions_370_);
lean_inc(v_cancelTk_x3f_368_);
lean_inc(v_currMacroScope_366_);
lean_inc(v_quotContext_365_);
lean_inc(v_maxHeartbeats_364_);
lean_inc(v_initHeartbeats_363_);
lean_inc(v_openDecls_362_);
lean_inc(v_currNamespace_361_);
lean_inc(v_maxRecDepth_359_);
lean_inc(v_currRecDepth_358_);
lean_inc_ref(v_options_357_);
lean_inc_ref(v_fileMap_356_);
lean_inc_ref(v_fileName_355_);
v___x_372_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_372_, 0, v_fileName_355_);
lean_ctor_set(v___x_372_, 1, v_fileMap_356_);
lean_ctor_set(v___x_372_, 2, v_options_357_);
lean_ctor_set(v___x_372_, 3, v_currRecDepth_358_);
lean_ctor_set(v___x_372_, 4, v_maxRecDepth_359_);
lean_ctor_set(v___x_372_, 5, v_ref_371_);
lean_ctor_set(v___x_372_, 6, v_currNamespace_361_);
lean_ctor_set(v___x_372_, 7, v_openDecls_362_);
lean_ctor_set(v___x_372_, 8, v_initHeartbeats_363_);
lean_ctor_set(v___x_372_, 9, v_maxHeartbeats_364_);
lean_ctor_set(v___x_372_, 10, v_quotContext_365_);
lean_ctor_set(v___x_372_, 11, v_currMacroScope_366_);
lean_ctor_set(v___x_372_, 12, v_cancelTk_x3f_368_);
lean_ctor_set(v___x_372_, 13, v_inheritedTraceOptions_370_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*14, v_diag_367_);
lean_ctor_set_uint8(v___x_372_, sizeof(void*)*14 + 1, v_suppressElabErrors_369_);
v___x_373_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v_msg_351_, v___x_372_, v___y_353_);
lean_dec_ref_known(v___x_372_, 14);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_ref_374_, lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_374_, v_msg_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v_ref_374_);
return v_res_379_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6));
v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
return v___x_391_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8));
v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
return v___x_394_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10));
v___x_397_ = l_Lean_stringToMessageData(v___x_396_);
return v___x_397_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12));
v___x_400_ = l_Lean_stringToMessageData(v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(lean_object* v_msg_401_, lean_object* v_declHint_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; lean_object* v_env_406_; uint8_t v___y_408_; uint8_t v___x_464_; uint8_t v___x_465_; 
v___x_405_ = lean_st_ref_get(v___y_403_);
v_env_406_ = lean_ctor_get(v___x_405_, 0);
lean_inc_ref(v_env_406_);
lean_dec(v___x_405_);
v___x_464_ = l_Lean_Name_isAnonymous(v_declHint_402_);
v___x_465_ = lean_bool_not(v___x_464_);
if (v___x_465_ == 0)
{
v___y_408_ = v___x_465_;
goto v___jp_407_;
}
else
{
uint8_t v_isExporting_466_; 
v_isExporting_466_ = lean_ctor_get_uint8(v_env_406_, sizeof(void*)*8);
v___y_408_ = v_isExporting_466_;
goto v___jp_407_;
}
v___jp_407_:
{
if (v___y_408_ == 0)
{
lean_object* v___x_409_; 
lean_dec_ref(v_env_406_);
lean_dec(v_declHint_402_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v_msg_401_);
return v___x_409_;
}
else
{
uint8_t v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = 0;
lean_inc_ref(v_env_406_);
v___x_411_ = l_Lean_Environment_setExporting(v_env_406_, v___x_410_);
lean_inc(v_declHint_402_);
lean_inc_ref(v___x_411_);
v___x_412_ = l_Lean_Environment_contains(v___x_411_, v_declHint_402_, v___y_408_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
lean_dec_ref(v___x_411_);
lean_dec_ref(v_env_406_);
lean_dec(v_declHint_402_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v_msg_401_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_c_419_; lean_object* v___x_420_; 
v___x_414_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_415_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__5);
v___x_416_ = l_Lean_Options_empty;
v___x_417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_417_, 0, v___x_411_);
lean_ctor_set(v___x_417_, 1, v___x_414_);
lean_ctor_set(v___x_417_, 2, v___x_415_);
lean_ctor_set(v___x_417_, 3, v___x_416_);
lean_inc(v_declHint_402_);
v___x_418_ = l_Lean_MessageData_ofConstName(v_declHint_402_, v___x_410_);
v_c_419_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_419_, 0, v___x_417_);
lean_ctor_set(v_c_419_, 1, v___x_418_);
v___x_420_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_406_, v_declHint_402_);
if (lean_obj_tag(v___x_420_) == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec_ref(v_env_406_);
lean_dec(v_declHint_402_);
v___x_421_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1);
v___x_422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v_c_419_);
v___x_423_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3);
v___x_424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_422_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_Lean_MessageData_note(v___x_424_);
v___x_426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_426_, 0, v_msg_401_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
return v___x_427_;
}
else
{
lean_object* v_val_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_463_; 
v_val_428_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_463_ == 0)
{
v___x_430_ = v___x_420_;
v_isShared_431_ = v_isSharedCheck_463_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_val_428_);
lean_dec(v___x_420_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_463_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v_mod_435_; uint8_t v___x_436_; 
v___x_432_ = lean_box(0);
v___x_433_ = l_Lean_Environment_header(v_env_406_);
lean_dec_ref(v_env_406_);
v___x_434_ = l_Lean_EnvironmentHeader_moduleNames(v___x_433_);
v_mod_435_ = lean_array_get(v___x_432_, v___x_434_, v_val_428_);
lean_dec(v_val_428_);
lean_dec_ref(v___x_434_);
v___x_436_ = l_Lean_isPrivateName(v_declHint_402_);
lean_dec(v_declHint_402_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_437_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5);
v___x_438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_c_419_);
v___x_439_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = l_Lean_MessageData_ofName(v_mod_435_);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9);
v___x_444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_442_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_Lean_MessageData_note(v___x_444_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v_msg_401_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 0);
lean_ctor_set(v___x_430_, 0, v___x_446_);
v___x_448_ = v___x_430_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_450_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1);
v___x_451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v_c_419_);
v___x_452_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11);
v___x_453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_451_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
v___x_454_ = l_Lean_MessageData_ofName(v_mod_435_);
v___x_455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_453_);
lean_ctor_set(v___x_455_, 1, v___x_454_);
v___x_456_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13);
v___x_457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_455_);
lean_ctor_set(v___x_457_, 1, v___x_456_);
v___x_458_ = l_Lean_MessageData_note(v___x_457_);
v___x_459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_459_, 0, v_msg_401_);
lean_ctor_set(v___x_459_, 1, v___x_458_);
if (v_isShared_431_ == 0)
{
lean_ctor_set_tag(v___x_430_, 0);
lean_ctor_set(v___x_430_, 0, v___x_459_);
v___x_461_ = v___x_430_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_msg_467_, lean_object* v_declHint_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_467_, v_declHint_468_, v___y_469_);
lean_dec(v___y_469_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_msg_472_, lean_object* v_declHint_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_487_; 
v___x_477_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_472_, v_declHint_473_, v___y_475_);
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_487_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_487_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_482_ = l_Lean_unknownIdentifierMessageTag;
v___x_483_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v_a_478_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_483_);
v___x_485_ = v___x_480_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_msg_488_, lean_object* v_declHint_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(v_msg_488_, v_declHint_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_494_, lean_object* v_msg_495_, lean_object* v_declHint_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; lean_object* v_a_501_; lean_object* v___x_502_; 
v___x_500_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(v_msg_495_, v_declHint_496_, v___y_497_, v___y_498_);
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref(v___x_500_);
v___x_502_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_494_, v_a_501_, v___y_497_, v___y_498_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_503_, lean_object* v_msg_504_, lean_object* v_declHint_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_503_, v_msg_504_, v_declHint_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v_ref_503_);
return v_res_509_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0));
v___x_512_ = l_Lean_stringToMessageData(v___x_511_);
return v___x_512_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2));
v___x_515_ = l_Lean_stringToMessageData(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_ref_516_, lean_object* v_constName_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_521_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_522_ = 0;
lean_inc(v_constName_517_);
v___x_523_ = l_Lean_MessageData_ofConstName(v_constName_517_, v___x_522_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_521_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_516_, v___x_526_, v_constName_517_, v___y_518_, v___y_519_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_528_, lean_object* v_constName_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_528_, v_constName_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v_ref_528_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_constName_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v_ref_538_; lean_object* v___x_539_; 
v_ref_538_ = lean_ctor_get(v___y_535_, 5);
v___x_539_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_538_, v_constName_534_, v___y_535_, v___y_536_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_constName_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0(lean_object* v_constName_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; lean_object* v_env_550_; uint8_t v___x_551_; lean_object* v___x_552_; 
v___x_549_ = lean_st_ref_get(v___y_547_);
v_env_550_ = lean_ctor_get(v___x_549_, 0);
lean_inc_ref(v_env_550_);
lean_dec(v___x_549_);
v___x_551_ = 0;
lean_inc(v_constName_545_);
v___x_552_ = l_Lean_Environment_find_x3f(v_env_550_, v_constName_545_, v___x_551_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_545_, v___y_546_, v___y_547_);
return v___x_553_;
}
else
{
lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_constName_545_);
v_val_554_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_552_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v___x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 0);
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_val_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0___boxed(lean_object* v_constName_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0(v_constName_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
if (lean_obj_tag(v_a_567_) == 0)
{
lean_object* v___x_569_; 
v___x_569_ = l_List_reverse___redArg(v_a_568_);
return v___x_569_;
}
else
{
lean_object* v_head_570_; lean_object* v_tail_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_580_; 
v_head_570_ = lean_ctor_get(v_a_567_, 0);
v_tail_571_ = lean_ctor_get(v_a_567_, 1);
v_isSharedCheck_580_ = !lean_is_exclusive(v_a_567_);
if (v_isSharedCheck_580_ == 0)
{
v___x_573_ = v_a_567_;
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_tail_571_);
lean_inc(v_head_570_);
lean_dec(v_a_567_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_580_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_575_ = l_Lean_mkLevelParam(v_head_570_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v_a_568_);
lean_ctor_set(v___x_573_, 0, v___x_575_);
v___x_577_ = v___x_573_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_a_568_);
v___x_577_ = v_reuseFailAlloc_579_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
v_a_567_ = v_tail_571_;
v_a_568_ = v___x_577_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_constName_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; lean_object* v_env_586_; uint8_t v___x_587_; lean_object* v___x_588_; 
v___x_585_ = lean_st_ref_get(v___y_583_);
v_env_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc_ref(v_env_586_);
lean_dec(v___x_585_);
v___x_587_ = 0;
lean_inc(v_constName_581_);
v___x_588_ = l_Lean_Environment_findConstVal_x3f(v_env_586_, v_constName_581_, v___x_587_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_581_, v___y_582_, v___y_583_);
return v___x_589_;
}
else
{
lean_object* v_val_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_constName_581_);
v_val_590_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_588_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_val_590_);
lean_dec(v___x_588_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 0);
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_val_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_constName_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_constName_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_constName_603_, lean_object* v___y_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; 
lean_inc(v_constName_603_);
v___x_607_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_constName_603_, v___y_604_, v___y_605_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_619_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_619_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_619_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_619_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_levelParams_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v_levelParams_612_ = lean_ctor_get(v_a_608_, 1);
lean_inc(v_levelParams_612_);
lean_dec(v_a_608_);
v___x_613_ = lean_box(0);
v___x_614_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_levelParams_612_, v___x_613_);
v___x_615_ = l_Lean_mkConst(v_constName_603_, v___x_614_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_615_);
v___x_617_ = v___x_610_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v_constName_603_);
v_a_620_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_607_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_607_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_constName_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2(v_constName_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(lean_object* v_t_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; lean_object* v_infoState_637_; uint8_t v_enabled_638_; 
v___x_636_ = lean_st_ref_get(v___y_634_);
v_infoState_637_ = lean_ctor_get(v___x_636_, 7);
lean_inc_ref(v_infoState_637_);
lean_dec(v___x_636_);
v_enabled_638_ = lean_ctor_get_uint8(v_infoState_637_, sizeof(void*)*3);
lean_dec_ref(v_infoState_637_);
if (v_enabled_638_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec_ref(v_t_633_);
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v_infoState_642_; lean_object* v_env_643_; lean_object* v_nextMacroScope_644_; lean_object* v_ngen_645_; lean_object* v_auxDeclNGen_646_; lean_object* v_traceState_647_; lean_object* v_cache_648_; lean_object* v_messages_649_; lean_object* v_snapshotTasks_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_672_; 
v___x_641_ = lean_st_ref_take(v___y_634_);
v_infoState_642_ = lean_ctor_get(v___x_641_, 7);
v_env_643_ = lean_ctor_get(v___x_641_, 0);
v_nextMacroScope_644_ = lean_ctor_get(v___x_641_, 1);
v_ngen_645_ = lean_ctor_get(v___x_641_, 2);
v_auxDeclNGen_646_ = lean_ctor_get(v___x_641_, 3);
v_traceState_647_ = lean_ctor_get(v___x_641_, 4);
v_cache_648_ = lean_ctor_get(v___x_641_, 5);
v_messages_649_ = lean_ctor_get(v___x_641_, 6);
v_snapshotTasks_650_ = lean_ctor_get(v___x_641_, 8);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_672_ == 0)
{
v___x_652_ = v___x_641_;
v_isShared_653_ = v_isSharedCheck_672_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_snapshotTasks_650_);
lean_inc(v_infoState_642_);
lean_inc(v_messages_649_);
lean_inc(v_cache_648_);
lean_inc(v_traceState_647_);
lean_inc(v_auxDeclNGen_646_);
lean_inc(v_ngen_645_);
lean_inc(v_nextMacroScope_644_);
lean_inc(v_env_643_);
lean_dec(v___x_641_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_672_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
uint8_t v_enabled_654_; lean_object* v_assignment_655_; lean_object* v_lazyAssignment_656_; lean_object* v_trees_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_671_; 
v_enabled_654_ = lean_ctor_get_uint8(v_infoState_642_, sizeof(void*)*3);
v_assignment_655_ = lean_ctor_get(v_infoState_642_, 0);
v_lazyAssignment_656_ = lean_ctor_get(v_infoState_642_, 1);
v_trees_657_ = lean_ctor_get(v_infoState_642_, 2);
v_isSharedCheck_671_ = !lean_is_exclusive(v_infoState_642_);
if (v_isSharedCheck_671_ == 0)
{
v___x_659_ = v_infoState_642_;
v_isShared_660_ = v_isSharedCheck_671_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_trees_657_);
lean_inc(v_lazyAssignment_656_);
lean_inc(v_assignment_655_);
lean_dec(v_infoState_642_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_671_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = l_Lean_PersistentArray_push___redArg(v_trees_657_, v_t_633_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 2, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_assignment_655_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_lazyAssignment_656_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v___x_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_670_, sizeof(void*)*3, v_enabled_654_);
v___x_663_ = v_reuseFailAlloc_670_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 7, v___x_663_);
v___x_665_ = v___x_652_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_env_643_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v_nextMacroScope_644_);
lean_ctor_set(v_reuseFailAlloc_669_, 2, v_ngen_645_);
lean_ctor_set(v_reuseFailAlloc_669_, 3, v_auxDeclNGen_646_);
lean_ctor_set(v_reuseFailAlloc_669_, 4, v_traceState_647_);
lean_ctor_set(v_reuseFailAlloc_669_, 5, v_cache_648_);
lean_ctor_set(v_reuseFailAlloc_669_, 6, v_messages_649_);
lean_ctor_set(v_reuseFailAlloc_669_, 7, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_669_, 8, v_snapshotTasks_650_);
v___x_665_ = v_reuseFailAlloc_669_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_666_ = lean_st_ref_set(v___y_634_, v___x_665_);
v___x_667_ = lean_box(0);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_t_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_t_673_, v___y_674_);
lean_dec(v___y_674_);
return v_res_676_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_677_ = lean_unsigned_to_nat(32u);
v___x_678_ = lean_mk_empty_array_with_capacity(v___x_677_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__1(void){
_start:
{
size_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_680_ = ((size_t)5ULL);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_unsigned_to_nat(32u);
v___x_683_ = lean_mk_empty_array_with_capacity(v___x_682_);
v___x_684_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__0);
v___x_685_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_685_, 0, v___x_684_);
lean_ctor_set(v___x_685_, 1, v___x_683_);
lean_ctor_set(v___x_685_, 2, v___x_681_);
lean_ctor_set(v___x_685_, 3, v___x_681_);
lean_ctor_set_usize(v___x_685_, 4, v___x_680_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_t_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; lean_object* v_infoState_691_; uint8_t v_enabled_692_; 
v___x_690_ = lean_st_ref_get(v___y_688_);
v_infoState_691_ = lean_ctor_get(v___x_690_, 7);
lean_inc_ref(v_infoState_691_);
lean_dec(v___x_690_);
v_enabled_692_ = lean_ctor_get_uint8(v_infoState_691_, sizeof(void*)*3);
lean_dec_ref(v_infoState_691_);
if (v_enabled_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec_ref(v_t_686_);
v___x_693_ = lean_box(0);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__1);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v_t_686_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___x_697_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v___x_696_, v___y_688_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_t_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3(v_t_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1(lean_object* v_stx_703_, lean_object* v_n_704_, lean_object* v_expectedType_x3f_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2(v_n_704_, v___y_706_, v___y_707_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = lean_box(0);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v_stx_703_);
v___x_713_ = l_Lean_LocalContext_empty;
v___x_714_ = 0;
v___x_715_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_715_, 0, v___x_712_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
lean_ctor_set(v___x_715_, 2, v_expectedType_x3f_705_);
lean_ctor_set(v___x_715_, 3, v_a_710_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*4, v___x_714_);
lean_ctor_set_uint8(v___x_715_, sizeof(void*)*4 + 1, v___x_714_);
v___x_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
v___x_717_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3(v___x_716_, v___y_706_, v___y_707_);
return v___x_717_;
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec(v_expectedType_x3f_705_);
lean_dec(v_stx_703_);
v_a_718_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_709_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_709_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1___boxed(lean_object* v_stx_726_, lean_object* v_n_727_, lean_object* v_expectedType_x3f_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1(v_stx_726_, v_n_727_, v_expectedType_x3f_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
return v_res_732_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_733_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_740_ = l_Lean_stringToMessageData(v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_743_ = l_Lean_stringToMessageData(v___x_742_);
return v___x_743_;
}
}
static uint64_t _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_750_; uint64_t v___x_751_; 
v___x_750_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_751_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_750_);
return v___x_751_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_752_ = lean_uint64_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_753_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_754_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set_uint64(v___x_754_, sizeof(void*)*1, v___x_752_);
return v___x_754_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_755_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_759_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_759_, 0, v___x_758_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
lean_ctor_set(v___x_759_, 3, v___x_758_);
lean_ctor_set(v___x_759_, 4, v___x_758_);
lean_ctor_set(v___x_759_, 5, v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
lean_ctor_set(v___x_761_, 2, v___x_760_);
lean_ctor_set(v___x_761_, 3, v___x_760_);
lean_ctor_set(v___x_761_, 4, v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_782_ = l_Lean_stringToMessageData(v___x_781_);
return v___x_782_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_788_ = l_Lean_stringToMessageData(v___x_787_);
return v___x_788_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__34_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__33_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object* v___x_792_, lean_object* v___x_793_, lean_object* v___x_794_, lean_object* v___x_795_, lean_object* v___x_796_, lean_object* v___x_797_, lean_object* v___x_798_, lean_object* v___x_799_, lean_object* v_decl_800_, lean_object* v_stx_801_, uint8_t v_kind_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; uint8_t v___y_840_; lean_object* v___y_841_; uint8_t v_a_842_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_911_; lean_object* v___y_912_; lean_object* v___y_917_; uint8_t v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_928_; uint8_t v___y_929_; lean_object* v___y_930_; uint8_t v___y_931_; lean_object* v___y_932_; uint8_t v___y_933_; lean_object* v___y_942_; lean_object* v___y_943_; lean_object* v___y_944_; lean_object* v___y_945_; lean_object* v___y_950_; lean_object* v___y_951_; lean_object* v___y_952_; lean_object* v___y_953_; lean_object* v_optName_969_; lean_object* v___y_970_; lean_object* v___y_971_; uint8_t v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = 0;
v___x_1014_ = l_Lean_instBEqAttributeKind_beq(v_kind_802_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
lean_dec(v_stx_801_);
lean_dec(v_decl_800_);
lean_dec_ref(v___x_799_);
lean_dec(v___x_798_);
lean_dec(v___x_797_);
lean_dec(v___x_796_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_794_);
lean_dec_ref(v___x_793_);
lean_dec(v___x_792_);
v___x_1015_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__34_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__34_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__34_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1016_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1015_, v___y_803_, v___y_804_);
return v___x_1016_;
}
else
{
goto v___jp_985_;
}
v___jp_806_:
{
lean_object* v___x_809_; lean_object* v_env_810_; lean_object* v_nextMacroScope_811_; lean_object* v_ngen_812_; lean_object* v_auxDeclNGen_813_; lean_object* v_traceState_814_; lean_object* v_messages_815_; lean_object* v_infoState_816_; lean_object* v_snapshotTasks_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_833_; 
v___x_809_ = lean_st_ref_take(v___y_808_);
v_env_810_ = lean_ctor_get(v___x_809_, 0);
v_nextMacroScope_811_ = lean_ctor_get(v___x_809_, 1);
v_ngen_812_ = lean_ctor_get(v___x_809_, 2);
v_auxDeclNGen_813_ = lean_ctor_get(v___x_809_, 3);
v_traceState_814_ = lean_ctor_get(v___x_809_, 4);
v_messages_815_ = lean_ctor_get(v___x_809_, 6);
v_infoState_816_ = lean_ctor_get(v___x_809_, 7);
v_snapshotTasks_817_ = lean_ctor_get(v___x_809_, 8);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v___x_809_, 5);
lean_dec(v_unused_834_);
v___x_819_ = v___x_809_;
v_isShared_820_ = v_isSharedCheck_833_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_snapshotTasks_817_);
lean_inc(v_infoState_816_);
lean_inc(v_messages_815_);
lean_inc(v_traceState_814_);
lean_inc(v_auxDeclNGen_813_);
lean_inc(v_ngen_812_);
lean_inc(v_nextMacroScope_811_);
lean_inc(v_env_810_);
lean_dec(v___x_809_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_833_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_821_; lean_object* v_toEnvExtension_822_; lean_object* v_asyncMode_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_821_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_822_ = lean_ctor_get(v___x_821_, 0);
v_asyncMode_823_ = lean_ctor_get(v_toEnvExtension_822_, 2);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v___y_807_);
lean_ctor_set(v___x_824_, 1, v_decl_800_);
v___x_825_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_821_, v_env_810_, v___x_824_, v_asyncMode_823_, v___x_792_);
v___x_826_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
if (v_isShared_820_ == 0)
{
lean_ctor_set(v___x_819_, 5, v___x_826_);
lean_ctor_set(v___x_819_, 0, v___x_825_);
v___x_828_ = v___x_819_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_nextMacroScope_811_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_ngen_812_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_auxDeclNGen_813_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v_traceState_814_);
lean_ctor_set(v_reuseFailAlloc_832_, 5, v___x_826_);
lean_ctor_set(v_reuseFailAlloc_832_, 6, v_messages_815_);
lean_ctor_set(v_reuseFailAlloc_832_, 7, v_infoState_816_);
lean_ctor_set(v_reuseFailAlloc_832_, 8, v_snapshotTasks_817_);
v___x_828_ = v_reuseFailAlloc_832_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_829_ = lean_st_ref_set(v___y_808_, v___x_828_);
v___x_830_ = lean_box(0);
v___x_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
return v___x_831_;
}
}
}
v___jp_835_:
{
if (v_a_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v___y_836_);
lean_dec(v___x_792_);
v___x_843_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
v___x_844_ = l_Lean_MessageData_ofConstName(v_decl_800_, v___y_840_);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_845_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = l_Lean_MessageData_ofConstName(v___y_839_, v___y_840_);
v___x_849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_849_, 0, v___x_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
v___x_850_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_849_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = l_Lean_MessageData_ofExpr(v___y_837_);
v___x_853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_851_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
lean_ctor_set(v___x_854_, 1, v___x_843_);
v___x_855_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_854_, v___y_838_, v___y_841_);
return v___x_855_;
}
else
{
lean_dec(v___y_839_);
lean_dec_ref(v___y_837_);
v___y_807_ = v___y_836_;
v___y_808_ = v___y_841_;
goto v___jp_806_;
}
}
v___jp_856_:
{
lean_object* v___x_860_; 
lean_inc(v_decl_800_);
v___x_860_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0(v_decl_800_, v___y_858_, v___y_859_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_862_; uint8_t v___x_863_; uint8_t v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; size_t v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
lean_inc_ref(v___x_795_);
v___x_862_ = l_Lean_Name_mkStr4(v___x_793_, v___x_794_, v___x_795_, v___x_795_);
v___x_863_ = 0;
v___x_864_ = 1;
v___x_865_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_866_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_867_ = lean_unsigned_to_nat(32u);
v___x_868_ = lean_mk_empty_array_with_capacity(v___x_867_);
v___x_869_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_870_ = ((size_t)5ULL);
lean_inc_n(v___x_796_, 6);
v___x_871_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_868_);
lean_ctor_set(v___x_871_, 2, v___x_796_);
lean_ctor_set(v___x_871_, 3, v___x_796_);
lean_ctor_set_usize(v___x_871_, 4, v___x_870_);
v___x_872_ = lean_box(1);
lean_inc_ref(v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_873_, 0, v___x_866_);
lean_ctor_set(v___x_873_, 1, v___x_871_);
lean_ctor_set(v___x_873_, 2, v___x_872_);
v___x_874_ = lean_mk_empty_array_with_capacity(v___x_796_);
v___x_875_ = lean_box(0);
lean_inc(v___x_797_);
v___x_876_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_876_, 0, v___x_865_);
lean_ctor_set(v___x_876_, 1, v___x_797_);
lean_ctor_set(v___x_876_, 2, v___x_873_);
lean_ctor_set(v___x_876_, 3, v___x_874_);
lean_ctor_set(v___x_876_, 4, v___x_875_);
lean_ctor_set(v___x_876_, 5, v___x_796_);
lean_ctor_set(v___x_876_, 6, v___x_875_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*7, v___x_863_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*7 + 1, v___x_863_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*7 + 2, v___x_863_);
lean_ctor_set_uint8(v___x_876_, sizeof(void*)*7 + 3, v___x_864_);
v___x_877_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_877_, 0, v___x_796_);
lean_ctor_set(v___x_877_, 1, v___x_796_);
lean_ctor_set(v___x_877_, 2, v___x_796_);
lean_ctor_set(v___x_877_, 3, v___x_796_);
lean_ctor_set(v___x_877_, 4, v___x_866_);
lean_ctor_set(v___x_877_, 5, v___x_866_);
lean_ctor_set(v___x_877_, 6, v___x_866_);
lean_ctor_set(v___x_877_, 7, v___x_866_);
lean_ctor_set(v___x_877_, 8, v___x_866_);
lean_ctor_set(v___x_877_, 9, v___x_866_);
v___x_878_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_879_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_880_, 0, v___x_877_);
lean_ctor_set(v___x_880_, 1, v___x_878_);
lean_ctor_set(v___x_880_, 2, v___x_797_);
lean_ctor_set(v___x_880_, 3, v___x_871_);
lean_ctor_set(v___x_880_, 4, v___x_879_);
v___x_881_ = lean_st_mk_ref(v___x_880_);
v___x_882_ = l_Lean_ConstantInfo_type(v_a_861_);
lean_dec(v_a_861_);
v___x_883_ = lean_box(0);
lean_inc(v___x_862_);
v___x_884_ = l_Lean_mkConst(v___x_862_, v___x_883_);
lean_inc_ref(v___x_882_);
v___x_885_ = l_Lean_Meta_isExprDefEq(v___x_882_, v___x_884_, v___x_876_, v___x_881_, v___y_858_, v___y_859_);
lean_dec_ref_known(v___x_876_, 7);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = lean_st_ref_get(v___x_881_);
lean_dec(v___x_881_);
lean_dec(v___x_887_);
v___x_888_ = lean_unbox(v_a_886_);
lean_dec(v_a_886_);
v___y_836_ = v___y_857_;
v___y_837_ = v___x_882_;
v___y_838_ = v___y_858_;
v___y_839_ = v___x_862_;
v___y_840_ = v___x_863_;
v___y_841_ = v___y_859_;
v_a_842_ = v___x_888_;
goto v___jp_835_;
}
else
{
lean_dec(v___x_881_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_889_; uint8_t v___x_890_; 
v_a_889_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_889_);
lean_dec_ref_known(v___x_885_, 1);
v___x_890_ = lean_unbox(v_a_889_);
lean_dec(v_a_889_);
v___y_836_ = v___y_857_;
v___y_837_ = v___x_882_;
v___y_838_ = v___y_858_;
v___y_839_ = v___x_862_;
v___y_840_ = v___x_863_;
v___y_841_ = v___y_859_;
v_a_842_ = v___x_890_;
goto v___jp_835_;
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v___x_882_);
lean_dec(v___x_862_);
lean_dec(v___y_857_);
lean_dec(v_decl_800_);
lean_dec(v___x_792_);
v_a_891_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_885_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_885_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
else
{
lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_906_; 
lean_dec(v___y_857_);
lean_dec(v_decl_800_);
lean_dec(v___x_797_);
lean_dec(v___x_796_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_794_);
lean_dec_ref(v___x_793_);
lean_dec(v___x_792_);
v_a_899_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_906_ == 0)
{
v___x_901_ = v___x_860_;
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_860_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_906_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_904_; 
if (v_isShared_902_ == 0)
{
v___x_904_ = v___x_901_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v_a_899_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
v___jp_907_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec(v___y_908_);
lean_inc_ref(v___y_912_);
v___x_913_ = l_Lean_stringToMessageData(v___y_912_);
v___x_914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_914_, 0, v___y_909_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
v___x_915_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_914_, v___y_910_, v___y_911_);
return v___x_915_;
}
v___jp_916_:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_inc_ref(v___y_922_);
v___x_923_ = l_Lean_stringToMessageData(v___y_922_);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___y_920_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
if (v___y_918_ == 0)
{
lean_object* v___x_925_; 
v___x_925_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_908_ = v___y_917_;
v___y_909_ = v___x_924_;
v___y_910_ = v___y_919_;
v___y_911_ = v___y_921_;
v___y_912_ = v___x_925_;
goto v___jp_907_;
}
else
{
lean_object* v___x_926_; 
v___x_926_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_908_ = v___y_917_;
v___y_909_ = v___x_924_;
v___y_910_ = v___y_919_;
v___y_911_ = v___y_921_;
v___y_912_ = v___x_926_;
goto v___jp_907_;
}
}
v___jp_927_:
{
if (v___y_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
lean_dec(v___x_797_);
lean_dec(v___x_796_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_794_);
lean_dec_ref(v___x_793_);
lean_dec(v___x_792_);
v___x_934_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_935_ = l_Lean_MessageData_ofConstName(v_decl_800_, v___y_933_);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_934_);
lean_ctor_set(v___x_936_, 1, v___x_935_);
v___x_937_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
if (v___y_931_ == 0)
{
lean_object* v___x_939_; 
v___x_939_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_917_ = v___y_928_;
v___y_918_ = v___y_929_;
v___y_919_ = v___y_930_;
v___y_920_ = v___x_938_;
v___y_921_ = v___y_932_;
v___y_922_ = v___x_939_;
goto v___jp_916_;
}
else
{
lean_object* v___x_940_; 
v___x_940_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_917_ = v___y_928_;
v___y_918_ = v___y_929_;
v___y_919_ = v___y_930_;
v___y_920_ = v___x_938_;
v___y_921_ = v___y_932_;
v___y_922_ = v___x_940_;
goto v___jp_916_;
}
}
else
{
v___y_857_ = v___y_928_;
v___y_858_ = v___y_930_;
v___y_859_ = v___y_932_;
goto v___jp_856_;
}
}
v___jp_941_:
{
uint8_t v___x_946_; uint8_t v___x_947_; uint8_t v___x_948_; 
v___x_946_ = l_Lean_isPrivateName(v_decl_800_);
v___x_947_ = lean_bool_not(v___x_946_);
lean_inc(v_decl_800_);
v___x_948_ = l_Lean_isMarkedMeta(v___y_943_, v_decl_800_);
if (v___x_947_ == 0)
{
v___y_928_ = v___y_942_;
v___y_929_ = v___x_948_;
v___y_930_ = v___y_944_;
v___y_931_ = v___x_947_;
v___y_932_ = v___y_945_;
v___y_933_ = v___x_947_;
goto v___jp_927_;
}
else
{
v___y_928_ = v___y_942_;
v___y_929_ = v___x_948_;
v___y_930_ = v___y_944_;
v___y_931_ = v___x_947_;
v___y_932_ = v___y_945_;
v___y_933_ = v___x_948_;
goto v___jp_927_;
}
}
v___jp_949_:
{
lean_object* v___x_954_; lean_object* v_toEnvExtension_955_; lean_object* v_asyncMode_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_954_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_955_ = lean_ctor_get(v___x_954_, 0);
v_asyncMode_956_ = lean_ctor_get(v_toEnvExtension_955_, 2);
lean_inc(v___x_792_);
lean_inc_ref(v___y_951_);
v___x_957_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_798_, v___x_954_, v___y_951_, v_asyncMode_956_, v___x_792_);
v___x_958_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_957_, v___y_950_);
lean_dec(v___x_957_);
if (lean_obj_tag(v___x_958_) == 1)
{
lean_object* v_val_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
lean_dec_ref(v___y_951_);
lean_dec(v_decl_800_);
lean_dec(v___x_797_);
lean_dec(v___x_796_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_794_);
lean_dec_ref(v___x_793_);
lean_dec(v___x_792_);
v_val_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_val_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = lean_box(0);
v___x_961_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1(v_stx_801_, v_val_959_, v___x_960_, v___y_952_, v___y_953_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec_ref_known(v___x_961_, 1);
v___x_962_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_963_ = l_Lean_MessageData_ofName(v___y_950_);
v___x_964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_962_);
lean_ctor_set(v___x_964_, 1, v___x_963_);
v___x_965_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_964_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_966_, v___y_952_, v___y_953_);
return v___x_967_;
}
else
{
lean_dec(v___y_950_);
return v___x_961_;
}
}
else
{
lean_dec(v___x_958_);
lean_dec(v_stx_801_);
v___y_942_ = v___y_950_;
v___y_943_ = v___y_951_;
v___y_944_ = v___y_952_;
v___y_945_ = v___y_953_;
goto v___jp_941_;
}
}
v___jp_968_:
{
lean_object* v___x_972_; lean_object* v_env_973_; uint8_t v___x_974_; uint8_t v___x_975_; 
v___x_972_ = lean_st_ref_get(v___y_971_);
v_env_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc_ref_n(v_env_973_, 2);
lean_dec(v___x_972_);
v___x_974_ = 1;
lean_inc(v_optName_969_);
v___x_975_ = l_Lean_Environment_contains(v_env_973_, v_optName_969_, v___x_974_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec_ref(v_env_973_);
lean_dec(v_stx_801_);
lean_dec(v_decl_800_);
lean_dec(v___x_798_);
lean_dec(v___x_797_);
lean_dec(v___x_796_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_794_);
lean_dec_ref(v___x_793_);
lean_dec(v___x_792_);
v___x_976_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_977_ = l_Lean_MessageData_ofName(v_optName_969_);
lean_inc_ref(v___x_977_);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_976_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_977_);
v___x_982_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_983_, v___y_970_, v___y_971_);
return v___x_984_;
}
else
{
v___y_950_ = v_optName_969_;
v___y_951_ = v_env_973_;
v___y_952_ = v___y_970_;
v___y_953_ = v___y_971_;
goto v___jp_949_;
}
}
v___jp_985_:
{
lean_object* v___x_986_; uint8_t v___x_987_; 
lean_inc_ref(v___x_795_);
lean_inc_ref(v___x_794_);
lean_inc_ref(v___x_793_);
v___x_986_ = l_Lean_Name_mkStr4(v___x_793_, v___x_794_, v___x_795_, v___x_799_);
lean_inc(v_stx_801_);
v___x_987_ = l_Lean_Syntax_isOfKind(v_stx_801_, v___x_986_);
lean_dec(v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec(v_stx_801_);
lean_dec(v_decl_800_);
lean_dec(v___x_798_);
lean_dec(v___x_797_);
lean_dec(v___x_796_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_794_);
lean_dec_ref(v___x_793_);
lean_dec(v___x_792_);
v___x_988_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_989_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_988_, v___y_803_, v___y_804_);
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
else
{
lean_object* v___x_998_; lean_object* v_id_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_998_ = lean_unsigned_to_nat(1u);
v_id_999_ = l_Lean_Syntax_getArg(v_stx_801_, v___x_998_);
v___x_1000_ = ((lean_object*)(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7));
lean_inc(v_id_999_);
v___x_1001_ = l_Lean_Syntax_isOfKind(v_id_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec(v_id_999_);
lean_dec(v_stx_801_);
lean_dec(v_decl_800_);
lean_dec(v___x_798_);
lean_dec(v___x_797_);
lean_dec(v___x_796_);
lean_dec_ref(v___x_795_);
lean_dec_ref(v___x_794_);
lean_dec_ref(v___x_793_);
lean_dec(v___x_792_);
v___x_1002_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1003_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1002_, v___y_803_, v___y_804_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_TSyntax_getId(v_id_999_);
lean_dec(v_id_999_);
v_optName_969_ = v___x_1012_;
v___y_970_ = v___y_803_;
v___y_971_ = v___y_804_;
goto v___jp_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object* v___x_1017_, lean_object* v___x_1018_, lean_object* v___x_1019_, lean_object* v___x_1020_, lean_object* v___x_1021_, lean_object* v___x_1022_, lean_object* v___x_1023_, lean_object* v___x_1024_, lean_object* v_decl_1025_, lean_object* v_stx_1026_, lean_object* v_kind_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
uint8_t v_kind_boxed_1031_; lean_object* v_res_1032_; 
v_kind_boxed_1031_ = lean_unbox(v_kind_1027_);
v_res_1032_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(v___x_1017_, v___x_1018_, v___x_1019_, v___x_1020_, v___x_1021_, v___x_1022_, v___x_1023_, v___x_1024_, v_decl_1025_, v_stx_1026_, v_kind_boxed_1031_, v___y_1028_, v___y_1029_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1032_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object* v___x_1039_, lean_object* v_decl_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1044_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1045_ = l_Lean_MessageData_ofName(v___x_1039_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1_spec__0_spec__0_spec__1___redArg(v___x_1048_, v___y_1041_, v___y_1042_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object* v___x_1050_, lean_object* v_decl_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(v___x_1050_, v_decl_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v_decl_1051_);
return v_res_1055_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1105_ = lean_unsigned_to_nat(3183030336u);
v___x_1106_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1107_ = l_Lean_Name_num___override(v___x_1106_, v___x_1105_);
return v___x_1107_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1110_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1111_ = l_Lean_Name_str___override(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1114_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1115_ = l_Lean_Name_str___override(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_unsigned_to_nat(2u);
v___x_1117_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1118_ = l_Lean_Name_num___override(v___x_1117_, v___x_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1132_ = 0;
v___x_1133_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1134_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1135_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1136_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1134_);
lean_ctor_set(v___x_1136_, 2, v___x_1133_);
lean_ctor_set_uint8(v___x_1136_, sizeof(void*)*3, v___x_1132_);
return v___x_1136_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1137_; lean_object* v___f_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___f_1137_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___f_1138_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1139_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___f_1138_);
lean_ctor_set(v___x_1140_, 2, v___f_1137_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1142_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1143_ = l_Lean_registerBuiltinAttribute(v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_();
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b1_1146_, lean_object* v_constName_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_1147_, v___y_1148_, v___y_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1152_, lean_object* v_constName_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1152_, v_constName_1153_, v___y_1154_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7(lean_object* v_t_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_t_1158_, v___y_1160_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___boxed(lean_object* v_t_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7(v_t_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1168_, lean_object* v_ref_1169_, lean_object* v_constName_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_1169_, v_constName_1170_, v___y_1171_, v___y_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1175_, lean_object* v_ref_1176_, lean_object* v_constName_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b1_1175_, v_ref_1176_, v_constName_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v_ref_1176_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1182_, lean_object* v_ref_1183_, lean_object* v_msg_1184_, lean_object* v_declHint_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1189_; 
v___x_1189_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1183_, v_msg_1184_, v_declHint_1185_, v___y_1186_, v___y_1187_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_ref_1191_, lean_object* v_msg_1192_, lean_object* v_declHint_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v_res_1197_; 
v_res_1197_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1190_, v_ref_1191_, v_msg_1192_, v_declHint_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v_ref_1191_);
return v_res_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10(lean_object* v_msg_1198_, lean_object* v_declHint_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_1198_, v_declHint_1199_, v___y_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___boxed(lean_object* v_msg_1204_, lean_object* v_declHint_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10(v_msg_1204_, v_declHint_1205_, v___y_1206_, v___y_1207_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b1_1210_, lean_object* v_ref_1211_, lean_object* v_msg_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_1211_, v_msg_1212_, v___y_1213_, v___y_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b1_1217_, lean_object* v_ref_1218_, lean_object* v_msg_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b1_1217_, v_ref_1218_, v_msg_1219_, v___y_1220_, v___y_1221_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v_ref_1218_);
return v_res_1223_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_AutoDecl(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AutoDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_EnvLinter_envLinterExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_EnvLinter_envLinterExt);
lean_dec_ref(res);
res = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* initialize_Lean_AutoDecl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_InfoTree_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AutoDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_EnvLinter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_EnvLinter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_EnvLinter_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
