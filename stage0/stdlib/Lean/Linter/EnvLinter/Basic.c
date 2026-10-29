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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_empty;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadEnvCoreM;
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
extern lean_object* l_Lean_Core_instMonadRefCoreM;
extern lean_object* l_Lean_Core_instAddMessageContextCoreM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadOptionsCoreM;
lean_object* l_Lean_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_has_compile_error(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* l_Lean_Environment_evalConstCheck___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t, uint8_t);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2_value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3_value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__4 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__4_value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__5 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__5_value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7_value_aux_1),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7_value_aux_2),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(44, 32, 157, 0, 199, 45, 83, 147)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7 = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(118, 34, 157, 198, 119, 92, 66, 12)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_envLinterExt;
static const lean_string_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "builtin_env_linter"};
static const lean_object* l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
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
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` must have type `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "`, got `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " but is only marked `meta`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "invalid attribute `builtin_env_linter`, declaration `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "` must be marked as `public` and `meta`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " but is only marked `public`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "invalid attribute `builtin_env_linter`, linter `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "invalid attribute `builtin_env_linter`, no constant named `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`; did you forget `register_builtin_option "};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " : Bool := ...`\?"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "invalid `builtin_env_linter` syntax: expected an option name argument"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "invalid attribute `builtin_env_linter`, must be global"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__33_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__33_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(196, 60, 89, 104, 222, 184, 104, 61)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(255, 77, 64, 120, 151, 50, 41, 244)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Basic"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(176, 75, 158, 206, 205, 238, 69, 21)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(137, 12, 34, 233, 215, 60, 102, 16)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(204, 210, 128, 199, 109, 85, 222, 11)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(202, 197, 79, 202, 254, 40, 158, 224)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(209, 170, 47, 185, 53, 142, 137, 13)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(40, 191, 200, 41, 134, 97, 182, 145)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(217, 137, 166, 37, 185, 248, 93, 214)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(188, 95, 129, 252, 190, 49, 60, 207)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(186, 162, 40, 223, 118, 24, 158, 134)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(129, 50, 203, 113, 71, 15, 125, 124)}};
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
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*8, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed, .m_arity = 14, .m_num_fixed = 8, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__4_value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__5_value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value)} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_EnvLinter_builtin__env__linter___closed__0_value),LEAN_SCALAR_PTR_LITERAL(31, 8, 91, 236, 76, 189, 200, 47)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "Use this declaration as a linting test in `lake builtin-lint`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO___redArg();
return v___x_1_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0_once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__0);
v___x_3_ = l_StateRefT_x27_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(lean_object* v_optName_13_, lean_object* v_declName_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v___x_18_; lean_object* v_toApplicative_19_; lean_object* v_toFunctor_20_; lean_object* v_toSeq_21_; lean_object* v_toSeqLeft_22_; lean_object* v_toSeqRight_23_; lean_object* v___f_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___f_29_; lean_object* v___f_30_; lean_object* v___f_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_172__overap_42_; lean_object* v___x_43_; 
v___x_18_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1_once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__1);
v_toApplicative_19_ = lean_ctor_get(v___x_18_, 0);
v_toFunctor_20_ = lean_ctor_get(v_toApplicative_19_, 0);
v_toSeq_21_ = lean_ctor_get(v_toApplicative_19_, 2);
v_toSeqLeft_22_ = lean_ctor_get(v_toApplicative_19_, 3);
v_toSeqRight_23_ = lean_ctor_get(v_toApplicative_19_, 4);
v___f_24_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__2));
v___f_25_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__3));
lean_inc_ref_n(v_toFunctor_20_, 2);
v___f_26_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_26_, 0, v_toFunctor_20_);
v___f_27_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_27_, 0, v_toFunctor_20_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v___f_26_);
lean_ctor_set(v___x_28_, 1, v___f_27_);
lean_inc(v_toSeqRight_23_);
v___f_29_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_29_, 0, v_toSeqRight_23_);
lean_inc(v_toSeqLeft_22_);
v___f_30_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_30_, 0, v_toSeqLeft_22_);
lean_inc(v_toSeq_21_);
v___f_31_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_31_, 0, v_toSeq_21_);
v___x_32_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_32_, 0, v___x_28_);
lean_ctor_set(v___x_32_, 1, v___f_24_);
lean_ctor_set(v___x_32_, 2, v___f_31_);
lean_ctor_set(v___x_32_, 3, v___f_30_);
lean_ctor_set(v___x_32_, 4, v___f_29_);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___f_25_);
v___x_34_ = l_Lean_Core_instMonadEnvCoreM;
v___x_35_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_36_ = l_Lean_Core_instMonadRefCoreM;
v___x_37_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_33_);
v___x_38_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_37_, v___x_33_);
v___x_39_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_39_, 0, v___x_35_);
lean_ctor_set(v___x_39_, 1, v___x_36_);
lean_ctor_set(v___x_39_, 2, v___x_38_);
v___x_40_ = l_Lean_Core_instMonadOptionsCoreM;
v___x_41_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7));
lean_inc(v_declName_14_);
v___x_172__overap_42_ = l_Lean_evalConstCheck___redArg(v___x_33_, v___x_34_, v___x_39_, v___x_40_, v___x_41_, v_declName_14_);
lean_inc(v_a_16_);
lean_inc_ref(v_a_15_);
v___x_43_ = lean_apply_3(v___x_172__overap_42_, v_a_15_, v_a_16_, lean_box(0));
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v_a_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_52_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_52_ == 0)
{
v___x_46_ = v___x_43_;
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_a_44_);
lean_dec(v___x_43_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_52_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
v___x_48_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_48_, 0, v_a_44_);
lean_ctor_set(v___x_48_, 1, v_optName_13_);
lean_ctor_set(v___x_48_, 2, v_declName_14_);
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 0, v___x_48_);
v___x_50_ = v___x_46_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v___x_48_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
else
{
lean_object* v_a_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_60_; 
lean_dec(v_declName_14_);
lean_dec(v_optName_13_);
v_a_53_ = lean_ctor_get(v___x_43_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_60_ == 0)
{
v___x_55_ = v___x_43_;
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_a_53_);
lean_dec(v___x_43_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_60_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
lean_object* v___x_58_; 
if (v_isShared_56_ == 0)
{
v___x_58_ = v___x_55_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v_a_53_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___boxed(lean_object* v_optName_61_, lean_object* v_declName_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1(v_optName_61_, v_declName_62_, v_a_63_, v_a_64_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
return v_res_66_;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_box(0);
v___x_68_ = l_Lean_Elab_abortCommandExceptionId;
v___x_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg(){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_obj_once(&l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg___closed__0, &l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg___closed__0);
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg___boxed(lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg();
return v_res_74_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_75_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_79_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_alloc_ctor(0, 12, 0);
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
lean_ctor_set(v___x_81_, 10, v___x_79_);
lean_ctor_set(v___x_81_, 11, v___x_78_);
return v___x_81_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3(void){
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__4(void){
_start:
{
size_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_85_ = ((size_t)5ULL);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_unsigned_to_nat(32u);
v___x_88_ = lean_mk_empty_array_with_capacity(v___x_87_);
v___x_89_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_90_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_86_);
lean_ctor_set(v___x_90_, 3, v___x_86_);
lean_ctor_set_usize(v___x_90_, 4, v___x_85_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_box(1);
v___x_92_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__4);
v___x_93_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__1);
v___x_94_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_92_);
lean_ctor_set(v___x_94_, 2, v___x_91_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3(lean_object* v_msgData_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; lean_object* v_toCold_100_; lean_object* v_env_101_; lean_object* v_options_102_; uint8_t v___x_103_; lean_object* v_env_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_99_ = lean_st_ref_get(v___y_97_);
v_toCold_100_ = lean_ctor_get(v___y_96_, 0);
v_env_101_ = lean_ctor_get(v___x_99_, 0);
lean_inc_ref(v_env_101_);
lean_dec(v___x_99_);
v_options_102_ = lean_ctor_get(v_toCold_100_, 2);
v___x_103_ = 0;
v_env_104_ = l_Lean_Environment_setRecordingDeps(v_env_101_, v___x_103_);
v___x_105_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_106_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5);
lean_inc_ref(v_options_102_);
v___x_107_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_107_, 0, v_env_104_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_106_);
lean_ctor_set(v___x_107_, 3, v_options_102_);
v___x_108_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v_msgData_95_);
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3(v_msgData_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(lean_object* v_msg_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_ref_119_; lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_129_; 
v_ref_119_ = lean_ctor_get(v___y_116_, 2);
v___x_120_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3(v_msg_115_, v___y_116_, v___y_117_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_120_);
if (v_isSharedCheck_129_ == 0)
{
v___x_123_ = v___x_120_;
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v___x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_129_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_ref_119_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_ref_119_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set_tag(v___x_123_, 1);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_127_ = v___x_123_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v_msg_130_, v___y_131_, v___y_132_);
lean_dec(v___y_132_);
lean_dec_ref(v___y_131_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0___redArg(lean_object* v_x_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_a_139_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v_x_135_, 1);
v___x_140_ = l_Lean_stringToMessageData(v_a_139_);
v___x_141_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_140_, v___y_136_, v___y_137_);
return v___x_141_;
}
else
{
lean_object* v_a_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_149_; 
v_a_142_ = lean_ctor_get(v_x_135_, 0);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_135_);
if (v_isSharedCheck_149_ == 0)
{
v___x_144_ = v_x_135_;
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_a_142_);
lean_dec(v_x_135_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_149_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_147_; 
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 0);
v___x_147_ = v___x_144_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_a_142_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0___redArg___boxed(lean_object* v_x_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0___redArg(v_x_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0___redArg(lean_object* v_typeName_155_, lean_object* v_constName_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v___x_160_; lean_object* v_env_161_; uint8_t v___x_162_; 
v___x_160_ = lean_st_ref_get(v___y_158_);
v_env_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc_ref(v_env_161_);
lean_dec(v___x_160_);
lean_inc(v_constName_156_);
v___x_162_ = lean_has_compile_error(v_env_161_, v_constName_156_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v_env_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_163_ = lean_st_ref_get(v___y_158_);
v_env_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc_ref(v_env_164_);
lean_dec(v___x_163_);
v___x_165_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_157_);
v___x_166_ = l_Lean_Environment_evalConstCheck___redArg(v_env_164_, v___x_165_, v_typeName_155_, v_constName_156_);
lean_dec_ref(v___x_165_);
v___x_167_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0___redArg(v___x_166_, v___y_157_, v___y_158_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg();
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v___x_169_; lean_object* v_env_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec_ref_known(v___x_168_, 1);
v___x_169_ = lean_st_ref_get(v___y_158_);
v_env_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc_ref(v_env_170_);
lean_dec(v___x_169_);
v___x_171_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_157_);
v___x_172_ = l_Lean_Environment_evalConstCheck___redArg(v_env_170_, v___x_171_, v_typeName_155_, v_constName_156_);
lean_dec_ref(v___x_171_);
v___x_173_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0___redArg(v___x_172_, v___y_157_, v___y_158_);
return v___x_173_;
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec(v_constName_156_);
lean_dec(v_typeName_155_);
v_a_174_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_168_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_168_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0___redArg___boxed(lean_object* v_typeName_182_, lean_object* v_constName_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0___redArg(v_typeName_182_, v_constName_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter(lean_object* v_optName_188_, lean_object* v_declName_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_getEnvLinter_unsafe__1___closed__7));
lean_inc(v_declName_189_);
v___x_194_ = l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0___redArg(v___x_193_, v_declName_189_, v_a_190_, v_a_191_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_203_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_199_, 0, v_a_195_);
lean_ctor_set(v___x_199_, 1, v_optName_188_);
lean_ctor_set(v___x_199_, 2, v_declName_189_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_211_; 
lean_dec(v_declName_189_);
lean_dec(v_optName_188_);
v_a_204_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_211_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_211_ == 0)
{
v___x_206_ = v___x_194_;
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v___x_194_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_211_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_209_; 
if (v_isShared_207_ == 0)
{
v___x_209_ = v___x_206_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_a_204_);
v___x_209_ = v_reuseFailAlloc_210_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
return v___x_209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getEnvLinter___boxed(lean_object* v_optName_212_, lean_object* v_declName_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Linter_EnvLinter_getEnvLinter(v_optName_212_, v_declName_213_, v_a_214_, v_a_215_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1(lean_object* v_00_u03b1_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___redArg();
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1___boxed(lean_object* v_00_u03b1_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__1(v_00_u03b1_223_, v___y_224_, v___y_225_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0(lean_object* v_00_u03b1_228_, lean_object* v_typeName_229_, lean_object* v_constName_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0___redArg(v_typeName_229_, v_constName_230_, v___y_231_, v___y_232_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0___boxed(lean_object* v_00_u03b1_235_, lean_object* v_typeName_236_, lean_object* v_constName_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0(v_00_u03b1_235_, v_typeName_236_, v_constName_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0(lean_object* v_00_u03b1_242_, lean_object* v_x_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0___redArg(v_x_243_, v___y_244_, v___y_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0___boxed(lean_object* v_00_u03b1_248_, lean_object* v_x_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0(v_00_u03b1_248_, v_x_249_, v___y_250_, v___y_251_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_254_, lean_object* v_msg_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v_msg_255_, v___y_256_, v___y_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_260_, lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1(v_00_u03b1_260_, v_msg_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object* v_m_266_, lean_object* v_x_267_){
_start:
{
lean_object* v_fst_268_; lean_object* v_snd_269_; lean_object* v___x_270_; 
v_fst_268_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_fst_268_);
v_snd_269_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_snd_269_);
lean_dec_ref(v_x_267_);
v___x_270_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_268_, v_snd_269_, v_m_266_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_271_, size_t v_i_272_, size_t v_stop_273_, lean_object* v_b_274_){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = lean_usize_dec_eq(v_i_272_, v_stop_273_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v_fst_277_; lean_object* v_snd_278_; lean_object* v___x_279_; size_t v___x_280_; size_t v___x_281_; 
v___x_276_ = lean_array_uget_borrowed(v_as_271_, v_i_272_);
v_fst_277_ = lean_ctor_get(v___x_276_, 0);
v_snd_278_ = lean_ctor_get(v___x_276_, 1);
lean_inc(v_snd_278_);
lean_inc(v_fst_277_);
v___x_279_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_277_, v_snd_278_, v_b_274_);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_add(v_i_272_, v___x_280_);
v_i_272_ = v___x_281_;
v_b_274_ = v___x_279_;
goto _start;
}
else
{
return v_b_274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_283_, lean_object* v_i_284_, lean_object* v_stop_285_, lean_object* v_b_286_){
_start:
{
size_t v_i_boxed_287_; size_t v_stop_boxed_288_; lean_object* v_res_289_; 
v_i_boxed_287_ = lean_unbox_usize(v_i_284_);
lean_dec(v_i_284_);
v_stop_boxed_288_ = lean_unbox_usize(v_stop_285_);
lean_dec(v_stop_285_);
v_res_289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0_spec__0(v_as_283_, v_i_boxed_287_, v_stop_boxed_288_, v_b_286_);
lean_dec_ref(v_as_283_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0(lean_object* v_as_290_, size_t v_i_291_, size_t v_stop_292_, lean_object* v_b_293_){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = lean_usize_dec_eq(v_i_291_, v_stop_292_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v_fst_296_; lean_object* v_snd_297_; lean_object* v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v___x_301_; 
v___x_295_ = lean_array_uget_borrowed(v_as_290_, v_i_291_);
v_fst_296_ = lean_ctor_get(v___x_295_, 0);
v_snd_297_ = lean_ctor_get(v___x_295_, 1);
lean_inc(v_snd_297_);
lean_inc(v_fst_296_);
v___x_298_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_296_, v_snd_297_, v_b_293_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_add(v_i_291_, v___x_299_);
v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0_spec__0(v_as_290_, v___x_300_, v_stop_292_, v___x_298_);
return v___x_301_;
}
else
{
return v_b_293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0___boxed(lean_object* v_as_302_, lean_object* v_i_303_, lean_object* v_stop_304_, lean_object* v_b_305_){
_start:
{
size_t v_i_boxed_306_; size_t v_stop_boxed_307_; lean_object* v_res_308_; 
v_i_boxed_306_ = lean_unbox_usize(v_i_303_);
lean_dec(v_i_303_);
v_stop_boxed_307_ = lean_unbox_usize(v_stop_304_);
lean_dec(v_stop_304_);
v_res_308_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0(v_as_302_, v_i_boxed_306_, v_stop_boxed_307_, v_b_305_);
lean_dec_ref(v_as_302_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(lean_object* v_as_309_, size_t v_i_310_, size_t v_stop_311_, lean_object* v_b_312_){
_start:
{
lean_object* v___y_314_; uint8_t v___x_318_; 
v___x_318_ = lean_usize_dec_eq(v_i_310_, v_stop_311_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_319_ = lean_array_uget_borrowed(v_as_309_, v_i_310_);
v___x_320_ = lean_unsigned_to_nat(0u);
v___x_321_ = lean_array_get_size(v___x_319_);
v___x_322_ = lean_nat_dec_lt(v___x_320_, v___x_321_);
if (v___x_322_ == 0)
{
v___y_314_ = v_b_312_;
goto v___jp_313_;
}
else
{
size_t v___x_323_; size_t v___x_324_; lean_object* v___x_325_; 
v___x_323_ = ((size_t)0ULL);
v___x_324_ = lean_usize_of_nat(v___x_321_);
v___x_325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0(v___x_319_, v___x_323_, v___x_324_, v_b_312_);
v___y_314_ = v___x_325_;
goto v___jp_313_;
}
}
else
{
return v_b_312_;
}
v___jp_313_:
{
size_t v___x_315_; size_t v___x_316_; 
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_add(v_i_310_, v___x_315_);
v_i_310_ = v___x_316_;
v_b_312_ = v___y_314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_326_, lean_object* v_i_327_, lean_object* v_stop_328_, lean_object* v_b_329_){
_start:
{
size_t v_i_boxed_330_; size_t v_stop_boxed_331_; lean_object* v_res_332_; 
v_i_boxed_330_ = lean_unbox_usize(v_i_327_);
lean_dec(v_i_327_);
v_stop_boxed_331_ = lean_unbox_usize(v_stop_328_);
lean_dec(v_stop_328_);
v_res_332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(v_as_326_, v_i_boxed_330_, v_stop_boxed_331_, v_b_329_);
lean_dec_ref(v_as_326_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object* v_nss_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_334_ = lean_box(1);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = lean_array_get_size(v_nss_333_);
v___x_337_ = lean_nat_dec_lt(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
return v___x_334_;
}
else
{
size_t v___x_338_; size_t v___x_339_; lean_object* v___x_340_; 
v___x_338_ = ((size_t)0ULL);
v___x_339_ = lean_usize_of_nat(v___x_336_);
v___x_340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(v_nss_333_, v___x_338_, v___x_339_, v___x_334_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2____boxed(lean_object* v_nss_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(v_nss_341_);
lean_dec_ref(v_nss_341_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object* v_es_343_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lean_array_mk(v_es_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_));
v___x_364_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2____boxed(lean_object* v_a_365_){
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_();
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object* v_addEntryFn_394_, lean_object* v___x_395_, lean_object* v_s_396_){
_start:
{
lean_object* v_importedEntries_397_; lean_object* v_state_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_406_; 
v_importedEntries_397_ = lean_ctor_get(v_s_396_, 0);
v_state_398_ = lean_ctor_get(v_s_396_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_s_396_);
if (v_isSharedCheck_406_ == 0)
{
v___x_400_ = v_s_396_;
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_state_398_);
lean_inc(v_importedEntries_397_);
lean_dec(v_s_396_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_406_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_state_402_; lean_object* v___x_404_; 
v_state_402_ = lean_apply_2(v_addEntryFn_394_, v_state_398_, v___x_395_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 1, v_state_402_);
v___x_404_ = v___x_400_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_importedEntries_397_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_state_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10___redArg(lean_object* v_ref_407_, lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_toCold_412_; lean_object* v_currRecDepth_413_; lean_object* v_ref_414_; uint16_t v_optionFlags_415_; uint8_t v_suppressElabErrors_416_; uint8_t v_checkDeprecated_417_; uint8_t v_isRecordingDeps_418_; lean_object* v_ref_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v_toCold_412_ = lean_ctor_get(v___y_409_, 0);
v_currRecDepth_413_ = lean_ctor_get(v___y_409_, 1);
v_ref_414_ = lean_ctor_get(v___y_409_, 2);
v_optionFlags_415_ = lean_ctor_get_uint16(v___y_409_, sizeof(void*)*3);
v_suppressElabErrors_416_ = lean_ctor_get_uint8(v___y_409_, sizeof(void*)*3 + 2);
v_checkDeprecated_417_ = lean_ctor_get_uint8(v___y_409_, sizeof(void*)*3 + 3);
v_isRecordingDeps_418_ = lean_ctor_get_uint8(v___y_409_, sizeof(void*)*3 + 4);
v_ref_419_ = l_Lean_replaceRef(v_ref_407_, v_ref_414_);
lean_inc(v_currRecDepth_413_);
lean_inc_ref(v_toCold_412_);
v___x_420_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_420_, 0, v_toCold_412_);
lean_ctor_set(v___x_420_, 1, v_currRecDepth_413_);
lean_ctor_set(v___x_420_, 2, v_ref_419_);
lean_ctor_set_uint16(v___x_420_, sizeof(void*)*3, v_optionFlags_415_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*3 + 2, v_suppressElabErrors_416_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*3 + 3, v_checkDeprecated_417_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*3 + 4, v_isRecordingDeps_418_);
v___x_421_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v_msg_408_, v___x_420_, v___y_410_);
lean_dec_ref_known(v___x_420_, 3);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10___redArg___boxed(lean_object* v_ref_422_, lean_object* v_msg_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10___redArg(v_ref_422_, v_msg_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v_ref_422_);
return v_res_427_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__0));
v___x_430_ = l_Lean_stringToMessageData(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__2));
v___x_433_ = l_Lean_stringToMessageData(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__5(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__4));
v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__7(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__6));
v___x_439_ = l_Lean_stringToMessageData(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__9(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__8));
v___x_442_ = l_Lean_stringToMessageData(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__11(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__10));
v___x_445_ = l_Lean_stringToMessageData(v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__13(void){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__12));
v___x_448_ = l_Lean_stringToMessageData(v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg(lean_object* v_msg_449_, lean_object* v_declHint_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v_env_455_; uint8_t v___x_456_; 
v___x_453_ = lean_box(0);
v___x_454_ = lean_st_ref_get(v___y_451_);
v_env_455_ = lean_ctor_get(v___x_454_, 0);
lean_inc_ref(v_env_455_);
lean_dec(v___x_454_);
v___x_456_ = l_Lean_Name_isAnonymous(v_declHint_450_);
if (v___x_456_ == 0)
{
uint8_t v_isExporting_457_; 
v_isExporting_457_ = lean_ctor_get_uint8(v_env_455_, sizeof(void*)*13);
if (v_isExporting_457_ == 0)
{
lean_object* v___x_458_; 
lean_dec_ref(v_env_455_);
lean_dec(v_declHint_450_);
v___x_458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_458_, 0, v_msg_449_);
return v___x_458_;
}
else
{
lean_object* v___x_459_; uint8_t v___x_460_; 
lean_inc_ref(v_env_455_);
v___x_459_ = l_Lean_Environment_setExporting(v_env_455_, v___x_456_);
lean_inc(v_declHint_450_);
lean_inc_ref(v___x_459_);
v___x_460_ = l_Lean_Environment_contains(v___x_459_, v_declHint_450_, v_isExporting_457_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_dec_ref(v___x_459_);
lean_dec_ref(v_env_455_);
lean_dec(v_declHint_450_);
v___x_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_461_, 0, v_msg_449_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_c_467_; lean_object* v___x_468_; 
v___x_462_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_463_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5);
v___x_464_ = l_Lean_Options_empty;
lean_inc_ref(v___x_459_);
v___x_465_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_465_, 0, v___x_459_);
lean_ctor_set(v___x_465_, 1, v___x_462_);
lean_ctor_set(v___x_465_, 2, v___x_463_);
lean_ctor_set(v___x_465_, 3, v___x_464_);
lean_inc(v_declHint_450_);
v___x_466_ = l_Lean_MessageData_ofConstName(v_declHint_450_, v___x_456_);
v_c_467_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_467_, 0, v___x_465_);
lean_ctor_set(v_c_467_, 1, v___x_466_);
v___x_468_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_459_, v_declHint_450_);
lean_dec_ref(v___x_459_);
if (lean_obj_tag(v___x_468_) == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec_ref(v_env_455_);
lean_dec(v_declHint_450_);
v___x_469_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__1);
v___x_470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v_c_467_);
v___x_471_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__3);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = l_Lean_MessageData_note(v___x_472_);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v_msg_449_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_475_, 0, v___x_474_);
return v___x_475_;
}
else
{
lean_object* v_val_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_510_; 
v_val_476_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_510_ == 0)
{
v___x_478_ = v___x_468_;
v_isShared_479_ = v_isSharedCheck_510_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_val_476_);
lean_dec(v___x_468_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_510_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v_moduleNames_481_; lean_object* v_mod_482_; uint8_t v___x_483_; 
v___x_480_ = l_Lean_Environment_header(v_env_455_);
lean_dec_ref(v_env_455_);
v_moduleNames_481_ = lean_ctor_get(v___x_480_, 4);
lean_inc_ref(v_moduleNames_481_);
lean_dec_ref(v___x_480_);
v_mod_482_ = lean_array_get(v___x_453_, v_moduleNames_481_, v_val_476_);
lean_dec(v_val_476_);
lean_dec_ref(v_moduleNames_481_);
v___x_483_ = l_Lean_isPrivateName(v_declHint_450_);
lean_dec(v_declHint_450_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_484_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__5);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_c_467_);
v___x_486_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__7);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = l_Lean_MessageData_ofName(v_mod_482_);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__9);
v___x_491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set(v___x_491_, 1, v___x_490_);
v___x_492_ = l_Lean_MessageData_note(v___x_491_);
v___x_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_493_, 0, v_msg_449_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
if (v_isShared_479_ == 0)
{
lean_ctor_set_tag(v___x_478_, 0);
lean_ctor_set(v___x_478_, 0, v___x_493_);
v___x_495_ = v___x_478_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_497_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__1);
v___x_498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_c_467_);
v___x_499_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__11);
v___x_500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_498_);
lean_ctor_set(v___x_500_, 1, v___x_499_);
v___x_501_ = l_Lean_MessageData_ofName(v_mod_482_);
v___x_502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_502_, 0, v___x_500_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v___x_503_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___closed__13);
v___x_504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_502_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v___x_505_ = l_Lean_MessageData_note(v___x_504_);
v___x_506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_506_, 0, v_msg_449_);
lean_ctor_set(v___x_506_, 1, v___x_505_);
if (v_isShared_479_ == 0)
{
lean_ctor_set_tag(v___x_478_, 0);
lean_ctor_set(v___x_478_, 0, v___x_506_);
v___x_508_ = v___x_478_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_511_; 
lean_dec_ref(v_env_455_);
lean_dec(v_declHint_450_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v_msg_449_);
return v___x_511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg___boxed(lean_object* v_msg_512_, lean_object* v_declHint_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg(v_msg_512_, v_declHint_513_, v___y_514_);
lean_dec(v___y_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(lean_object* v_msg_517_, lean_object* v_declHint_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_532_; 
v___x_522_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg(v_msg_517_, v_declHint_518_, v___y_520_);
v_a_523_ = lean_ctor_get(v___x_522_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_522_);
if (v_isSharedCheck_532_ == 0)
{
v___x_525_ = v___x_522_;
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_522_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_532_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_530_; 
v___x_527_ = l_Lean_unknownIdentifierMessageTag;
v___x_528_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_a_523_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_528_);
v___x_530_ = v___x_525_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9___boxed(lean_object* v_msg_533_, lean_object* v_declHint_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(v_msg_533_, v_declHint_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_ref_539_, lean_object* v_msg_540_, lean_object* v_declHint_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; lean_object* v_a_546_; lean_object* v___x_547_; 
v___x_545_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9(v_msg_540_, v_declHint_541_, v___y_542_, v___y_543_);
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref(v___x_545_);
v___x_547_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10___redArg(v_ref_539_, v_a_546_, v___y_542_, v___y_543_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_ref_548_, lean_object* v_msg_549_, lean_object* v_declHint_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_ref_548_, v_msg_549_, v_declHint_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v_ref_548_);
return v_res_554_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0));
v___x_557_ = l_Lean_stringToMessageData(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_559_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2));
v___x_560_ = l_Lean_stringToMessageData(v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_ref_561_, lean_object* v_constName_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_566_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_567_ = 0;
lean_inc(v_constName_562_);
v___x_568_ = l_Lean_MessageData_ofConstName(v_constName_562_, v___x_567_);
v___x_569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_566_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
v___x_571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_569_);
lean_ctor_set(v___x_571_, 1, v___x_570_);
v___x_572_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_ref_561_, v___x_571_, v_constName_562_, v___y_563_, v___y_564_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_573_, lean_object* v_constName_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_573_, v_constName_574_, v___y_575_, v___y_576_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec(v_ref_573_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_constName_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_ref_583_; lean_object* v___x_584_; 
v_ref_583_ = lean_ctor_get(v___y_580_, 2);
v___x_584_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_583_, v_constName_579_, v___y_580_, v___y_581_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_constName_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0(lean_object* v_constName_590_, lean_object* v___y_591_, lean_object* v___y_592_){
_start:
{
lean_object* v___x_594_; lean_object* v_env_595_; uint8_t v___x_596_; lean_object* v___x_597_; 
v___x_594_ = lean_st_ref_get(v___y_592_);
v_env_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc_ref(v_env_595_);
lean_dec(v___x_594_);
v___x_596_ = 0;
lean_inc(v_constName_590_);
v___x_597_ = l_Lean_Environment_find_x3f(v_env_595_, v_constName_590_, v___x_596_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_590_, v___y_591_, v___y_592_);
return v___x_598_;
}
else
{
lean_object* v_val_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_606_; 
lean_dec(v_constName_590_);
v_val_599_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_606_ == 0)
{
v___x_601_ = v___x_597_;
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_val_599_);
lean_dec(v___x_597_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_606_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set_tag(v___x_601_, 0);
v___x_604_ = v___x_601_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_val_599_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0___boxed(lean_object* v_constName_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0(v_constName_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_611_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg(){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg___closed__0);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v___dummy_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg();
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4_spec__6(lean_object* v_constName_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; lean_object* v_env_623_; uint8_t v___x_624_; lean_object* v___x_625_; 
v___x_622_ = lean_st_ref_get(v___y_620_);
v_env_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc_ref(v_env_623_);
lean_dec(v___x_622_);
v___x_624_ = 0;
lean_inc(v_constName_618_);
v___x_625_ = l_Lean_Environment_findConstVal_x3f(v_env_623_, v_constName_618_, v___x_624_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_618_, v___y_619_, v___y_620_);
return v___x_626_;
}
else
{
lean_object* v_val_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec(v_constName_618_);
v_val_627_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_625_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_val_627_);
lean_dec(v___x_625_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 0);
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_val_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4_spec__6___boxed(lean_object* v_constName_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4_spec__6(v_constName_635_, v___y_636_, v___y_637_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4_spec__7(lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
if (lean_obj_tag(v_a_640_) == 0)
{
lean_object* v___x_642_; 
v___x_642_ = l_List_reverse___redArg(v_a_641_);
return v___x_642_;
}
else
{
lean_object* v_head_643_; lean_object* v_tail_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_653_; 
v_head_643_ = lean_ctor_get(v_a_640_, 0);
v_tail_644_ = lean_ctor_get(v_a_640_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_a_640_);
if (v_isSharedCheck_653_ == 0)
{
v___x_646_ = v_a_640_;
v_isShared_647_ = v_isSharedCheck_653_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_tail_644_);
lean_inc(v_head_643_);
lean_dec(v_a_640_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_653_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = l_Lean_mkLevelParam(v_head_643_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v_a_641_);
lean_ctor_set(v___x_646_, 0, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_648_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_a_641_);
v___x_650_ = v_reuseFailAlloc_652_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
v_a_640_ = v_tail_644_;
v_a_641_ = v___x_650_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4(lean_object* v_constName_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v___x_658_; 
lean_inc(v_constName_654_);
v___x_658_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4_spec__6(v_constName_654_, v___y_655_, v___y_656_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_670_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_670_ == 0)
{
v___x_661_ = v___x_658_;
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_658_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_670_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v_levelParams_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v_levelParams_663_ = lean_ctor_get(v_a_659_, 1);
lean_inc(v_levelParams_663_);
lean_dec(v_a_659_);
v___x_664_ = lean_box(0);
v___x_665_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4_spec__7(v_levelParams_663_, v___x_664_);
v___x_666_ = l_Lean_mkConst(v_constName_654_, v___x_665_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 0, v___x_666_);
v___x_668_ = v___x_661_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
lean_dec(v_constName_654_);
v_a_671_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_658_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_658_);
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
return v___x_676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4___boxed(lean_object* v_constName_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4(v_constName_679_, v___y_680_, v___y_681_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
return v_res_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9___redArg(lean_object* v_t_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; lean_object* v_infoState_688_; uint8_t v_enabled_689_; 
v___x_687_ = lean_st_ref_get(v___y_685_);
v_infoState_688_ = lean_ctor_get(v___x_687_, 8);
lean_inc_ref(v_infoState_688_);
lean_dec(v___x_687_);
v_enabled_689_ = lean_ctor_get_uint8(v_infoState_688_, sizeof(void*)*3);
lean_dec_ref(v_infoState_688_);
if (v_enabled_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec_ref(v_t_684_);
v___x_690_ = lean_box(0);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
else
{
lean_object* v___x_692_; lean_object* v_infoState_693_; lean_object* v_env_694_; lean_object* v_nextMacroScope_695_; lean_object* v_ngen_696_; lean_object* v_auxDeclNGen_697_; lean_object* v_traceState_698_; lean_object* v_cache_699_; lean_object* v_recordedDeps_700_; lean_object* v_messages_701_; lean_object* v_snapshotTasks_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_724_; 
v___x_692_ = lean_st_ref_take(v___y_685_);
v_infoState_693_ = lean_ctor_get(v___x_692_, 8);
v_env_694_ = lean_ctor_get(v___x_692_, 0);
v_nextMacroScope_695_ = lean_ctor_get(v___x_692_, 1);
v_ngen_696_ = lean_ctor_get(v___x_692_, 2);
v_auxDeclNGen_697_ = lean_ctor_get(v___x_692_, 3);
v_traceState_698_ = lean_ctor_get(v___x_692_, 4);
v_cache_699_ = lean_ctor_get(v___x_692_, 5);
v_recordedDeps_700_ = lean_ctor_get(v___x_692_, 6);
v_messages_701_ = lean_ctor_get(v___x_692_, 7);
v_snapshotTasks_702_ = lean_ctor_get(v___x_692_, 9);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_724_ == 0)
{
v___x_704_ = v___x_692_;
v_isShared_705_ = v_isSharedCheck_724_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_snapshotTasks_702_);
lean_inc(v_infoState_693_);
lean_inc(v_messages_701_);
lean_inc(v_recordedDeps_700_);
lean_inc(v_cache_699_);
lean_inc(v_traceState_698_);
lean_inc(v_auxDeclNGen_697_);
lean_inc(v_ngen_696_);
lean_inc(v_nextMacroScope_695_);
lean_inc(v_env_694_);
lean_dec(v___x_692_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_724_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint8_t v_enabled_706_; lean_object* v_assignment_707_; lean_object* v_lazyAssignment_708_; lean_object* v_trees_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_723_; 
v_enabled_706_ = lean_ctor_get_uint8(v_infoState_693_, sizeof(void*)*3);
v_assignment_707_ = lean_ctor_get(v_infoState_693_, 0);
v_lazyAssignment_708_ = lean_ctor_get(v_infoState_693_, 1);
v_trees_709_ = lean_ctor_get(v_infoState_693_, 2);
v_isSharedCheck_723_ = !lean_is_exclusive(v_infoState_693_);
if (v_isSharedCheck_723_ == 0)
{
v___x_711_ = v_infoState_693_;
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_trees_709_);
lean_inc(v_lazyAssignment_708_);
lean_inc(v_assignment_707_);
lean_dec(v_infoState_693_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_723_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_box(0);
v___x_714_ = l_Lean_PersistentArray_push___redArg(v_trees_709_, v_t_684_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 2, v___x_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_assignment_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_lazyAssignment_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v___x_714_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, sizeof(void*)*3, v_enabled_706_);
v___x_716_ = v_reuseFailAlloc_722_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 8, v___x_716_);
v___x_718_ = v___x_704_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_env_694_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_nextMacroScope_695_);
lean_ctor_set(v_reuseFailAlloc_721_, 2, v_ngen_696_);
lean_ctor_set(v_reuseFailAlloc_721_, 3, v_auxDeclNGen_697_);
lean_ctor_set(v_reuseFailAlloc_721_, 4, v_traceState_698_);
lean_ctor_set(v_reuseFailAlloc_721_, 5, v_cache_699_);
lean_ctor_set(v_reuseFailAlloc_721_, 6, v_recordedDeps_700_);
lean_ctor_set(v_reuseFailAlloc_721_, 7, v_messages_701_);
lean_ctor_set(v_reuseFailAlloc_721_, 8, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_721_, 9, v_snapshotTasks_702_);
v___x_718_ = v_reuseFailAlloc_721_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_st_ref_put(v___y_685_, v___x_718_);
v___x_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_713_);
return v___x_720_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_t_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9___redArg(v_t_725_, v___y_726_);
lean_dec(v___y_726_);
return v_res_728_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__0(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_729_ = lean_unsigned_to_nat(32u);
v___x_730_ = lean_mk_empty_array_with_capacity(v___x_729_);
v___x_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__1(void){
_start:
{
size_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = ((size_t)5ULL);
v___x_733_ = lean_unsigned_to_nat(0u);
v___x_734_ = lean_unsigned_to_nat(32u);
v___x_735_ = lean_mk_empty_array_with_capacity(v___x_734_);
v___x_736_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__0);
v___x_737_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_737_, 0, v___x_736_);
lean_ctor_set(v___x_737_, 1, v___x_735_);
lean_ctor_set(v___x_737_, 2, v___x_733_);
lean_ctor_set(v___x_737_, 3, v___x_733_);
lean_ctor_set_usize(v___x_737_, 4, v___x_732_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5(lean_object* v_t_738_, lean_object* v___y_739_, lean_object* v___y_740_){
_start:
{
lean_object* v___x_742_; lean_object* v_infoState_743_; uint8_t v_enabled_744_; 
v___x_742_ = lean_st_ref_get(v___y_740_);
v_infoState_743_ = lean_ctor_get(v___x_742_, 8);
lean_inc_ref(v_infoState_743_);
lean_dec(v___x_742_);
v_enabled_744_ = lean_ctor_get_uint8(v_infoState_743_, sizeof(void*)*3);
lean_dec_ref(v_infoState_743_);
if (v_enabled_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; 
lean_dec_ref(v_t_738_);
v___x_745_ = lean_box(0);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_747_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___closed__1);
v___x_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_748_, 0, v_t_738_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9___redArg(v___x_748_, v___y_740_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5___boxed(lean_object* v_t_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5(v_t_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2(lean_object* v_stx_755_, lean_object* v_n_756_, lean_object* v_expectedType_x3f_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__4(v_n_756_, v___y_758_, v___y_759_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = lean_box(0);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v_stx_755_);
v___x_765_ = l_Lean_LocalContext_empty;
v___x_766_ = 0;
v___x_767_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_767_, 0, v___x_764_);
lean_ctor_set(v___x_767_, 1, v___x_765_);
lean_ctor_set(v___x_767_, 2, v_expectedType_x3f_757_);
lean_ctor_set(v___x_767_, 3, v_a_762_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*4, v___x_766_);
lean_ctor_set_uint8(v___x_767_, sizeof(void*)*4 + 1, v___x_766_);
v___x_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
v___x_769_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5(v___x_768_, v___y_758_, v___y_759_);
return v___x_769_;
}
else
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_777_; 
lean_dec(v_expectedType_x3f_757_);
lean_dec(v_stx_755_);
v_a_770_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_777_ == 0)
{
v___x_772_ = v___x_761_;
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_761_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_777_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_a_770_);
v___x_775_ = v_reuseFailAlloc_776_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2___boxed(lean_object* v_stx_778_, lean_object* v_n_779_, lean_object* v_expectedType_x3f_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2(v_stx_778_, v_n_779_, v_expectedType_x3f_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_784_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v___x_785_);
return v___x_786_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
return v___x_788_;
}
}
static uint64_t _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_795_; uint64_t v___x_796_; 
v___x_795_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_796_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_795_);
return v___x_796_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = lean_uint64_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_798_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_799_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_799_, 0, v___x_798_);
lean_ctor_set_uint64(v___x_799_, sizeof(void*)*1, v___x_797_);
return v___x_799_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___redArg();
return v___x_802_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_804_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_805_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_803_);
lean_ctor_set(v___x_805_, 2, v___x_803_);
lean_ctor_set(v___x_805_, 3, v___x_803_);
lean_ctor_set(v___x_805_, 4, v___x_803_);
lean_ctor_set(v___x_805_, 5, v___x_803_);
lean_ctor_set(v___x_805_, 6, v___x_803_);
return v___x_805_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
lean_ctor_set(v___x_807_, 2, v___x_806_);
lean_ctor_set(v___x_807_, 3, v___x_806_);
lean_ctor_set(v___x_807_, 4, v___x_806_);
return v___x_807_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_809_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_810_ = l_Lean_stringToMessageData(v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_812_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
return v___x_813_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_818_ = l_Lean_stringToMessageData(v___x_817_);
return v___x_818_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_821_ = l_Lean_stringToMessageData(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_831_ = l_Lean_stringToMessageData(v___x_830_);
return v___x_831_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_834_ = l_Lean_stringToMessageData(v___x_833_);
return v___x_834_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_837_ = l_Lean_stringToMessageData(v___x_836_);
return v___x_837_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_839_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_840_ = l_Lean_stringToMessageData(v___x_839_);
return v___x_840_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__33_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_843_ = l_Lean_stringToMessageData(v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object* v___x_844_, lean_object* v___x_845_, lean_object* v___x_846_, lean_object* v___x_847_, lean_object* v___x_848_, lean_object* v___x_849_, lean_object* v___x_850_, lean_object* v___x_851_, lean_object* v_decl_852_, lean_object* v_stx_853_, uint8_t v_kind_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___y_859_; lean_object* v_nextMacroScope_860_; lean_object* v_ngen_861_; lean_object* v_auxDeclNGen_862_; lean_object* v_traceState_863_; lean_object* v_recordedDeps_864_; lean_object* v_messages_865_; lean_object* v_infoState_866_; lean_object* v_snapshotTasks_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_972_; lean_object* v___y_973_; uint8_t v___y_974_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_983_; uint8_t v___y_984_; lean_object* v___y_985_; uint8_t v___y_986_; lean_object* v___y_987_; uint8_t v___y_988_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v_optName_1026_; lean_object* v___y_1027_; lean_object* v___y_1028_; uint8_t v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = 0;
v___x_1071_ = l_Lean_instBEqAttributeKind_beq(v_kind_854_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec(v_stx_853_);
lean_dec(v_decl_852_);
lean_dec_ref(v___x_851_);
lean_dec(v___x_850_);
lean_dec(v___x_849_);
lean_dec(v___x_848_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v___x_846_);
lean_dec_ref(v___x_845_);
lean_dec(v___x_844_);
v___x_1072_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__33_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__33_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__33_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1073_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1072_, v___y_855_, v___y_856_);
return v___x_1073_;
}
else
{
goto v___jp_1042_;
}
v___jp_858_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_870_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_871_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_871_, 0, v___y_869_);
lean_ctor_set(v___x_871_, 1, v_nextMacroScope_860_);
lean_ctor_set(v___x_871_, 2, v_ngen_861_);
lean_ctor_set(v___x_871_, 3, v_auxDeclNGen_862_);
lean_ctor_set(v___x_871_, 4, v_traceState_863_);
lean_ctor_set(v___x_871_, 5, v___x_870_);
lean_ctor_set(v___x_871_, 6, v_recordedDeps_864_);
lean_ctor_set(v___x_871_, 7, v_messages_865_);
lean_ctor_set(v___x_871_, 8, v_infoState_866_);
lean_ctor_set(v___x_871_, 9, v_snapshotTasks_867_);
v___x_872_ = lean_st_ref_put(v___y_868_, v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_873_, 0, v___y_859_);
return v___x_873_;
}
v___jp_874_:
{
lean_object* v___x_877_; lean_object* v_env_878_; lean_object* v_nextMacroScope_879_; lean_object* v_ngen_880_; lean_object* v_auxDeclNGen_881_; lean_object* v_traceState_882_; lean_object* v_recordedDeps_883_; lean_object* v_messages_884_; lean_object* v_infoState_885_; lean_object* v_snapshotTasks_886_; lean_object* v___x_887_; lean_object* v_toEnvExtension_888_; lean_object* v_addEntryFn_889_; lean_object* v_asyncMode_890_; uint8_t v_logWrites_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___f_894_; uint8_t v___x_895_; 
v___x_877_ = lean_st_ref_take(v___y_876_);
v_env_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc_ref(v_env_878_);
v_nextMacroScope_879_ = lean_ctor_get(v___x_877_, 1);
lean_inc(v_nextMacroScope_879_);
v_ngen_880_ = lean_ctor_get(v___x_877_, 2);
lean_inc_ref(v_ngen_880_);
v_auxDeclNGen_881_ = lean_ctor_get(v___x_877_, 3);
lean_inc_ref(v_auxDeclNGen_881_);
v_traceState_882_ = lean_ctor_get(v___x_877_, 4);
lean_inc_ref(v_traceState_882_);
v_recordedDeps_883_ = lean_ctor_get(v___x_877_, 6);
lean_inc_ref(v_recordedDeps_883_);
v_messages_884_ = lean_ctor_get(v___x_877_, 7);
lean_inc_ref(v_messages_884_);
v_infoState_885_ = lean_ctor_get(v___x_877_, 8);
lean_inc_ref(v_infoState_885_);
v_snapshotTasks_886_ = lean_ctor_get(v___x_877_, 9);
lean_inc_ref(v_snapshotTasks_886_);
lean_dec(v___x_877_);
v___x_887_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_888_ = lean_ctor_get(v___x_887_, 0);
v_addEntryFn_889_ = lean_ctor_get(v___x_887_, 3);
v_asyncMode_890_ = lean_ctor_get(v_toEnvExtension_888_, 2);
v_logWrites_891_ = lean_ctor_get_uint8(v_toEnvExtension_888_, sizeof(void*)*6);
v___x_892_ = lean_box(0);
v___x_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_893_, 0, v___y_875_);
lean_ctor_set(v___x_893_, 1, v_decl_852_);
lean_inc(v_addEntryFn_889_);
v___f_894_ = lean_alloc_closure((void*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_894_, 0, v_addEntryFn_889_);
lean_closure_set(v___f_894_, 1, v___x_893_);
v___x_895_ = 1;
if (v_logWrites_891_ == 0)
{
lean_object* v___x_896_; 
lean_inc_ref(v_toEnvExtension_888_);
v___x_896_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_888_, v_env_878_, v___f_894_, v_asyncMode_890_, v___x_844_, v___x_895_);
v___y_859_ = v___x_892_;
v_nextMacroScope_860_ = v_nextMacroScope_879_;
v_ngen_861_ = v_ngen_880_;
v_auxDeclNGen_862_ = v_auxDeclNGen_881_;
v_traceState_863_ = v_traceState_882_;
v_recordedDeps_864_ = v_recordedDeps_883_;
v_messages_865_ = v_messages_884_;
v_infoState_866_ = v_infoState_885_;
v_snapshotTasks_867_ = v_snapshotTasks_886_;
v___y_868_ = v___y_876_;
v___y_869_ = v___x_896_;
goto v___jp_858_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_inc_ref_n(v_toEnvExtension_888_, 2);
v___x_897_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_888_, v_env_878_);
lean_dec_ref(v_env_878_);
v___x_898_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_888_, v___x_897_, v___f_894_, v_asyncMode_890_, v___x_844_, v___x_895_);
v___y_859_ = v___x_892_;
v_nextMacroScope_860_ = v_nextMacroScope_879_;
v_ngen_861_ = v_ngen_880_;
v_auxDeclNGen_862_ = v_auxDeclNGen_881_;
v_traceState_863_ = v_traceState_882_;
v_recordedDeps_864_ = v_recordedDeps_883_;
v_messages_865_ = v_messages_884_;
v_infoState_866_ = v_infoState_885_;
v_snapshotTasks_867_ = v_snapshotTasks_886_;
v___y_868_ = v___y_876_;
v___y_869_ = v___x_898_;
goto v___jp_858_;
}
}
v___jp_899_:
{
lean_object* v___x_903_; 
lean_inc(v_decl_852_);
v___x_903_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0(v_decl_852_, v___y_901_, v___y_902_);
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v_a_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; uint8_t v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; size_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_a_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_a_904_);
lean_dec_ref_known(v___x_903_, 1);
v___x_905_ = l_Lean_ConstantInfo_type(v_a_904_);
lean_dec(v_a_904_);
lean_inc_ref(v___x_847_);
v___x_906_ = l_Lean_Name_mkStr4(v___x_845_, v___x_846_, v___x_847_, v___x_847_);
v___x_907_ = lean_box(0);
lean_inc(v___x_906_);
v___x_908_ = l_Lean_mkConst(v___x_906_, v___x_907_);
v___x_909_ = 0;
v___x_910_ = 1;
v___x_911_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_912_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_913_ = lean_unsigned_to_nat(32u);
v___x_914_ = lean_mk_empty_array_with_capacity(v___x_913_);
v___x_915_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_916_ = ((size_t)5ULL);
lean_inc_n(v___x_848_, 6);
v___x_917_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_914_);
lean_ctor_set(v___x_917_, 2, v___x_848_);
lean_ctor_set(v___x_917_, 3, v___x_848_);
lean_ctor_set_usize(v___x_917_, 4, v___x_916_);
v___x_918_ = lean_box(1);
lean_inc_ref(v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_919_, 0, v___x_912_);
lean_ctor_set(v___x_919_, 1, v___x_917_);
lean_ctor_set(v___x_919_, 2, v___x_918_);
v___x_920_ = lean_mk_empty_array_with_capacity(v___x_848_);
v___x_921_ = lean_box(0);
lean_inc(v___x_849_);
v___x_922_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_922_, 0, v___x_911_);
lean_ctor_set(v___x_922_, 1, v___x_849_);
lean_ctor_set(v___x_922_, 2, v___x_919_);
lean_ctor_set(v___x_922_, 3, v___x_920_);
lean_ctor_set(v___x_922_, 4, v___x_921_);
lean_ctor_set(v___x_922_, 5, v___x_848_);
lean_ctor_set(v___x_922_, 6, v___x_921_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*7, v___x_909_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*7 + 1, v___x_909_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*7 + 2, v___x_909_);
lean_ctor_set_uint8(v___x_922_, sizeof(void*)*7 + 3, v___x_910_);
v___x_923_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_924_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_924_, 0, v___x_848_);
lean_ctor_set(v___x_924_, 1, v___x_848_);
lean_ctor_set(v___x_924_, 2, v___x_848_);
lean_ctor_set(v___x_924_, 3, v___x_848_);
lean_ctor_set(v___x_924_, 4, v___x_912_);
lean_ctor_set(v___x_924_, 5, v___x_912_);
lean_ctor_set(v___x_924_, 6, v___x_912_);
lean_ctor_set(v___x_924_, 7, v___x_912_);
lean_ctor_set(v___x_924_, 8, v___x_912_);
lean_ctor_set(v___x_924_, 9, v___x_912_);
lean_ctor_set(v___x_924_, 10, v___x_912_);
lean_ctor_set(v___x_924_, 11, v___x_923_);
v___x_925_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_926_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_927_, 0, v___x_924_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
lean_ctor_set(v___x_927_, 2, v___x_849_);
lean_ctor_set(v___x_927_, 3, v___x_917_);
lean_ctor_set(v___x_927_, 4, v___x_926_);
v___x_928_ = lean_st_mk_ref(v___x_927_);
lean_inc_ref(v___x_905_);
v___x_929_ = l_Lean_Meta_isExprDefEq(v___x_905_, v___x_908_, v___x_922_, v___x_928_, v___y_901_, v___y_902_);
lean_dec_ref_known(v___x_922_, 7);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
lean_inc(v_a_930_);
lean_dec_ref_known(v___x_929_, 1);
v___x_931_ = lean_st_ref_get(v___x_928_);
lean_dec(v___x_928_);
lean_dec(v___x_931_);
v___x_932_ = lean_unbox(v_a_930_);
lean_dec(v_a_930_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v___y_900_);
lean_dec(v___x_844_);
v___x_933_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
v___x_934_ = l_Lean_MessageData_ofConstName(v_decl_852_, v___x_909_);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_933_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_MessageData_ofConstName(v___x_906_, v___x_909_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Lean_MessageData_ofExpr(v___x_905_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v___x_933_);
v___x_945_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_944_, v___y_901_, v___y_902_);
return v___x_945_;
}
else
{
lean_dec(v___x_906_);
lean_dec_ref(v___x_905_);
v___y_875_ = v___y_900_;
v___y_876_ = v___y_902_;
goto v___jp_874_;
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v___x_928_);
lean_dec(v___x_906_);
lean_dec_ref(v___x_905_);
lean_dec(v___y_900_);
lean_dec(v_decl_852_);
lean_dec(v___x_844_);
v_a_946_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_929_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_929_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v___y_900_);
lean_dec(v_decl_852_);
lean_dec(v___x_849_);
lean_dec(v___x_848_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v___x_846_);
lean_dec_ref(v___x_845_);
lean_dec(v___x_844_);
v_a_954_ = lean_ctor_get(v___x_903_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_903_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_903_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
v___jp_962_:
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec(v___y_965_);
lean_inc_ref(v___y_967_);
v___x_968_ = l_Lean_stringToMessageData(v___y_967_);
v___x_969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_969_, 0, v___y_964_);
lean_ctor_set(v___x_969_, 1, v___x_968_);
v___x_970_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_969_, v___y_963_, v___y_966_);
return v___x_970_;
}
v___jp_971_:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
lean_inc_ref(v___y_977_);
v___x_978_ = l_Lean_stringToMessageData(v___y_977_);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___y_976_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
if (v___y_974_ == 0)
{
lean_object* v___x_980_; 
v___x_980_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_963_ = v___y_972_;
v___y_964_ = v___x_979_;
v___y_965_ = v___y_973_;
v___y_966_ = v___y_975_;
v___y_967_ = v___x_980_;
goto v___jp_962_;
}
else
{
lean_object* v___x_981_; 
v___x_981_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_963_ = v___y_972_;
v___y_964_ = v___x_979_;
v___y_965_ = v___y_973_;
v___y_966_ = v___y_975_;
v___y_967_ = v___x_981_;
goto v___jp_962_;
}
}
v___jp_982_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_989_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_990_ = l_Lean_MessageData_ofConstName(v_decl_852_, v___y_988_);
v___x_991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_989_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
v___x_992_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_991_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
if (v___y_984_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_972_ = v___y_983_;
v___y_973_ = v___y_985_;
v___y_974_ = v___y_986_;
v___y_975_ = v___y_987_;
v___y_976_ = v___x_993_;
v___y_977_ = v___x_994_;
goto v___jp_971_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_972_ = v___y_983_;
v___y_973_ = v___y_985_;
v___y_974_ = v___y_986_;
v___y_975_ = v___y_987_;
v___y_976_ = v___x_993_;
v___y_977_ = v___x_995_;
goto v___jp_971_;
}
}
v___jp_996_:
{
uint8_t v___x_1001_; 
v___x_1001_ = l_Lean_isPrivateName(v_decl_852_);
if (v___x_1001_ == 0)
{
uint8_t v___x_1002_; 
lean_inc(v_decl_852_);
v___x_1002_ = l_Lean_isMarkedMeta(v___y_997_, v_decl_852_);
if (v___x_1002_ == 0)
{
uint8_t v___x_1003_; 
lean_dec(v___x_849_);
lean_dec(v___x_848_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v___x_846_);
lean_dec_ref(v___x_845_);
lean_dec(v___x_844_);
v___x_1003_ = 1;
v___y_983_ = v___y_999_;
v___y_984_ = v___x_1003_;
v___y_985_ = v___y_998_;
v___y_986_ = v___x_1002_;
v___y_987_ = v___y_1000_;
v___y_988_ = v___x_1002_;
goto v___jp_982_;
}
else
{
v___y_900_ = v___y_998_;
v___y_901_ = v___y_999_;
v___y_902_ = v___y_1000_;
goto v___jp_899_;
}
}
else
{
uint8_t v___x_1004_; uint8_t v___x_1005_; 
lean_dec(v___x_849_);
lean_dec(v___x_848_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v___x_846_);
lean_dec_ref(v___x_845_);
lean_dec(v___x_844_);
v___x_1004_ = 0;
lean_inc(v_decl_852_);
v___x_1005_ = l_Lean_isMarkedMeta(v___y_997_, v_decl_852_);
v___y_983_ = v___y_999_;
v___y_984_ = v___x_1004_;
v___y_985_ = v___y_998_;
v___y_986_ = v___x_1005_;
v___y_987_ = v___y_1000_;
v___y_988_ = v___x_1004_;
goto v___jp_982_;
}
}
v___jp_1006_:
{
lean_object* v___x_1011_; lean_object* v_toEnvExtension_1012_; lean_object* v_asyncMode_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; 
v___x_1011_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_1012_ = lean_ctor_get(v___x_1011_, 0);
v_asyncMode_1013_ = lean_ctor_get(v_toEnvExtension_1012_, 2);
lean_inc(v___x_844_);
lean_inc_ref(v___y_1007_);
v___x_1014_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_850_, v___x_1011_, v___y_1007_, v_asyncMode_1013_, v___x_844_);
v___x_1015_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1014_, v___y_1008_);
lean_dec(v___x_1014_);
if (lean_obj_tag(v___x_1015_) == 1)
{
lean_object* v_val_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec_ref(v___y_1007_);
lean_dec(v_decl_852_);
lean_dec(v___x_849_);
lean_dec(v___x_848_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v___x_846_);
lean_dec_ref(v___x_845_);
lean_dec(v___x_844_);
v_val_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v___x_1015_, 1);
v___x_1017_ = lean_box(0);
v___x_1018_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2(v_stx_853_, v_val_1016_, v___x_1017_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec_ref_known(v___x_1018_, 1);
v___x_1019_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1020_ = l_Lean_MessageData_ofName(v___y_1008_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1023_, v___y_1009_, v___y_1010_);
return v___x_1024_;
}
else
{
lean_dec(v___y_1008_);
return v___x_1018_;
}
}
else
{
lean_dec(v___x_1015_);
lean_dec(v_stx_853_);
v___y_997_ = v___y_1007_;
v___y_998_ = v___y_1008_;
v___y_999_ = v___y_1009_;
v___y_1000_ = v___y_1010_;
goto v___jp_996_;
}
}
v___jp_1025_:
{
lean_object* v___x_1029_; lean_object* v_env_1030_; uint8_t v___x_1031_; uint8_t v___x_1032_; 
v___x_1029_ = lean_st_ref_get(v___y_1028_);
v_env_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_ref_n(v_env_1030_, 2);
lean_dec(v___x_1029_);
v___x_1031_ = 1;
lean_inc(v_optName_1026_);
v___x_1032_ = l_Lean_Environment_contains(v_env_1030_, v_optName_1026_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
lean_dec_ref(v_env_1030_);
lean_dec(v_stx_853_);
lean_dec(v_decl_852_);
lean_dec(v___x_850_);
lean_dec(v___x_849_);
lean_dec(v___x_848_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v___x_846_);
lean_dec_ref(v___x_845_);
lean_dec(v___x_844_);
v___x_1033_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1034_ = l_Lean_MessageData_ofName(v_optName_1026_);
lean_inc_ref(v___x_1034_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___x_1034_);
v___x_1039_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1040_, v___y_1027_, v___y_1028_);
return v___x_1041_;
}
else
{
v___y_1007_ = v_env_1030_;
v___y_1008_ = v_optName_1026_;
v___y_1009_ = v___y_1027_;
v___y_1010_ = v___y_1028_;
goto v___jp_1006_;
}
}
v___jp_1042_:
{
lean_object* v___x_1043_; uint8_t v___x_1044_; 
lean_inc_ref(v___x_847_);
lean_inc_ref(v___x_846_);
lean_inc_ref(v___x_845_);
v___x_1043_ = l_Lean_Name_mkStr4(v___x_845_, v___x_846_, v___x_847_, v___x_851_);
lean_inc(v_stx_853_);
v___x_1044_ = l_Lean_Syntax_isOfKind(v_stx_853_, v___x_1043_);
lean_dec(v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec(v_stx_853_);
lean_dec(v_decl_852_);
lean_dec(v___x_850_);
lean_dec(v___x_849_);
lean_dec(v___x_848_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v___x_846_);
lean_dec_ref(v___x_845_);
lean_dec(v___x_844_);
v___x_1045_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1046_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1045_, v___y_855_, v___y_856_);
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
else
{
lean_object* v___x_1055_; lean_object* v_id_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1055_ = lean_unsigned_to_nat(1u);
v_id_1056_ = l_Lean_Syntax_getArg(v_stx_853_, v___x_1055_);
v___x_1057_ = ((lean_object*)(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7));
lean_inc(v_id_1056_);
v___x_1058_ = l_Lean_Syntax_isOfKind(v_id_1056_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec(v_id_1056_);
lean_dec(v_stx_853_);
lean_dec(v_decl_852_);
lean_dec(v___x_850_);
lean_dec(v___x_849_);
lean_dec(v___x_848_);
lean_dec_ref(v___x_847_);
lean_dec_ref(v___x_846_);
lean_dec_ref(v___x_845_);
lean_dec(v___x_844_);
v___x_1059_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1060_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1059_, v___y_855_, v___y_856_);
v_a_1061_ = lean_ctor_get(v___x_1060_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1060_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1060_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1060_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_TSyntax_getId(v_id_1056_);
lean_dec(v_id_1056_);
v_optName_1026_ = v___x_1069_;
v___y_1027_ = v___y_855_;
v___y_1028_ = v___y_856_;
goto v___jp_1025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v___x_1076_, lean_object* v___x_1077_, lean_object* v___x_1078_, lean_object* v___x_1079_, lean_object* v___x_1080_, lean_object* v___x_1081_, lean_object* v_decl_1082_, lean_object* v_stx_1083_, lean_object* v_kind_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_){
_start:
{
uint8_t v_kind_boxed_1088_; lean_object* v_res_1089_; 
v_kind_boxed_1088_ = lean_unbox(v_kind_1084_);
v_res_1089_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(v___x_1074_, v___x_1075_, v___x_1076_, v___x_1077_, v___x_1078_, v___x_1079_, v___x_1080_, v___x_1081_, v_decl_1082_, v_stx_1083_, v_kind_boxed_1088_, v___y_1085_, v___y_1086_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
return v_res_1089_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1092_ = l_Lean_stringToMessageData(v___x_1091_);
return v___x_1092_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1095_ = l_Lean_stringToMessageData(v___x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object* v___x_1096_, lean_object* v_decl_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1101_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1102_ = l_Lean_MessageData_ofName(v___x_1096_);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1105_, v___y_1098_, v___y_1099_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object* v___x_1107_, lean_object* v_decl_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(v___x_1107_, v_decl_1108_, v___y_1109_, v___y_1110_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v_decl_1108_);
return v_res_1112_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_unsigned_to_nat(3183030336u);
v___x_1163_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1164_ = l_Lean_Name_num___override(v___x_1163_, v___x_1162_);
return v___x_1164_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1167_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1168_ = l_Lean_Name_str___override(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1171_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1172_ = l_Lean_Name_str___override(v___x_1171_, v___x_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_unsigned_to_nat(2u);
v___x_1174_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1175_ = l_Lean_Name_num___override(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1189_ = 0;
v___x_1190_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1191_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1192_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1193_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
lean_ctor_set(v___x_1193_, 1, v___x_1191_);
lean_ctor_set(v___x_1193_, 2, v___x_1190_);
lean_ctor_set_uint8(v___x_1193_, sizeof(void*)*3, v___x_1189_);
return v___x_1193_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1194_; lean_object* v___f_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___f_1194_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___f_1195_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1196_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v___f_1195_);
lean_ctor_set(v___x_1197_, 2, v___f_1194_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1200_ = l_Lean_registerBuiltinAttribute(v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_();
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
return v___x_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1___redArg(){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v___dummy_1207_){
_start:
{
lean_object* v_res_1208_; 
v_res_1208_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1___redArg();
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b1_1211_, lean_object* v_constName_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_1212_, v___y_1213_, v___y_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1217_, lean_object* v_constName_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1217_, v_constName_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9(lean_object* v_t_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9___redArg(v_t_1223_, v___y_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9___boxed(lean_object* v_t_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__2_spec__5_spec__9(v_t_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1233_, lean_object* v_ref_1234_, lean_object* v_constName_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_1234_, v_constName_1235_, v___y_1236_, v___y_1237_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1240_, lean_object* v_ref_1241_, lean_object* v_constName_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b1_1240_, v_ref_1241_, v_constName_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v_ref_1241_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b1_1247_, lean_object* v_ref_1248_, lean_object* v_msg_1249_, lean_object* v_declHint_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1248_, v_msg_1249_, v_declHint_1250_, v___y_1251_, v___y_1252_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b1_1255_, lean_object* v_ref_1256_, lean_object* v_msg_1257_, lean_object* v_declHint_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5(v_00_u03b1_1255_, v_ref_1256_, v_msg_1257_, v_declHint_1258_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v_ref_1256_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12(lean_object* v_msg_1263_, lean_object* v_declHint_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___redArg(v_msg_1263_, v_declHint_1264_, v___y_1266_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12___boxed(lean_object* v_msg_1269_, lean_object* v_declHint_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__9_spec__12(v_msg_1269_, v_declHint_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10(lean_object* v_00_u03b1_1275_, lean_object* v_ref_1276_, lean_object* v_msg_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10___redArg(v_ref_1276_, v_msg_1277_, v___y_1278_, v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_ref_1283_, lean_object* v_msg_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__5_spec__10(v_00_u03b1_1282_, v_ref_1283_, v_msg_1284_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v_ref_1283_);
return v_res_1288_;
}
}
lean_object* runtime_initialize_Lean_Elab_InfoTree_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_AutoDecl(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
