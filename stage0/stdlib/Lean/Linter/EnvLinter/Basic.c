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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadEIO___redArg();
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__21;
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
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` must have type `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "`, got `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = " but is only marked `meta`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "invalid attribute `builtin_env_linter`, declaration `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "` must be marked as `public` and `meta`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = " but is only marked `public`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "invalid attribute `builtin_env_linter`, linter `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 60, .m_capacity = 60, .m_length = 59, .m_data = "invalid attribute `builtin_env_linter`, no constant named `"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "`; did you forget `register_builtin_option "};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = " : Bool := ...`\?"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "invalid `builtin_env_linter` syntax: expected an option name argument"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "invalid attribute `builtin_env_linter`, must be global"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_;
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
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_le(v___x_321_, v___x_321_);
if (v___x_323_ == 0)
{
if (v___x_322_ == 0)
{
v___y_314_ = v_b_312_;
goto v___jp_313_;
}
else
{
size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v___x_324_ = ((size_t)0ULL);
v___x_325_ = lean_usize_of_nat(v___x_321_);
v___x_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0(v___x_319_, v___x_324_, v___x_325_, v_b_312_);
v___y_314_ = v___x_326_;
goto v___jp_313_;
}
}
else
{
size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; 
v___x_327_ = ((size_t)0ULL);
v___x_328_ = lean_usize_of_nat(v___x_321_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__0(v___x_319_, v___x_327_, v___x_328_, v_b_312_);
v___y_314_ = v___x_329_;
goto v___jp_313_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1___boxed(lean_object* v_as_330_, lean_object* v_i_331_, lean_object* v_stop_332_, lean_object* v_b_333_){
_start:
{
size_t v_i_boxed_334_; size_t v_stop_boxed_335_; lean_object* v_res_336_; 
v_i_boxed_334_ = lean_unbox_usize(v_i_331_);
lean_dec(v_i_331_);
v_stop_boxed_335_ = lean_unbox_usize(v_stop_332_);
lean_dec(v_stop_332_);
v_res_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(v_as_330_, v_i_boxed_334_, v_stop_boxed_335_, v_b_333_);
lean_dec_ref(v_as_330_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object* v_nss_337_){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_338_ = lean_box(1);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_array_get_size(v_nss_337_);
v___x_341_ = lean_nat_dec_lt(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
return v___x_338_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = lean_nat_dec_le(v___x_340_, v___x_340_);
if (v___x_342_ == 0)
{
if (v___x_341_ == 0)
{
return v___x_338_;
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_340_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(v_nss_337_, v___x_343_, v___x_344_, v___x_338_);
return v___x_345_;
}
}
else
{
size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((size_t)0ULL);
v___x_347_ = lean_usize_of_nat(v___x_340_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2__spec__1(v_nss_337_, v___x_346_, v___x_347_, v___x_338_);
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2____boxed(lean_object* v_nss_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(v_nss_349_);
lean_dec_ref(v_nss_349_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(lean_object* v_es_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_array_mk(v_es_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_));
v___x_372_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2____boxed(lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_487034324____hygCtx___hyg_2_();
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object* v___x_402_, lean_object* v___x_403_, lean_object* v_s_404_){
_start:
{
lean_object* v_addEntryFn_405_; lean_object* v_importedEntries_406_; lean_object* v_state_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_415_; 
v_addEntryFn_405_ = lean_ctor_get(v___x_402_, 3);
lean_inc(v_addEntryFn_405_);
lean_dec_ref(v___x_402_);
v_importedEntries_406_ = lean_ctor_get(v_s_404_, 0);
v_state_407_ = lean_ctor_get(v_s_404_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_s_404_);
if (v_isSharedCheck_415_ == 0)
{
v___x_409_ = v_s_404_;
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_state_407_);
lean_inc(v_importedEntries_406_);
lean_dec(v_s_404_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_415_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_state_411_; lean_object* v___x_413_; 
v_state_411_ = lean_apply_2(v_addEntryFn_405_, v_state_407_, v___x_403_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v_state_411_);
v___x_413_ = v___x_409_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_importedEntries_406_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_state_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_ref_416_, lean_object* v_msg_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_toCold_421_; lean_object* v_currRecDepth_422_; lean_object* v_ref_423_; uint16_t v_optionFlags_424_; uint8_t v_suppressElabErrors_425_; uint8_t v_isRecordingDeps_426_; lean_object* v_ref_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_toCold_421_ = lean_ctor_get(v___y_418_, 0);
v_currRecDepth_422_ = lean_ctor_get(v___y_418_, 1);
v_ref_423_ = lean_ctor_get(v___y_418_, 2);
v_optionFlags_424_ = lean_ctor_get_uint16(v___y_418_, sizeof(void*)*3);
v_suppressElabErrors_425_ = lean_ctor_get_uint8(v___y_418_, sizeof(void*)*3 + 2);
v_isRecordingDeps_426_ = lean_ctor_get_uint8(v___y_418_, sizeof(void*)*3 + 3);
v_ref_427_ = l_Lean_replaceRef(v_ref_416_, v_ref_423_);
lean_inc(v_currRecDepth_422_);
lean_inc_ref(v_toCold_421_);
v___x_428_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_428_, 0, v_toCold_421_);
lean_ctor_set(v___x_428_, 1, v_currRecDepth_422_);
lean_ctor_set(v___x_428_, 2, v_ref_427_);
lean_ctor_set_uint16(v___x_428_, sizeof(void*)*3, v_optionFlags_424_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*3 + 2, v_suppressElabErrors_425_);
lean_ctor_set_uint8(v___x_428_, sizeof(void*)*3 + 3, v_isRecordingDeps_426_);
v___x_429_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v_msg_417_, v___x_428_, v___y_419_);
lean_dec_ref_known(v___x_428_, 3);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_ref_430_, lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_430_, v_msg_431_, v___y_432_, v___y_433_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
lean_dec(v_ref_430_);
return v_res_435_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__0));
v___x_438_ = l_Lean_stringToMessageData(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__2));
v___x_441_ = l_Lean_stringToMessageData(v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__4));
v___x_444_ = l_Lean_stringToMessageData(v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_446_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__6));
v___x_447_ = l_Lean_stringToMessageData(v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__8));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__10));
v___x_453_ = l_Lean_stringToMessageData(v___x_452_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__12));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_458_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__14));
v___x_459_ = l_Lean_stringToMessageData(v___x_458_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__16));
v___x_462_ = l_Lean_stringToMessageData(v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_464_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__18));
v___x_465_ = l_Lean_stringToMessageData(v___x_464_);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__21(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__20));
v___x_468_ = l_Lean_stringToMessageData(v___x_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(lean_object* v_msg_469_, lean_object* v_declHint_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_env_475_; uint8_t v___x_476_; 
v___x_473_ = lean_box(0);
v___x_474_ = lean_st_ref_get(v___y_471_);
v_env_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc_ref(v_env_475_);
lean_dec(v___x_474_);
v___x_476_ = l_Lean_Name_isAnonymous(v_declHint_470_);
if (v___x_476_ == 0)
{
uint8_t v_isExporting_477_; 
v_isExporting_477_ = lean_ctor_get_uint8(v_env_475_, sizeof(void*)*13);
if (v_isExporting_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec_ref(v_env_475_);
lean_dec(v_declHint_470_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v_msg_469_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; uint8_t v___x_480_; 
lean_inc_ref(v_env_475_);
v___x_479_ = l_Lean_Environment_setExporting(v_env_475_, v___x_476_);
lean_inc(v_declHint_470_);
lean_inc_ref(v___x_479_);
v___x_480_ = l_Lean_Environment_contains(v___x_479_, v_declHint_470_, v_isExporting_477_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; 
lean_dec_ref(v___x_479_);
lean_dec_ref(v_env_475_);
lean_dec(v_declHint_470_);
v___x_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_481_, 0, v_msg_469_);
return v___x_481_;
}
else
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v_c_487_; lean_object* v___x_488_; 
v___x_482_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__2);
v___x_483_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__5);
v___x_484_ = l_Lean_Options_empty;
v___x_485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_485_, 0, v___x_479_);
lean_ctor_set(v___x_485_, 1, v___x_482_);
lean_ctor_set(v___x_485_, 2, v___x_483_);
lean_ctor_set(v___x_485_, 3, v___x_484_);
lean_inc(v_declHint_470_);
v___x_486_ = l_Lean_MessageData_ofConstName(v_declHint_470_, v___x_476_);
v_c_487_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_487_, 0, v___x_485_);
lean_ctor_set(v_c_487_, 1, v___x_486_);
v___x_488_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_475_, v_declHint_470_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec_ref(v_env_475_);
lean_dec(v_declHint_470_);
v___x_489_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_c_487_);
v___x_491_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__3);
v___x_492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_490_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = l_Lean_MessageData_note(v___x_492_);
v___x_494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_494_, 0, v_msg_469_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
else
{
lean_object* v_val_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_552_; 
v_val_496_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_552_ == 0)
{
v___x_498_ = v___x_488_;
v_isShared_499_ = v_isSharedCheck_552_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_val_496_);
lean_dec(v___x_488_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_552_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v___x_500_; lean_object* v_modules_501_; lean_object* v_moduleNames_502_; lean_object* v_mod_503_; uint8_t v___y_505_; uint8_t v___x_535_; 
v___x_500_ = l_Lean_Environment_header(v_env_475_);
lean_dec_ref(v_env_475_);
v_modules_501_ = lean_ctor_get(v___x_500_, 3);
lean_inc_ref(v_modules_501_);
v_moduleNames_502_ = lean_ctor_get(v___x_500_, 4);
lean_inc_ref(v_moduleNames_502_);
lean_dec_ref(v___x_500_);
v_mod_503_ = lean_array_get(v___x_473_, v_moduleNames_502_, v_val_496_);
lean_dec_ref(v_moduleNames_502_);
v___x_535_ = l_Lean_isPrivateName(v_declHint_470_);
lean_dec(v_declHint_470_);
if (v___x_535_ == 0)
{
lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_536_ = lean_array_get_size(v_modules_501_);
v___x_537_ = lean_nat_dec_lt(v_val_496_, v___x_536_);
if (v___x_537_ == 0)
{
lean_dec_ref(v_modules_501_);
lean_dec(v_val_496_);
v___y_505_ = v___x_535_;
goto v___jp_504_;
}
else
{
lean_object* v___x_538_; lean_object* v_toImport_539_; uint8_t v_isExported_540_; 
v___x_538_ = lean_array_fget(v_modules_501_, v_val_496_);
lean_dec(v_val_496_);
lean_dec_ref(v_modules_501_);
v_toImport_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc_ref(v_toImport_539_);
lean_dec(v___x_538_);
v_isExported_540_ = lean_ctor_get_uint8(v_toImport_539_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_539_);
v___y_505_ = v_isExported_540_;
goto v___jp_504_;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec_ref(v_modules_501_);
lean_del_object(v___x_498_);
lean_dec(v_val_496_);
v___x_541_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__1);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
lean_ctor_set(v___x_542_, 1, v_c_487_);
v___x_543_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__19);
v___x_544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_542_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
v___x_545_ = l_Lean_MessageData_ofName(v_mod_503_);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__21);
v___x_548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_546_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
v___x_549_ = l_Lean_MessageData_note(v___x_548_);
v___x_550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_550_, 0, v_msg_469_);
lean_ctor_set(v___x_550_, 1, v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
v___jp_504_:
{
if (v___y_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_506_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__5);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_c_487_);
v___x_508_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__7);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_Lean_MessageData_ofName(v_mod_503_);
v___x_511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_509_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v___x_512_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__9);
v___x_513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_511_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = l_Lean_MessageData_note(v___x_513_);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v_msg_469_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 0);
lean_ctor_set(v___x_498_, 0, v___x_515_);
v___x_517_ = v___x_498_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_519_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__11);
v___x_520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
lean_ctor_set(v___x_520_, 1, v_c_487_);
v___x_521_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__13);
v___x_522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
v___x_523_ = l_Lean_MessageData_ofName(v_mod_503_);
lean_inc_ref(v___x_523_);
v___x_524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__15);
v___x_526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_524_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_523_);
v___x_528_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___closed__17);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_MessageData_note(v___x_529_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v_msg_469_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 0);
lean_ctor_set(v___x_498_, 0, v___x_531_);
v___x_533_ = v___x_498_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
return v___x_533_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_553_; 
lean_dec_ref(v_env_475_);
lean_dec(v_declHint_470_);
v___x_553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_553_, 0, v_msg_469_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg___boxed(lean_object* v_msg_554_, lean_object* v_declHint_555_, lean_object* v___y_556_, lean_object* v___y_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_554_, v_declHint_555_, v___y_556_);
lean_dec(v___y_556_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_msg_559_, lean_object* v_declHint_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_574_; 
v___x_564_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_559_, v_declHint_560_, v___y_562_);
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_574_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_574_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_574_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
v___x_569_ = l_Lean_unknownIdentifierMessageTag;
v___x_570_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
lean_ctor_set(v___x_570_, 1, v_a_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_570_);
v___x_572_ = v___x_567_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_570_);
v___x_572_ = v_reuseFailAlloc_573_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
return v___x_572_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_msg_575_, lean_object* v_declHint_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(v_msg_575_, v_declHint_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_581_, lean_object* v_msg_582_, lean_object* v_declHint_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v___x_587_; lean_object* v_a_588_; lean_object* v___x_589_; 
v___x_587_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7(v_msg_582_, v_declHint_583_, v___y_584_, v___y_585_);
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref(v___x_587_);
v___x_589_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_581_, v_a_588_, v___y_584_, v___y_585_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_590_, lean_object* v_msg_591_, lean_object* v_declHint_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_590_, v_msg_591_, v_declHint_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
lean_dec(v_ref_590_);
return v_res_596_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0));
v___x_599_ = l_Lean_stringToMessageData(v___x_598_);
return v___x_599_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2));
v___x_602_ = l_Lean_stringToMessageData(v___x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_ref_603_, lean_object* v_constName_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v___x_608_; uint8_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_608_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
v___x_609_ = 0;
lean_inc(v_constName_604_);
v___x_610_ = l_Lean_MessageData_ofConstName(v_constName_604_, v___x_609_);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_608_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_603_, v___x_613_, v_constName_604_, v___y_605_, v___y_606_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_615_, lean_object* v_constName_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_615_, v_constName_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v_ref_615_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_constName_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_ref_625_; lean_object* v___x_626_; 
v_ref_625_ = lean_ctor_get(v___y_622_, 2);
v___x_626_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_625_, v_constName_621_, v___y_622_, v___y_623_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_constName_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0(lean_object* v_constName_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v___x_636_; lean_object* v_env_637_; uint8_t v___x_638_; lean_object* v___x_639_; 
v___x_636_ = lean_st_ref_get(v___y_634_);
v_env_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc_ref(v_env_637_);
lean_dec(v___x_636_);
v___x_638_ = 0;
lean_inc(v_constName_632_);
v___x_639_ = l_Lean_Environment_find_x3f(v_env_637_, v_constName_632_, v___x_638_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_632_, v___y_633_, v___y_634_);
return v___x_640_;
}
else
{
lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_648_; 
lean_dec(v_constName_632_);
v_val_641_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_648_ == 0)
{
v___x_643_ = v___x_639_;
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v___x_639_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_648_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_646_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set_tag(v___x_643_, 0);
v___x_646_ = v___x_643_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_val_641_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0___boxed(lean_object* v_constName_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0(v_constName_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__5(lean_object* v_a_654_, lean_object* v_a_655_){
_start:
{
if (lean_obj_tag(v_a_654_) == 0)
{
lean_object* v___x_656_; 
v___x_656_ = l_List_reverse___redArg(v_a_655_);
return v___x_656_;
}
else
{
lean_object* v_head_657_; lean_object* v_tail_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_667_; 
v_head_657_ = lean_ctor_get(v_a_654_, 0);
v_tail_658_ = lean_ctor_get(v_a_654_, 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v_a_654_);
if (v_isSharedCheck_667_ == 0)
{
v___x_660_ = v_a_654_;
v_isShared_661_ = v_isSharedCheck_667_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_tail_658_);
lean_inc(v_head_657_);
lean_dec(v_a_654_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_667_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = l_Lean_mkLevelParam(v_head_657_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 1, v_a_655_);
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v_a_655_);
v___x_664_ = v_reuseFailAlloc_666_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
v_a_654_ = v_tail_658_;
v_a_655_ = v___x_664_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__4(lean_object* v_constName_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; lean_object* v_env_673_; uint8_t v___x_674_; lean_object* v___x_675_; 
v___x_672_ = lean_st_ref_get(v___y_670_);
v_env_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc_ref(v_env_673_);
lean_dec(v___x_672_);
v___x_674_ = 0;
lean_inc(v_constName_668_);
v___x_675_ = l_Lean_Environment_findConstVal_x3f(v_env_673_, v_constName_668_, v___x_674_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_668_, v___y_669_, v___y_670_);
return v___x_676_;
}
else
{
lean_object* v_val_677_; lean_object* v___x_679_; uint8_t v_isShared_680_; uint8_t v_isSharedCheck_684_; 
lean_dec(v_constName_668_);
v_val_677_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_684_ == 0)
{
v___x_679_ = v___x_675_;
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
else
{
lean_inc(v_val_677_);
lean_dec(v___x_675_);
v___x_679_ = lean_box(0);
v_isShared_680_ = v_isSharedCheck_684_;
goto v_resetjp_678_;
}
v_resetjp_678_:
{
lean_object* v___x_682_; 
if (v_isShared_680_ == 0)
{
lean_ctor_set_tag(v___x_679_, 0);
v___x_682_ = v___x_679_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_val_677_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(lean_object* v_constName_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_constName_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_constName_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; 
lean_inc(v_constName_690_);
v___x_694_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_constName_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_706_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_706_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_706_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_706_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_levelParams_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; 
v_levelParams_699_ = lean_ctor_get(v_a_695_, 1);
lean_inc(v_levelParams_699_);
lean_dec(v_a_695_);
v___x_700_ = lean_box(0);
v___x_701_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2_spec__5(v_levelParams_699_, v___x_700_);
v___x_702_ = l_Lean_mkConst(v_constName_690_, v___x_701_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_702_);
v___x_704_ = v___x_697_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v_constName_690_);
v_a_707_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_694_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_694_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_constName_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2(v_constName_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(lean_object* v_t_720_, lean_object* v___y_721_){
_start:
{
lean_object* v___x_723_; lean_object* v_infoState_724_; uint8_t v_enabled_725_; 
v___x_723_ = lean_st_ref_get(v___y_721_);
v_infoState_724_ = lean_ctor_get(v___x_723_, 8);
lean_inc_ref(v_infoState_724_);
lean_dec(v___x_723_);
v_enabled_725_ = lean_ctor_get_uint8(v_infoState_724_, sizeof(void*)*3);
lean_dec_ref(v_infoState_724_);
if (v_enabled_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec_ref(v_t_720_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; lean_object* v_infoState_729_; lean_object* v_env_730_; lean_object* v_nextMacroScope_731_; lean_object* v_ngen_732_; lean_object* v_auxDeclNGen_733_; lean_object* v_traceState_734_; lean_object* v_cache_735_; lean_object* v_recordedDeps_736_; lean_object* v_messages_737_; lean_object* v_snapshotTasks_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_760_; 
v___x_728_ = lean_st_ref_take(v___y_721_);
v_infoState_729_ = lean_ctor_get(v___x_728_, 8);
v_env_730_ = lean_ctor_get(v___x_728_, 0);
v_nextMacroScope_731_ = lean_ctor_get(v___x_728_, 1);
v_ngen_732_ = lean_ctor_get(v___x_728_, 2);
v_auxDeclNGen_733_ = lean_ctor_get(v___x_728_, 3);
v_traceState_734_ = lean_ctor_get(v___x_728_, 4);
v_cache_735_ = lean_ctor_get(v___x_728_, 5);
v_recordedDeps_736_ = lean_ctor_get(v___x_728_, 6);
v_messages_737_ = lean_ctor_get(v___x_728_, 7);
v_snapshotTasks_738_ = lean_ctor_get(v___x_728_, 9);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_760_ == 0)
{
v___x_740_ = v___x_728_;
v_isShared_741_ = v_isSharedCheck_760_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_snapshotTasks_738_);
lean_inc(v_infoState_729_);
lean_inc(v_messages_737_);
lean_inc(v_recordedDeps_736_);
lean_inc(v_cache_735_);
lean_inc(v_traceState_734_);
lean_inc(v_auxDeclNGen_733_);
lean_inc(v_ngen_732_);
lean_inc(v_nextMacroScope_731_);
lean_inc(v_env_730_);
lean_dec(v___x_728_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_760_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
uint8_t v_enabled_742_; lean_object* v_assignment_743_; lean_object* v_lazyAssignment_744_; lean_object* v_trees_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_759_; 
v_enabled_742_ = lean_ctor_get_uint8(v_infoState_729_, sizeof(void*)*3);
v_assignment_743_ = lean_ctor_get(v_infoState_729_, 0);
v_lazyAssignment_744_ = lean_ctor_get(v_infoState_729_, 1);
v_trees_745_ = lean_ctor_get(v_infoState_729_, 2);
v_isSharedCheck_759_ = !lean_is_exclusive(v_infoState_729_);
if (v_isSharedCheck_759_ == 0)
{
v___x_747_ = v_infoState_729_;
v_isShared_748_ = v_isSharedCheck_759_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_trees_745_);
lean_inc(v_lazyAssignment_744_);
lean_inc(v_assignment_743_);
lean_dec(v_infoState_729_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_759_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_749_ = lean_box(0);
v___x_750_ = l_Lean_PersistentArray_push___redArg(v_trees_745_, v_t_720_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 2, v___x_750_);
v___x_752_ = v___x_747_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_assignment_743_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_lazyAssignment_744_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v___x_750_);
lean_ctor_set_uint8(v_reuseFailAlloc_758_, sizeof(void*)*3, v_enabled_742_);
v___x_752_ = v_reuseFailAlloc_758_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_754_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 8, v___x_752_);
v___x_754_ = v___x_740_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_env_730_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_nextMacroScope_731_);
lean_ctor_set(v_reuseFailAlloc_757_, 2, v_ngen_732_);
lean_ctor_set(v_reuseFailAlloc_757_, 3, v_auxDeclNGen_733_);
lean_ctor_set(v_reuseFailAlloc_757_, 4, v_traceState_734_);
lean_ctor_set(v_reuseFailAlloc_757_, 5, v_cache_735_);
lean_ctor_set(v_reuseFailAlloc_757_, 6, v_recordedDeps_736_);
lean_ctor_set(v_reuseFailAlloc_757_, 7, v_messages_737_);
lean_ctor_set(v_reuseFailAlloc_757_, 8, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_757_, 9, v_snapshotTasks_738_);
v___x_754_ = v_reuseFailAlloc_757_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_st_ref_put(v___y_721_, v___x_754_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_749_);
return v___x_756_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_t_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_t_761_, v___y_762_);
lean_dec(v___y_762_);
return v_res_764_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_765_ = lean_unsigned_to_nat(32u);
v___x_766_ = lean_mk_empty_array_with_capacity(v___x_765_);
v___x_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_767_, 0, v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__1(void){
_start:
{
size_t v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_768_ = ((size_t)5ULL);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_unsigned_to_nat(32u);
v___x_771_ = lean_mk_empty_array_with_capacity(v___x_770_);
v___x_772_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__0);
v___x_773_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v___x_771_);
lean_ctor_set(v___x_773_, 2, v___x_769_);
lean_ctor_set(v___x_773_, 3, v___x_769_);
lean_ctor_set_usize(v___x_773_, 4, v___x_768_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3(lean_object* v_t_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; lean_object* v_infoState_779_; uint8_t v_enabled_780_; 
v___x_778_ = lean_st_ref_get(v___y_776_);
v_infoState_779_ = lean_ctor_get(v___x_778_, 8);
lean_inc_ref(v_infoState_779_);
lean_dec(v___x_778_);
v_enabled_780_ = lean_ctor_get_uint8(v_infoState_779_, sizeof(void*)*3);
lean_dec_ref(v_infoState_779_);
if (v_enabled_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref(v_t_774_);
v___x_781_ = lean_box(0);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_783_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___closed__1);
v___x_784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_784_, 0, v_t_774_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v___x_784_, v___y_776_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3___boxed(lean_object* v_t_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3(v_t_786_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1(lean_object* v_stx_791_, lean_object* v_n_792_, lean_object* v_expectedType_x3f_793_, lean_object* v___y_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__2(v_n_792_, v___y_794_, v___y_795_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref_known(v___x_797_, 1);
v___x_799_ = lean_box(0);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v_stx_791_);
v___x_801_ = l_Lean_LocalContext_empty;
v___x_802_ = 0;
v___x_803_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_803_, 0, v___x_800_);
lean_ctor_set(v___x_803_, 1, v___x_801_);
lean_ctor_set(v___x_803_, 2, v_expectedType_x3f_793_);
lean_ctor_set(v___x_803_, 3, v_a_798_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*4, v___x_802_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*4 + 1, v___x_802_);
v___x_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
v___x_805_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3(v___x_804_, v___y_794_, v___y_795_);
return v___x_805_;
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_expectedType_x3f_793_);
lean_dec(v_stx_791_);
v_a_806_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_797_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_797_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1___boxed(lean_object* v_stx_814_, lean_object* v_n_815_, lean_object* v_expectedType_x3f_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1(v_stx_814_, v_n_815_, v_expectedType_x3f_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_820_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_827_ = l_Lean_stringToMessageData(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__4_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_830_ = l_Lean_stringToMessageData(v___x_829_);
return v___x_830_;
}
}
static uint64_t _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_837_; uint64_t v___x_838_; 
v___x_837_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_838_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_837_);
return v___x_838_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_839_ = lean_uint64_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__7_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_840_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__6_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_841_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_841_, 0, v___x_840_);
lean_ctor_set_uint64(v___x_841_, sizeof(void*)*1, v___x_839_);
return v___x_841_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__0);
v___x_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_845_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
lean_ctor_set(v___x_845_, 2, v___x_844_);
lean_ctor_set(v___x_845_, 3, v___x_844_);
lean_ctor_set(v___x_845_, 4, v___x_844_);
lean_ctor_set(v___x_845_, 5, v___x_844_);
return v___x_845_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
lean_ctor_set(v___x_847_, 2, v___x_846_);
lean_ctor_set(v___x_847_, 3, v___x_846_);
lean_ctor_set(v___x_847_, 4, v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_851_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__14_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
return v___x_852_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__16_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_855_ = l_Lean_stringToMessageData(v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_862_ = l_Lean_stringToMessageData(v___x_861_);
return v___x_862_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_864_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_865_ = l_Lean_stringToMessageData(v___x_864_);
return v___x_865_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_871_ = l_Lean_stringToMessageData(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__31_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object* v___x_878_, lean_object* v___x_879_, lean_object* v___x_880_, lean_object* v___x_881_, lean_object* v___x_882_, lean_object* v___x_883_, lean_object* v___x_884_, lean_object* v___x_885_, lean_object* v_decl_886_, lean_object* v_stx_887_, uint8_t v_kind_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v___y_893_; lean_object* v___y_894_; lean_object* v_nextMacroScope_895_; lean_object* v_ngen_896_; lean_object* v_auxDeclNGen_897_; lean_object* v_traceState_898_; lean_object* v_recordedDeps_899_; lean_object* v_messages_900_; lean_object* v_infoState_901_; lean_object* v_snapshotTasks_902_; lean_object* v___y_903_; lean_object* v___y_909_; lean_object* v___y_910_; lean_object* v___y_933_; uint8_t v___y_934_; lean_object* v___y_935_; lean_object* v___y_936_; lean_object* v___y_937_; lean_object* v___y_938_; uint8_t v_a_939_; lean_object* v___y_954_; lean_object* v___y_955_; lean_object* v___y_956_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1015_; lean_object* v___y_1016_; uint8_t v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1026_; lean_object* v___y_1027_; uint8_t v___y_1028_; uint8_t v___y_1029_; lean_object* v___y_1030_; uint8_t v___y_1031_; lean_object* v___y_1040_; lean_object* v___y_1041_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1050_; lean_object* v___y_1051_; lean_object* v___y_1052_; lean_object* v___y_1053_; lean_object* v_optName_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; uint8_t v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = 0;
v___x_1114_ = l_Lean_instBEqAttributeKind_beq(v_kind_888_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
lean_dec(v_stx_887_);
lean_dec(v_decl_886_);
lean_dec_ref(v___x_885_);
lean_dec(v___x_884_);
lean_dec(v___x_883_);
lean_dec(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v___x_879_);
lean_dec(v___x_878_);
v___x_1115_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__32_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1116_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1115_, v___y_889_, v___y_890_);
return v___x_1116_;
}
else
{
goto v___jp_1085_;
}
v___jp_892_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_904_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_905_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_905_, 0, v___y_903_);
lean_ctor_set(v___x_905_, 1, v_nextMacroScope_895_);
lean_ctor_set(v___x_905_, 2, v_ngen_896_);
lean_ctor_set(v___x_905_, 3, v_auxDeclNGen_897_);
lean_ctor_set(v___x_905_, 4, v_traceState_898_);
lean_ctor_set(v___x_905_, 5, v___x_904_);
lean_ctor_set(v___x_905_, 6, v_recordedDeps_899_);
lean_ctor_set(v___x_905_, 7, v_messages_900_);
lean_ctor_set(v___x_905_, 8, v_infoState_901_);
lean_ctor_set(v___x_905_, 9, v_snapshotTasks_902_);
v___x_906_ = lean_st_ref_put(v___y_894_, v___x_905_);
v___x_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_907_, 0, v___y_893_);
return v___x_907_;
}
v___jp_908_:
{
lean_object* v___x_911_; lean_object* v_env_912_; lean_object* v_nextMacroScope_913_; lean_object* v_ngen_914_; lean_object* v_auxDeclNGen_915_; lean_object* v_traceState_916_; lean_object* v_recordedDeps_917_; lean_object* v_messages_918_; lean_object* v_infoState_919_; lean_object* v_snapshotTasks_920_; lean_object* v___x_921_; lean_object* v_toEnvExtension_922_; lean_object* v_asyncMode_923_; uint8_t v_logWrites_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___f_927_; uint8_t v___x_928_; 
v___x_911_ = lean_st_ref_take(v___y_910_);
v_env_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_ref(v_env_912_);
v_nextMacroScope_913_ = lean_ctor_get(v___x_911_, 1);
lean_inc(v_nextMacroScope_913_);
v_ngen_914_ = lean_ctor_get(v___x_911_, 2);
lean_inc_ref(v_ngen_914_);
v_auxDeclNGen_915_ = lean_ctor_get(v___x_911_, 3);
lean_inc_ref(v_auxDeclNGen_915_);
v_traceState_916_ = lean_ctor_get(v___x_911_, 4);
lean_inc_ref(v_traceState_916_);
v_recordedDeps_917_ = lean_ctor_get(v___x_911_, 6);
lean_inc_ref(v_recordedDeps_917_);
v_messages_918_ = lean_ctor_get(v___x_911_, 7);
lean_inc_ref(v_messages_918_);
v_infoState_919_ = lean_ctor_get(v___x_911_, 8);
lean_inc_ref(v_infoState_919_);
v_snapshotTasks_920_ = lean_ctor_get(v___x_911_, 9);
lean_inc_ref(v_snapshotTasks_920_);
lean_dec(v___x_911_);
v___x_921_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_922_ = lean_ctor_get(v___x_921_, 0);
v_asyncMode_923_ = lean_ctor_get(v_toEnvExtension_922_, 2);
v_logWrites_924_ = lean_ctor_get_uint8(v_toEnvExtension_922_, sizeof(void*)*6);
v___x_925_ = lean_box(0);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___y_909_);
lean_ctor_set(v___x_926_, 1, v_decl_886_);
v___f_927_ = lean_alloc_closure((void*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_), 3, 2);
lean_closure_set(v___f_927_, 0, v___x_921_);
lean_closure_set(v___f_927_, 1, v___x_926_);
v___x_928_ = 1;
if (v_logWrites_924_ == 0)
{
lean_object* v___x_929_; 
lean_inc_ref(v_toEnvExtension_922_);
v___x_929_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_922_, v_env_912_, v___f_927_, v_asyncMode_923_, v___x_878_, v___x_928_);
v___y_893_ = v___x_925_;
v___y_894_ = v___y_910_;
v_nextMacroScope_895_ = v_nextMacroScope_913_;
v_ngen_896_ = v_ngen_914_;
v_auxDeclNGen_897_ = v_auxDeclNGen_915_;
v_traceState_898_ = v_traceState_916_;
v_recordedDeps_899_ = v_recordedDeps_917_;
v_messages_900_ = v_messages_918_;
v_infoState_901_ = v_infoState_919_;
v_snapshotTasks_902_ = v_snapshotTasks_920_;
v___y_903_ = v___x_929_;
goto v___jp_892_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; 
lean_inc_ref_n(v_toEnvExtension_922_, 2);
v___x_930_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_922_, v_env_912_);
lean_dec_ref(v_env_912_);
v___x_931_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_922_, v___x_930_, v___f_927_, v_asyncMode_923_, v___x_878_, v___x_928_);
v___y_893_ = v___x_925_;
v___y_894_ = v___y_910_;
v_nextMacroScope_895_ = v_nextMacroScope_913_;
v_ngen_896_ = v_ngen_914_;
v_auxDeclNGen_897_ = v_auxDeclNGen_915_;
v_traceState_898_ = v_traceState_916_;
v_recordedDeps_899_ = v_recordedDeps_917_;
v_messages_900_ = v_messages_918_;
v_infoState_901_ = v_infoState_919_;
v_snapshotTasks_902_ = v_snapshotTasks_920_;
v___y_903_ = v___x_931_;
goto v___jp_892_;
}
}
v___jp_932_:
{
if (v_a_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v___y_933_);
lean_dec(v___x_878_);
v___x_940_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
v___x_941_ = l_Lean_MessageData_ofConstName(v_decl_886_, v___y_934_);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l_Lean_MessageData_ofConstName(v___y_938_, v___y_934_);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_944_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__5_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_948_, 0, v___x_946_);
lean_ctor_set(v___x_948_, 1, v___x_947_);
v___x_949_ = l_Lean_MessageData_ofExpr(v___y_937_);
v___x_950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_948_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___x_940_);
v___x_952_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_951_, v___y_935_, v___y_936_);
return v___x_952_;
}
else
{
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
v___y_909_ = v___y_933_;
v___y_910_ = v___y_936_;
goto v___jp_908_;
}
}
v___jp_953_:
{
lean_object* v___x_957_; 
lean_inc(v_decl_886_);
v___x_957_ = l_Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0(v_decl_886_, v___y_955_, v___y_956_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; uint8_t v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; size_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = l_Lean_ConstantInfo_type(v_a_958_);
lean_dec(v_a_958_);
lean_inc_ref(v___x_881_);
v___x_960_ = l_Lean_Name_mkStr4(v___x_879_, v___x_880_, v___x_881_, v___x_881_);
v___x_961_ = lean_box(0);
lean_inc(v___x_960_);
v___x_962_ = l_Lean_mkConst(v___x_960_, v___x_961_);
v___x_963_ = 0;
v___x_964_ = 1;
v___x_965_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__8_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_966_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__9_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_967_ = lean_unsigned_to_nat(32u);
v___x_968_ = lean_mk_empty_array_with_capacity(v___x_967_);
v___x_969_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1_spec__3___closed__3);
v___x_970_ = ((size_t)5ULL);
lean_inc_n(v___x_882_, 6);
v___x_971_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_968_);
lean_ctor_set(v___x_971_, 2, v___x_882_);
lean_ctor_set(v___x_971_, 3, v___x_882_);
lean_ctor_set_usize(v___x_971_, 4, v___x_970_);
v___x_972_ = lean_box(1);
lean_inc_ref(v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_973_, 0, v___x_966_);
lean_ctor_set(v___x_973_, 1, v___x_971_);
lean_ctor_set(v___x_973_, 2, v___x_972_);
v___x_974_ = lean_mk_empty_array_with_capacity(v___x_882_);
v___x_975_ = lean_box(0);
lean_inc(v___x_883_);
v___x_976_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_976_, 0, v___x_965_);
lean_ctor_set(v___x_976_, 1, v___x_883_);
lean_ctor_set(v___x_976_, 2, v___x_973_);
lean_ctor_set(v___x_976_, 3, v___x_974_);
lean_ctor_set(v___x_976_, 4, v___x_975_);
lean_ctor_set(v___x_976_, 5, v___x_882_);
lean_ctor_set(v___x_976_, 6, v___x_975_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*7, v___x_963_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*7 + 1, v___x_963_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*7 + 2, v___x_963_);
lean_ctor_set_uint8(v___x_976_, sizeof(void*)*7 + 3, v___x_964_);
v___x_977_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_978_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_978_, 0, v___x_882_);
lean_ctor_set(v___x_978_, 1, v___x_882_);
lean_ctor_set(v___x_978_, 2, v___x_882_);
lean_ctor_set(v___x_978_, 3, v___x_882_);
lean_ctor_set(v___x_978_, 4, v___x_966_);
lean_ctor_set(v___x_978_, 5, v___x_966_);
lean_ctor_set(v___x_978_, 6, v___x_966_);
lean_ctor_set(v___x_978_, 7, v___x_966_);
lean_ctor_set(v___x_978_, 8, v___x_966_);
lean_ctor_set(v___x_978_, 9, v___x_966_);
lean_ctor_set(v___x_978_, 10, v___x_966_);
lean_ctor_set(v___x_978_, 11, v___x_977_);
v___x_979_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__10_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_980_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__11_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_981_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_981_, 0, v___x_978_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
lean_ctor_set(v___x_981_, 2, v___x_883_);
lean_ctor_set(v___x_981_, 3, v___x_971_);
lean_ctor_set(v___x_981_, 4, v___x_980_);
v___x_982_ = lean_st_mk_ref(v___x_981_);
lean_inc_ref(v___x_959_);
v___x_983_ = l_Lean_Meta_isExprDefEq(v___x_959_, v___x_962_, v___x_976_, v___x_982_, v___y_955_, v___y_956_);
lean_dec_ref_known(v___x_976_, 7);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = lean_st_ref_get(v___x_982_);
lean_dec(v___x_982_);
lean_dec(v___x_985_);
v___x_986_ = lean_unbox(v_a_984_);
lean_dec(v_a_984_);
v___y_933_ = v___y_954_;
v___y_934_ = v___x_963_;
v___y_935_ = v___y_955_;
v___y_936_ = v___y_956_;
v___y_937_ = v___x_959_;
v___y_938_ = v___x_960_;
v_a_939_ = v___x_986_;
goto v___jp_932_;
}
else
{
lean_dec(v___x_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_987_; uint8_t v___x_988_; 
v_a_987_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_983_, 1);
v___x_988_ = lean_unbox(v_a_987_);
lean_dec(v_a_987_);
v___y_933_ = v___y_954_;
v___y_934_ = v___x_963_;
v___y_935_ = v___y_955_;
v___y_936_ = v___y_956_;
v___y_937_ = v___x_959_;
v___y_938_ = v___x_960_;
v_a_939_ = v___x_988_;
goto v___jp_932_;
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec(v___x_960_);
lean_dec_ref(v___x_959_);
lean_dec(v___y_954_);
lean_dec(v_decl_886_);
lean_dec(v___x_878_);
v_a_989_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_983_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_983_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
else
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1004_; 
lean_dec(v___y_954_);
lean_dec(v_decl_886_);
lean_dec(v___x_883_);
lean_dec(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v___x_879_);
lean_dec(v___x_878_);
v_a_997_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_999_ = v___x_957_;
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_957_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1004_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v___x_1002_; 
if (v_isShared_1000_ == 0)
{
v___x_1002_ = v___x_999_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_a_997_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
v___jp_1005_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v___y_1006_);
lean_inc_ref(v___y_1010_);
v___x_1011_ = l_Lean_stringToMessageData(v___y_1010_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___y_1008_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1012_, v___y_1007_, v___y_1009_);
return v___x_1013_;
}
v___jp_1014_:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_inc_ref(v___y_1020_);
v___x_1021_ = l_Lean_stringToMessageData(v___y_1020_);
v___x_1022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1022_, 0, v___y_1019_);
lean_ctor_set(v___x_1022_, 1, v___x_1021_);
if (v___y_1017_ == 0)
{
lean_object* v___x_1023_; 
v___x_1023_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_1006_ = v___y_1015_;
v___y_1007_ = v___y_1016_;
v___y_1008_ = v___x_1022_;
v___y_1009_ = v___y_1018_;
v___y_1010_ = v___x_1023_;
goto v___jp_1005_;
}
else
{
lean_object* v___x_1024_; 
v___x_1024_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__13_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_1006_ = v___y_1015_;
v___y_1007_ = v___y_1016_;
v___y_1008_ = v___x_1022_;
v___y_1009_ = v___y_1018_;
v___y_1010_ = v___x_1024_;
goto v___jp_1005_;
}
}
v___jp_1025_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1032_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__15_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1033_ = l_Lean_MessageData_ofConstName(v_decl_886_, v___y_1031_);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__17_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
if (v___y_1029_ == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__12_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_1015_ = v___y_1026_;
v___y_1016_ = v___y_1027_;
v___y_1017_ = v___y_1028_;
v___y_1018_ = v___y_1030_;
v___y_1019_ = v___x_1036_;
v___y_1020_ = v___x_1037_;
goto v___jp_1014_;
}
else
{
lean_object* v___x_1038_; 
v___x_1038_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___y_1015_ = v___y_1026_;
v___y_1016_ = v___y_1027_;
v___y_1017_ = v___y_1028_;
v___y_1018_ = v___y_1030_;
v___y_1019_ = v___x_1036_;
v___y_1020_ = v___x_1038_;
goto v___jp_1014_;
}
}
v___jp_1039_:
{
uint8_t v___x_1044_; 
v___x_1044_ = l_Lean_isPrivateName(v_decl_886_);
if (v___x_1044_ == 0)
{
uint8_t v___x_1045_; 
lean_inc(v_decl_886_);
v___x_1045_ = l_Lean_isMarkedMeta(v___y_1041_, v_decl_886_);
if (v___x_1045_ == 0)
{
uint8_t v___x_1046_; 
lean_dec(v___x_883_);
lean_dec(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v___x_879_);
lean_dec(v___x_878_);
v___x_1046_ = 1;
v___y_1026_ = v___y_1040_;
v___y_1027_ = v___y_1042_;
v___y_1028_ = v___x_1045_;
v___y_1029_ = v___x_1046_;
v___y_1030_ = v___y_1043_;
v___y_1031_ = v___x_1045_;
goto v___jp_1025_;
}
else
{
v___y_954_ = v___y_1040_;
v___y_955_ = v___y_1042_;
v___y_956_ = v___y_1043_;
goto v___jp_953_;
}
}
else
{
uint8_t v___x_1047_; uint8_t v___x_1048_; 
lean_dec(v___x_883_);
lean_dec(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v___x_879_);
lean_dec(v___x_878_);
v___x_1047_ = 0;
lean_inc(v_decl_886_);
v___x_1048_ = l_Lean_isMarkedMeta(v___y_1041_, v_decl_886_);
v___y_1026_ = v___y_1040_;
v___y_1027_ = v___y_1042_;
v___y_1028_ = v___x_1048_;
v___y_1029_ = v___x_1047_;
v___y_1030_ = v___y_1043_;
v___y_1031_ = v___x_1047_;
goto v___jp_1025_;
}
}
v___jp_1049_:
{
lean_object* v___x_1054_; lean_object* v_toEnvExtension_1055_; lean_object* v_asyncMode_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1054_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_1055_ = lean_ctor_get(v___x_1054_, 0);
v_asyncMode_1056_ = lean_ctor_get(v_toEnvExtension_1055_, 2);
lean_inc(v___x_878_);
lean_inc_ref(v___y_1051_);
v___x_1057_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_884_, v___x_1054_, v___y_1051_, v_asyncMode_1056_, v___x_878_);
v___x_1058_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1057_, v___y_1050_);
lean_dec(v___x_1057_);
if (lean_obj_tag(v___x_1058_) == 1)
{
lean_object* v_val_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
lean_dec_ref(v___y_1051_);
lean_dec(v_decl_886_);
lean_dec(v___x_883_);
lean_dec(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v___x_879_);
lean_dec(v___x_878_);
v_val_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_val_1059_);
lean_dec_ref_known(v___x_1058_, 1);
v___x_1060_ = lean_box(0);
v___x_1061_ = l_Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1(v_stx_887_, v_val_1059_, v___x_1060_, v___y_1052_, v___y_1053_);
if (lean_obj_tag(v___x_1061_) == 0)
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec_ref_known(v___x_1061_, 1);
v___x_1062_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1063_ = l_Lean_MessageData_ofName(v___y_1050_);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1066_, v___y_1052_, v___y_1053_);
return v___x_1067_;
}
else
{
lean_dec(v___y_1050_);
return v___x_1061_;
}
}
else
{
lean_dec(v___x_1058_);
lean_dec(v_stx_887_);
v___y_1040_ = v___y_1050_;
v___y_1041_ = v___y_1051_;
v___y_1042_ = v___y_1052_;
v___y_1043_ = v___y_1053_;
goto v___jp_1039_;
}
}
v___jp_1068_:
{
lean_object* v___x_1072_; lean_object* v_env_1073_; uint8_t v___x_1074_; uint8_t v___x_1075_; 
v___x_1072_ = lean_st_ref_get(v___y_1071_);
v_env_1073_ = lean_ctor_get(v___x_1072_, 0);
lean_inc_ref_n(v_env_1073_, 2);
lean_dec(v___x_1072_);
v___x_1074_ = 1;
lean_inc(v_optName_1069_);
v___x_1075_ = l_Lean_Environment_contains(v_env_1073_, v_optName_1069_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref(v_env_1073_);
lean_dec(v_stx_887_);
lean_dec(v_decl_886_);
lean_dec(v___x_884_);
lean_dec(v___x_883_);
lean_dec(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v___x_879_);
lean_dec(v___x_878_);
v___x_1076_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1077_ = l_Lean_MessageData_ofName(v_optName_1069_);
lean_inc_ref(v___x_1077_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1076_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v___x_1077_);
v___x_1082_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1083_, v___y_1070_, v___y_1071_);
return v___x_1084_;
}
else
{
v___y_1050_ = v_optName_1069_;
v___y_1051_ = v_env_1073_;
v___y_1052_ = v___y_1070_;
v___y_1053_ = v___y_1071_;
goto v___jp_1049_;
}
}
v___jp_1085_:
{
lean_object* v___x_1086_; uint8_t v___x_1087_; 
lean_inc_ref(v___x_881_);
lean_inc_ref(v___x_880_);
lean_inc_ref(v___x_879_);
v___x_1086_ = l_Lean_Name_mkStr4(v___x_879_, v___x_880_, v___x_881_, v___x_885_);
lean_inc(v_stx_887_);
v___x_1087_ = l_Lean_Syntax_isOfKind(v_stx_887_, v___x_1086_);
lean_dec(v___x_1086_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_stx_887_);
lean_dec(v_decl_886_);
lean_dec(v___x_884_);
lean_dec(v___x_883_);
lean_dec(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v___x_879_);
lean_dec(v___x_878_);
v___x_1088_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1089_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1088_, v___y_889_, v___y_890_);
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
else
{
lean_object* v___x_1098_; lean_object* v_id_1099_; lean_object* v___x_1100_; uint8_t v___x_1101_; 
v___x_1098_ = lean_unsigned_to_nat(1u);
v_id_1099_ = l_Lean_Syntax_getArg(v_stx_887_, v___x_1098_);
v___x_1100_ = ((lean_object*)(l_Lean_Linter_EnvLinter_builtin__env__linter___closed__7));
lean_inc(v_id_1099_);
v___x_1101_ = l_Lean_Syntax_isOfKind(v_id_1099_, v___x_1100_);
if (v___x_1101_ == 0)
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v_id_1099_);
lean_dec(v_stx_887_);
lean_dec(v_decl_886_);
lean_dec(v___x_884_);
lean_dec(v___x_883_);
lean_dec(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v___x_879_);
lean_dec(v___x_878_);
v___x_1102_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1103_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1102_, v___y_889_, v___y_890_);
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_TSyntax_getId(v_id_1099_);
lean_dec(v_id_1099_);
v_optName_1069_ = v___x_1112_;
v___y_1070_ = v___y_889_;
v___y_1071_ = v___y_890_;
goto v___jp_1068_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object* v___x_1117_, lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v___x_1120_, lean_object* v___x_1121_, lean_object* v___x_1122_, lean_object* v___x_1123_, lean_object* v___x_1124_, lean_object* v_decl_1125_, lean_object* v_stx_1126_, lean_object* v_kind_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
uint8_t v_kind_boxed_1131_; lean_object* v_res_1132_; 
v_kind_boxed_1131_ = lean_unbox(v_kind_1127_);
v_res_1132_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(v___x_1117_, v___x_1118_, v___x_1119_, v___x_1120_, v___x_1121_, v___x_1122_, v___x_1123_, v___x_1124_, v_decl_1125_, v_stx_1126_, v_kind_boxed_1131_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
return v_res_1132_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__0_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1135_ = l_Lean_stringToMessageData(v___x_1134_);
return v___x_1135_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1137_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1138_ = l_Lean_stringToMessageData(v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(lean_object* v___x_1139_, lean_object* v_decl_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1144_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__1_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1145_ = l_Lean_MessageData_ofName(v___x_1139_);
v___x_1146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1144_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2___closed__3_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1146_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_throwError___at___00Lean_ofExcept___at___00Lean_evalConstCheck___at___00Lean_Linter_EnvLinter_getEnvLinter_spec__0_spec__0_spec__1___redArg(v___x_1148_, v___y_1141_, v___y_1142_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object* v___x_1150_, lean_object* v_decl_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(v___x_1150_, v_decl_1151_, v___y_1152_, v___y_1153_);
lean_dec(v___y_1153_);
lean_dec_ref(v___y_1152_);
lean_dec(v_decl_1151_);
return v_res_1155_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1205_ = lean_unsigned_to_nat(3183030336u);
v___x_1206_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__18_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1207_ = l_Lean_Name_num___override(v___x_1206_, v___x_1205_);
return v___x_1207_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__20_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1210_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__19_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1211_ = l_Lean_Name_str___override(v___x_1210_, v___x_1209_);
return v___x_1211_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1213_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__22_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1214_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__21_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1215_ = l_Lean_Name_str___override(v___x_1214_, v___x_1213_);
return v___x_1215_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___x_1216_ = lean_unsigned_to_nat(2u);
v___x_1217_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__23_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1218_ = l_Lean_Name_num___override(v___x_1217_, v___x_1216_);
return v___x_1218_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1232_ = 0;
v___x_1233_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__28_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1234_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__26_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1235_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__24_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1236_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1236_, 0, v___x_1235_);
lean_ctor_set(v___x_1236_, 1, v___x_1234_);
lean_ctor_set(v___x_1236_, 2, v___x_1233_);
lean_ctor_set_uint8(v___x_1236_, sizeof(void*)*3, v___x_1232_);
return v___x_1236_;
}
}
static lean_object* _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1237_; lean_object* v___f_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v___f_1237_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__27_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___f_1238_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__25_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_));
v___x_1239_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__29_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1240_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1239_);
lean_ctor_set(v___x_1240_, 1, v___f_1238_);
lean_ctor_set(v___x_1240_, 2, v___f_1237_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1242_ = lean_obj_once(&l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_, &l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn___closed__30_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_);
v___x_1243_ = l_Lean_registerBuiltinAttribute(v___x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2____boxed(lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l___private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2_();
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b1_1246_, lean_object* v_constName_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_1247_, v___y_1248_, v___y_1249_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b1_1252_, lean_object* v_constName_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1252_, v_constName_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7(lean_object* v_t_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___redArg(v_t_1258_, v___y_1260_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7___boxed(lean_object* v_t_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__1_spec__3_spec__7(v_t_1263_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1268_, lean_object* v_ref_1269_, lean_object* v_constName_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_1269_, v_constName_1270_, v___y_1271_, v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1275_, lean_object* v_ref_1276_, lean_object* v_constName_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b1_1275_, v_ref_1276_, v_constName_1277_, v___y_1278_, v___y_1279_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v_ref_1276_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_1282_, lean_object* v_ref_1283_, lean_object* v_msg_1284_, lean_object* v_declHint_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
lean_object* v___x_1289_; 
v___x_1289_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_ref_1283_, v_msg_1284_, v_declHint_1285_, v___y_1286_, v___y_1287_);
return v___x_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1290_, lean_object* v_ref_1291_, lean_object* v_msg_1292_, lean_object* v_declHint_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_1290_, v_ref_1291_, v_msg_1292_, v_declHint_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v_ref_1291_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10(lean_object* v_msg_1298_, lean_object* v_declHint_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___redArg(v_msg_1298_, v_declHint_1299_, v___y_1301_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10___boxed(lean_object* v_msg_1304_, lean_object* v_declHint_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__7_spec__10(v_msg_1304_, v_declHint_1305_, v___y_1306_, v___y_1307_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b1_1310_, lean_object* v_ref_1311_, lean_object* v_msg_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ref_1311_, v_msg_1312_, v___y_1313_, v___y_1314_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b1_1317_, lean_object* v_ref_1318_, lean_object* v_msg_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Linter_EnvLinter_Basic_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Basic_3183030336____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b1_1317_, v_ref_1318_, v_msg_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v_ref_1318_);
return v_res_1323_;
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
