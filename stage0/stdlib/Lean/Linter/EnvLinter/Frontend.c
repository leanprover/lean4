// Lean compiler output
// Module: Lean.Linter.EnvLinter.Frontend
// Imports: public import Lean.Linter.EnvLinter.Basic import Lean.DeclarationRange import Lean.Util.Path import Lean.CoreM import Lean.Elab.Command
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Elab_Command_mkMetaContext;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_wrapAsync___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_as_task(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
extern lean_object* l_Lean_Linter_EnvLinter_builtinNolintAttr;
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_declRangeExt;
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_allImportedModuleNames(lean_object*);
uint8_t l_Lean_isRecCore(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_builtinDeclRanges;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_isAuxRecursor(lean_object*, lean_object*);
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l_Lean_Environment_constants(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Linter_EnvLinter_getEnvLinter(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SearchPath_findWithExt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_Environment_const2ModIdx(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_getSrcSearchPath();
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Linter_EnvLinter_isAutoDecl___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_EnvLinter_envLinterExt;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default;
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity;
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_LintVerbosity_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Linter.EnvLinter.LintVerbosity.low"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__0_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1_value;
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean.Linter.EnvLinter.LintVerbosity.medium"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__2_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3_value;
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Lean.Linter.EnvLinter.LintVerbosity.high"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__4_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6;
static lean_once_cell_t l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintVerbosity___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_extra_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_extra_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_extra_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_extra_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instInhabitedLintScope_default;
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instInhabitedLintScope;
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_LintScope_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instDecidableEqLintScope(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instDecidableEqLintScope___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Linter.EnvLinter.LintScope.default"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__0_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1_value;
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Lean.Linter.EnvLinter.LintScope.extra"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__2_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3_value;
static const lean_string_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Linter.EnvLinter.LintScope.all"};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4_value;
static const lean_ctor_object l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__4_value)}};
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_EnvLinter_instReprLintScope___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_EnvLinter_instReprLintScope_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Linter_EnvLinter_instReprLintScope = (const lean_object*)&l_Lean_Linter_EnvLinter_instReprLintScope___closed__0_value;
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Linter_EnvLinter_getChecks___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_EnvLinter_getChecks___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_getChecks___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getChecks(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getChecks___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0;
static const lean_array_object l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "LINTER FAILED:\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "#check "};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__0_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__1;
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " /- "};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__2_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__3;
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " -/"};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__4_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__5;
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__6 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__6_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__7;
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = ": error: "};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__8 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__8_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__9;
static const lean_string_object l_Lean_Linter_EnvLinter_printWarning___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__10 = (const lean_object*)&l_Lean_Linter_EnvLinter_printWarning___closed__10_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarning___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarning___closed__11;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_EnvLinter_printWarnings___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_printWarnings___closed__0;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-- "};
static const lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1;
static const lean_string_object l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2 = (const lean_object*)&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Linter_EnvLinter_groupedByFilename___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_groupedByFilename___closed__0;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "/- The `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` linter reports:\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " -/\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "/- OK: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "-- (non-default linters skipped)\n"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__0_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__1;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " in "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__2 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__2_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__3;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = " declarations (plus "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__4 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__4_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__5;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = " automatically generated ones) "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__6 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__6_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__7;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " with "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__8 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__8_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__9;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = " linters\n\n"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__10 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__10_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__11;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "-- Found "};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__12 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__12_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__13;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " error"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__14 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__14_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_formatLinterResults___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__15;
static const lean_string_object l_Lean_Linter_EnvLinter_formatLinterResults___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___closed__16 = (const lean_object*)&l_Lean_Linter_EnvLinter_formatLinterResults___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
uint8_t v_x_boxed_6_; lean_object* v_res_7_; 
v_x_boxed_6_ = lean_unbox(v_x_5_);
v_res_7_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_x_boxed_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_Linter_EnvLinter_LintVerbosity_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg(lean_object* v_low_28_){
_start:
{
lean_inc(v_low_28_);
return v_low_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg___boxed(lean_object* v_low_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___redArg(v_low_29_);
lean_dec(v_low_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_low_34_){
_start:
{
lean_inc(v_low_34_);
return v_low_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_low_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_low_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_Linter_EnvLinter_LintVerbosity_low_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_low_38_);
lean_dec(v_low_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg(lean_object* v_medium_41_){
_start:
{
lean_inc(v_medium_41_);
return v_medium_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg___boxed(lean_object* v_medium_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___redArg(v_medium_42_);
lean_dec(v_medium_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_medium_47_){
_start:
{
lean_inc(v_medium_47_);
return v_medium_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_medium_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_Linter_EnvLinter_LintVerbosity_medium_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_medium_51_);
lean_dec(v_medium_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg(lean_object* v_high_54_){
_start:
{
lean_inc(v_high_54_);
return v_high_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg___boxed(lean_object* v_high_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___redArg(v_high_55_);
lean_dec(v_high_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_high_60_){
_start:
{
lean_inc(v_high_60_);
return v_high_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_high_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_high_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_Linter_EnvLinter_LintVerbosity_high_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_high_64_);
lean_dec(v_high_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_LintVerbosity_ofNat(lean_object* v_n_69_){
_start:
{
lean_object* v___x_70_; uint8_t v___x_71_; 
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_nat_dec_le(v_n_69_, v___x_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_dec_le(v_n_69_, v___x_72_);
if (v___x_73_ == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 2;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 1;
return v___x_75_;
}
}
else
{
uint8_t v___x_76_; 
v___x_76_ = 0;
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintVerbosity_ofNat___boxed(lean_object* v_n_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Lean_Linter_EnvLinter_LintVerbosity_ofNat(v_n_77_);
lean_dec(v_n_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(uint8_t v_x_80_, uint8_t v_y_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_x_80_);
v___x_83_ = l_Lean_Linter_EnvLinter_LintVerbosity_ctorIdx(v_y_81_);
v___x_84_ = lean_nat_dec_eq(v___x_82_, v___x_83_);
lean_dec(v___x_83_);
lean_dec(v___x_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity___boxed(lean_object* v_x_85_, lean_object* v_y_86_){
_start:
{
uint8_t v_x_13__boxed_87_; uint8_t v_y_14__boxed_88_; uint8_t v_res_89_; lean_object* v_r_90_; 
v_x_13__boxed_87_ = lean_unbox(v_x_85_);
v_y_14__boxed_88_ = lean_unbox(v_y_86_);
v_res_89_ = l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(v_x_13__boxed_87_, v_y_14__boxed_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(2u);
v___x_101_ = lean_nat_to_int(v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_unsigned_to_nat(1u);
v___x_103_ = lean_nat_to_int(v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr(uint8_t v_x_104_, lean_object* v_prec_105_){
_start:
{
lean_object* v___y_107_; lean_object* v___y_114_; lean_object* v___y_121_; 
switch(v_x_104_)
{
case 0:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_unsigned_to_nat(1024u);
v___x_128_ = lean_nat_dec_le(v___x_127_, v_prec_105_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
v___x_129_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_107_ = v___x_129_;
goto v___jp_106_;
}
else
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_107_ = v___x_130_;
goto v___jp_106_;
}
}
case 1:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = lean_unsigned_to_nat(1024u);
v___x_132_ = lean_nat_dec_le(v___x_131_, v_prec_105_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_114_ = v___x_133_;
goto v___jp_113_;
}
else
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_114_ = v___x_134_;
goto v___jp_113_;
}
}
default: 
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_unsigned_to_nat(1024u);
v___x_136_ = lean_nat_dec_le(v___x_135_, v_prec_105_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_121_ = v___x_137_;
goto v___jp_120_;
}
else
{
lean_object* v___x_138_; 
v___x_138_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_121_ = v___x_138_;
goto v___jp_120_;
}
}
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_108_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__1));
lean_inc(v___y_107_);
v___x_109_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_109_, 0, v___y_107_);
lean_ctor_set(v___x_109_, 1, v___x_108_);
v___x_110_ = 0;
v___x_111_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set_uint8(v___x_111_, sizeof(void*)*1, v___x_110_);
v___x_112_ = l_Repr_addAppParen(v___x_111_, v_prec_105_);
return v___x_112_;
}
v___jp_113_:
{
lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_115_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__3));
lean_inc(v___y_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___y_114_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
v___x_117_ = 0;
v___x_118_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_118_, 0, v___x_116_);
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_117_);
v___x_119_ = l_Repr_addAppParen(v___x_118_, v_prec_105_);
return v___x_119_;
}
v___jp_120_:
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_122_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__5));
lean_inc(v___y_121_);
v___x_123_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_123_, 0, v___y_121_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = 0;
v___x_125_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_125_, 0, v___x_123_);
lean_ctor_set_uint8(v___x_125_, sizeof(void*)*1, v___x_124_);
v___x_126_ = l_Repr_addAppParen(v___x_125_, v_prec_105_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___boxed(lean_object* v_x_139_, lean_object* v_prec_140_){
_start:
{
uint8_t v_x_177__boxed_141_; lean_object* v_res_142_; 
v_x_177__boxed_141_ = lean_unbox(v_x_139_);
v_res_142_ = l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr(v_x_177__boxed_141_, v_prec_140_);
lean_dec(v_prec_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorIdx(uint8_t v_x_145_){
_start:
{
switch(v_x_145_)
{
case 0:
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(0u);
return v___x_146_;
}
case 1:
{
lean_object* v___x_147_; 
v___x_147_ = lean_unsigned_to_nat(1u);
return v___x_147_;
}
default: 
{
lean_object* v___x_148_; 
v___x_148_ = lean_unsigned_to_nat(2u);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorIdx___boxed(lean_object* v_x_149_){
_start:
{
uint8_t v_x_boxed_150_; lean_object* v_res_151_; 
v_x_boxed_150_ = lean_unbox(v_x_149_);
v_res_151_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_x_boxed_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_toCtorIdx(uint8_t v_x_152_){
_start:
{
lean_object* v___x_153_; 
v___x_153_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_toCtorIdx___boxed(lean_object* v_x_154_){
_start:
{
uint8_t v_x_4__boxed_155_; lean_object* v_res_156_; 
v_x_4__boxed_155_ = lean_unbox(v_x_154_);
v_res_156_ = l_Lean_Linter_EnvLinter_LintScope_toCtorIdx(v_x_4__boxed_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg(lean_object* v_k_157_){
_start:
{
lean_inc(v_k_157_);
return v_k_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg___boxed(lean_object* v_k_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lean_Linter_EnvLinter_LintScope_ctorElim___redArg(v_k_158_);
lean_dec(v_k_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim(lean_object* v_motive_160_, lean_object* v_ctorIdx_161_, uint8_t v_t_162_, lean_object* v_h_163_, lean_object* v_k_164_){
_start:
{
lean_inc(v_k_164_);
return v_k_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ctorElim___boxed(lean_object* v_motive_165_, lean_object* v_ctorIdx_166_, lean_object* v_t_167_, lean_object* v_h_168_, lean_object* v_k_169_){
_start:
{
uint8_t v_t_boxed_170_; lean_object* v_res_171_; 
v_t_boxed_170_ = lean_unbox(v_t_167_);
v_res_171_ = l_Lean_Linter_EnvLinter_LintScope_ctorElim(v_motive_165_, v_ctorIdx_166_, v_t_boxed_170_, v_h_168_, v_k_169_);
lean_dec(v_k_169_);
lean_dec(v_ctorIdx_166_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg(lean_object* v_default_172_){
_start:
{
lean_inc(v_default_172_);
return v_default_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg___boxed(lean_object* v_default_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_Linter_EnvLinter_LintScope_default_elim___redArg(v_default_173_);
lean_dec(v_default_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim(lean_object* v_motive_175_, uint8_t v_t_176_, lean_object* v_h_177_, lean_object* v_default_178_){
_start:
{
lean_inc(v_default_178_);
return v_default_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_default_elim___boxed(lean_object* v_motive_179_, lean_object* v_t_180_, lean_object* v_h_181_, lean_object* v_default_182_){
_start:
{
uint8_t v_t_boxed_183_; lean_object* v_res_184_; 
v_t_boxed_183_ = lean_unbox(v_t_180_);
v_res_184_ = l_Lean_Linter_EnvLinter_LintScope_default_elim(v_motive_179_, v_t_boxed_183_, v_h_181_, v_default_182_);
lean_dec(v_default_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_extra_elim___redArg(lean_object* v_extra_185_){
_start:
{
lean_inc(v_extra_185_);
return v_extra_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_extra_elim___redArg___boxed(lean_object* v_extra_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_Linter_EnvLinter_LintScope_extra_elim___redArg(v_extra_186_);
lean_dec(v_extra_186_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_extra_elim(lean_object* v_motive_188_, uint8_t v_t_189_, lean_object* v_h_190_, lean_object* v_extra_191_){
_start:
{
lean_inc(v_extra_191_);
return v_extra_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_extra_elim___boxed(lean_object* v_motive_192_, lean_object* v_t_193_, lean_object* v_h_194_, lean_object* v_extra_195_){
_start:
{
uint8_t v_t_boxed_196_; lean_object* v_res_197_; 
v_t_boxed_196_ = lean_unbox(v_t_193_);
v_res_197_ = l_Lean_Linter_EnvLinter_LintScope_extra_elim(v_motive_192_, v_t_boxed_196_, v_h_194_, v_extra_195_);
lean_dec(v_extra_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg(lean_object* v_all_198_){
_start:
{
lean_inc(v_all_198_);
return v_all_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg___boxed(lean_object* v_all_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Linter_EnvLinter_LintScope_all_elim___redArg(v_all_199_);
lean_dec(v_all_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim(lean_object* v_motive_201_, uint8_t v_t_202_, lean_object* v_h_203_, lean_object* v_all_204_){
_start:
{
lean_inc(v_all_204_);
return v_all_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_all_elim___boxed(lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h_207_, lean_object* v_all_208_){
_start:
{
uint8_t v_t_boxed_209_; lean_object* v_res_210_; 
v_t_boxed_209_ = lean_unbox(v_t_206_);
v_res_210_ = l_Lean_Linter_EnvLinter_LintScope_all_elim(v_motive_205_, v_t_boxed_209_, v_h_207_, v_all_208_);
lean_dec(v_all_208_);
return v_res_210_;
}
}
static uint8_t _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope_default(void){
_start:
{
uint8_t v___x_211_; 
v___x_211_ = 0;
return v___x_211_;
}
}
static uint8_t _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope(void){
_start:
{
uint8_t v___x_212_; 
v___x_212_ = 0;
return v___x_212_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_LintScope_ofNat(lean_object* v_n_213_){
_start:
{
lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_nat_dec_le(v_n_213_, v___x_214_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; uint8_t v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_dec_le(v_n_213_, v___x_216_);
if (v___x_217_ == 0)
{
uint8_t v___x_218_; 
v___x_218_ = 2;
return v___x_218_;
}
else
{
uint8_t v___x_219_; 
v___x_219_ = 1;
return v___x_219_;
}
}
else
{
uint8_t v___x_220_; 
v___x_220_ = 0;
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_LintScope_ofNat___boxed(lean_object* v_n_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Lean_Linter_EnvLinter_LintScope_ofNat(v_n_221_);
lean_dec(v_n_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_EnvLinter_instDecidableEqLintScope(uint8_t v_x_224_, uint8_t v_y_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_x_224_);
v___x_227_ = l_Lean_Linter_EnvLinter_LintScope_ctorIdx(v_y_225_);
v___x_228_ = lean_nat_dec_eq(v___x_226_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v___x_226_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instDecidableEqLintScope___boxed(lean_object* v_x_229_, lean_object* v_y_230_){
_start:
{
uint8_t v_x_13__boxed_231_; uint8_t v_y_14__boxed_232_; uint8_t v_res_233_; lean_object* v_r_234_; 
v_x_13__boxed_231_ = lean_unbox(v_x_229_);
v_y_14__boxed_232_ = lean_unbox(v_y_230_);
v_res_233_ = l_Lean_Linter_EnvLinter_instDecidableEqLintScope(v_x_13__boxed_231_, v_y_14__boxed_232_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr(uint8_t v_x_244_, lean_object* v_prec_245_){
_start:
{
lean_object* v___y_247_; lean_object* v___y_254_; lean_object* v___y_261_; 
switch(v_x_244_)
{
case 0:
{
lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1024u);
v___x_268_ = lean_nat_dec_le(v___x_267_, v_prec_245_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_247_ = v___x_269_;
goto v___jp_246_;
}
else
{
lean_object* v___x_270_; 
v___x_270_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_247_ = v___x_270_;
goto v___jp_246_;
}
}
case 1:
{
lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(1024u);
v___x_272_ = lean_nat_dec_le(v___x_271_, v_prec_245_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; 
v___x_273_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_254_ = v___x_273_;
goto v___jp_253_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_254_ = v___x_274_;
goto v___jp_253_;
}
}
default: 
{
lean_object* v___x_275_; uint8_t v___x_276_; 
v___x_275_ = lean_unsigned_to_nat(1024u);
v___x_276_ = lean_nat_dec_le(v___x_275_, v_prec_245_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
v___x_277_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__6);
v___y_261_ = v___x_277_;
goto v___jp_260_;
}
else
{
lean_object* v___x_278_; 
v___x_278_ = lean_obj_once(&l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7, &l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7_once, _init_l_Lean_Linter_EnvLinter_instReprLintVerbosity_repr___closed__7);
v___y_261_ = v___x_278_;
goto v___jp_260_;
}
}
}
v___jp_246_:
{
lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_248_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__1));
lean_inc(v___y_247_);
v___x_249_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_249_, 0, v___y_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = 0;
v___x_251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*1, v___x_250_);
v___x_252_ = l_Repr_addAppParen(v___x_251_, v_prec_245_);
return v___x_252_;
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_255_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__3));
lean_inc(v___y_254_);
v___x_256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_256_, 0, v___y_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = 0;
v___x_258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_257_);
v___x_259_ = l_Repr_addAppParen(v___x_258_, v_prec_245_);
return v___x_259_;
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_262_ = ((lean_object*)(l_Lean_Linter_EnvLinter_instReprLintScope_repr___closed__5));
lean_inc(v___y_261_);
v___x_263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_263_, 0, v___y_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = l_Repr_addAppParen(v___x_265_, v_prec_245_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_instReprLintScope_repr___boxed(lean_object* v_x_279_, lean_object* v_prec_280_){
_start:
{
uint8_t v_x_173__boxed_281_; lean_object* v_res_282_; 
v_x_173__boxed_281_ = lean_unbox(v_x_279_);
v_res_282_ = l_Lean_Linter_EnvLinter_instReprLintScope_repr(v_x_173__boxed_281_, v_prec_280_);
lean_dec(v_prec_280_);
return v_res_282_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(lean_object* v_x1_285_, lean_object* v_x2_286_){
_start:
{
lean_object* v_name_287_; lean_object* v_name_288_; uint8_t v___x_289_; 
v_name_287_ = lean_ctor_get(v_x1_285_, 1);
v_name_288_ = lean_ctor_get(v_x2_286_, 1);
v___x_289_ = l_Lean_Name_lt(v_name_287_, v_name_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0___boxed(lean_object* v_x1_290_, lean_object* v_x2_291_){
_start:
{
uint8_t v_res_292_; lean_object* v_r_293_; 
v_res_292_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_x1_290_, v_x2_291_);
lean_dec_ref(v_x2_291_);
lean_dec_ref(v_x1_290_);
v_r_293_ = lean_box(v_res_292_);
return v_r_293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(lean_object* v_a_294_, lean_object* v_as_295_, lean_object* v_k_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_mid_301_; lean_object* v_midVal_302_; uint8_t v___x_303_; 
v___x_299_ = lean_nat_add(v_x_297_, v_x_298_);
v___x_300_ = lean_unsigned_to_nat(1u);
v_mid_301_ = lean_nat_shiftr(v___x_299_, v___x_300_);
lean_dec(v___x_299_);
v_midVal_302_ = lean_array_fget_borrowed(v_as_295_, v_mid_301_);
v___x_303_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_midVal_302_, v_k_296_);
if (v___x_303_ == 0)
{
uint8_t v___x_304_; 
lean_dec(v_x_298_);
v___x_304_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_296_, v_midVal_302_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; uint8_t v___x_306_; 
lean_dec(v_x_297_);
v___x_305_ = lean_array_get_size(v_as_295_);
v___x_306_ = lean_nat_dec_lt(v_mid_301_, v___x_305_);
if (v___x_306_ == 0)
{
lean_dec(v_mid_301_);
lean_dec_ref(v_a_294_);
return v_as_295_;
}
else
{
lean_object* v___x_307_; lean_object* v_xs_x27_308_; lean_object* v___x_309_; 
v___x_307_ = lean_box(0);
v_xs_x27_308_ = lean_array_fset(v_as_295_, v_mid_301_, v___x_307_);
v___x_309_ = lean_array_fset(v_xs_x27_308_, v_mid_301_, v_a_294_);
lean_dec(v_mid_301_);
return v___x_309_;
}
}
else
{
v_x_298_ = v_mid_301_;
goto _start;
}
}
else
{
uint8_t v___x_311_; 
v___x_311_ = lean_nat_dec_eq(v_mid_301_, v_x_297_);
if (v___x_311_ == 0)
{
lean_dec(v_x_297_);
v_x_297_ = v_mid_301_;
goto _start;
}
else
{
lean_object* v___x_313_; lean_object* v_j_314_; lean_object* v_as_315_; lean_object* v___x_316_; 
lean_dec(v_mid_301_);
lean_dec(v_x_298_);
v___x_313_ = lean_nat_add(v_x_297_, v___x_300_);
lean_dec(v_x_297_);
v_j_314_ = lean_array_get_size(v_as_295_);
v_as_315_ = lean_array_push(v_as_295_, v_a_294_);
v___x_316_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_313_, v_as_315_, v_j_314_);
lean_dec(v___x_313_);
return v___x_316_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg___boxed(lean_object* v_a_317_, lean_object* v_as_318_, lean_object* v_k_319_, lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_317_, v_as_318_, v_k_319_, v_x_320_, v_x_321_);
lean_dec_ref(v_k_319_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(lean_object* v_a_323_, lean_object* v_as_324_, lean_object* v_k_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = lean_array_get_size(v_as_324_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_nat_dec_eq(v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_array_fget_borrowed(v_as_324_, v___x_327_);
v___x_330_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_325_, v___x_329_);
if (v___x_330_ == 0)
{
uint8_t v___x_331_; 
v___x_331_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v___x_329_, v_k_325_);
if (v___x_331_ == 0)
{
uint8_t v___x_332_; 
v___x_332_ = lean_nat_dec_lt(v___x_327_, v___x_326_);
if (v___x_332_ == 0)
{
lean_dec_ref(v_a_323_);
return v_as_324_;
}
else
{
lean_object* v___x_333_; lean_object* v_xs_x27_334_; lean_object* v___x_335_; 
v___x_333_ = lean_box(0);
v_xs_x27_334_ = lean_array_fset(v_as_324_, v___x_327_, v___x_333_);
v___x_335_ = lean_array_fset(v_xs_x27_334_, v___x_327_, v_a_323_);
return v___x_335_;
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_sub(v___x_326_, v___x_336_);
v___x_338_ = lean_array_fget_borrowed(v_as_324_, v___x_337_);
v___x_339_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v___x_338_, v_k_325_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___lam__0(v_k_325_, v___x_338_);
if (v___x_340_ == 0)
{
uint8_t v___x_341_; 
v___x_341_ = lean_nat_dec_lt(v___x_337_, v___x_326_);
if (v___x_341_ == 0)
{
lean_dec(v___x_337_);
lean_dec_ref(v_a_323_);
return v_as_324_;
}
else
{
lean_object* v___x_342_; lean_object* v_xs_x27_343_; lean_object* v___x_344_; 
v___x_342_ = lean_box(0);
v_xs_x27_343_ = lean_array_fset(v_as_324_, v___x_337_, v___x_342_);
v___x_344_ = lean_array_fset(v_xs_x27_343_, v___x_337_, v_a_323_);
lean_dec(v___x_337_);
return v___x_344_;
}
}
else
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_323_, v_as_324_, v_k_325_, v___x_327_, v___x_337_);
return v___x_345_;
}
}
else
{
lean_object* v___x_346_; 
lean_dec(v___x_337_);
v___x_346_ = lean_array_push(v_as_324_, v_a_323_);
return v___x_346_;
}
}
}
else
{
lean_object* v_as_347_; lean_object* v___x_348_; 
v_as_347_ = lean_array_push(v_as_324_, v_a_323_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_327_, v_as_347_, v___x_326_);
return v___x_348_;
}
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_array_push(v_as_324_, v_a_323_);
return v___x_349_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0___boxed(lean_object* v_a_350_, lean_object* v_as_351_, lean_object* v_k_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(v_a_350_, v_as_351_, v_k_352_);
lean_dec_ref(v_k_352_);
return v_res_353_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(lean_object* v_a_354_, lean_object* v_x_355_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
uint8_t v___x_356_; 
v___x_356_ = 0;
return v___x_356_;
}
else
{
lean_object* v_head_357_; lean_object* v_tail_358_; uint8_t v___x_359_; 
v_head_357_ = lean_ctor_get(v_x_355_, 0);
v_tail_358_ = lean_ctor_get(v_x_355_, 1);
v___x_359_ = lean_name_eq(v_a_354_, v_head_357_);
if (v___x_359_ == 0)
{
v_x_355_ = v_tail_358_;
goto _start;
}
else
{
return v___x_359_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1___boxed(lean_object* v_a_361_, lean_object* v_x_362_){
_start:
{
uint8_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(v_a_361_, v_x_362_);
lean_dec(v_x_362_);
lean_dec(v_a_361_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(lean_object* v_runOnly_365_, uint8_t v_scope_366_, lean_object* v_init_367_, lean_object* v_x_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_d_373_; 
if (lean_obj_tag(v_x_368_) == 0)
{
lean_object* v_k_376_; lean_object* v_v_377_; lean_object* v_l_378_; lean_object* v_r_379_; lean_object* v___x_380_; 
v_k_376_ = lean_ctor_get(v_x_368_, 1);
lean_inc(v_k_376_);
v_v_377_ = lean_ctor_get(v_x_368_, 2);
lean_inc(v_v_377_);
v_l_378_ = lean_ctor_get(v_x_368_, 3);
lean_inc(v_l_378_);
v_r_379_ = lean_ctor_get(v_x_368_, 4);
lean_inc(v_r_379_);
lean_dec_ref_known(v_x_368_, 5);
v___x_380_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_365_, v_scope_366_, v_init_367_, v_l_378_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_381_);
if (lean_obj_tag(v_a_381_) == 0)
{
lean_object* v_a_382_; 
lean_dec_ref_known(v___x_380_, 1);
lean_dec(v_r_379_);
lean_dec(v_v_377_);
lean_dec(v_k_376_);
v_a_382_ = lean_ctor_get(v_a_381_, 0);
lean_inc(v_a_382_);
lean_dec_ref_known(v_a_381_, 1);
v_d_373_ = v_a_382_;
goto v___jp_372_;
}
else
{
lean_object* v_a_383_; lean_object* v_fst_384_; lean_object* v_snd_385_; uint8_t v___y_400_; 
v_a_383_ = lean_ctor_get(v_a_381_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v_a_381_, 1);
v_fst_384_ = lean_ctor_get(v_v_377_, 0);
lean_inc(v_fst_384_);
v_snd_385_ = lean_ctor_get(v_v_377_, 1);
lean_inc(v_snd_385_);
lean_dec(v_v_377_);
if (lean_obj_tag(v_runOnly_365_) == 0)
{
if (v_scope_366_ == 0)
{
uint8_t v___x_405_; 
v___x_405_ = lean_unbox(v_snd_385_);
lean_dec(v_snd_385_);
v___y_400_ = v___x_405_;
goto v___jp_399_;
}
else
{
lean_dec(v_snd_385_);
lean_dec_ref_known(v___x_380_, 1);
goto v___jp_386_;
}
}
else
{
lean_object* v_val_406_; uint8_t v___x_407_; 
lean_dec(v_snd_385_);
v_val_406_ = lean_ctor_get(v_runOnly_365_, 0);
v___x_407_ = l_List_elem___at___00Lean_Linter_EnvLinter_getChecks_spec__1(v_k_376_, v_val_406_);
v___y_400_ = v___x_407_;
goto v___jp_399_;
}
v___jp_386_:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_Linter_EnvLinter_getEnvLinter(v_k_376_, v_fst_384_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_389_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
lean_inc_n(v_a_388_, 2);
lean_dec_ref_known(v___x_387_, 1);
v___x_389_ = l_Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0(v_a_388_, v_a_383_, v_a_388_);
lean_dec(v_a_388_);
v_init_367_ = v___x_389_;
v_x_368_ = v_r_379_;
goto _start;
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
lean_dec(v_a_383_);
lean_dec(v_r_379_);
v_a_391_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_387_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_387_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
v___jp_399_:
{
if (v___y_400_ == 0)
{
lean_dec(v_fst_384_);
lean_dec(v_a_383_);
lean_dec(v_k_376_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_401_; 
v_a_401_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_380_, 1);
if (lean_obj_tag(v_a_401_) == 0)
{
lean_object* v_a_402_; 
lean_dec(v_r_379_);
v_a_402_ = lean_ctor_get(v_a_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref_known(v_a_401_, 1);
v_d_373_ = v_a_402_;
goto v___jp_372_;
}
else
{
lean_object* v_a_403_; 
v_a_403_ = lean_ctor_get(v_a_401_, 0);
lean_inc(v_a_403_);
lean_dec_ref_known(v_a_401_, 1);
v_init_367_ = v_a_403_;
v_x_368_ = v_r_379_;
goto _start;
}
}
else
{
lean_dec(v_r_379_);
return v___x_380_;
}
}
else
{
lean_dec_ref_known(v___x_380_, 1);
goto v___jp_386_;
}
}
}
}
else
{
lean_dec(v_r_379_);
lean_dec(v_v_377_);
lean_dec(v_k_376_);
return v___x_380_;
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_408_, 0, v_init_367_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
return v___x_409_;
}
v___jp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_d_373_);
v___x_375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2___boxed(lean_object* v_runOnly_410_, lean_object* v_scope_411_, lean_object* v_init_412_, lean_object* v_x_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
uint8_t v_scope_boxed_417_; lean_object* v_res_418_; 
v_scope_boxed_417_ = lean_unbox(v_scope_411_);
v_res_418_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_410_, v_scope_boxed_417_, v_init_412_, v_x_413_, v___y_414_, v___y_415_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v_runOnly_410_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getChecks(uint8_t v_scope_421_, lean_object* v_runOnly_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; lean_object* v_env_427_; lean_object* v___x_428_; lean_object* v_toEnvExtension_429_; lean_object* v_asyncMode_430_; lean_object* v___x_431_; lean_object* v_result_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_426_ = lean_st_ref_get(v_a_424_);
v_env_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc_ref(v_env_427_);
lean_dec(v___x_426_);
v___x_428_ = l_Lean_Linter_EnvLinter_envLinterExt;
v_toEnvExtension_429_ = lean_ctor_get(v___x_428_, 0);
v_asyncMode_430_ = lean_ctor_get(v_toEnvExtension_429_, 2);
v___x_431_ = lean_box(1);
v_result_432_ = ((lean_object*)(l_Lean_Linter_EnvLinter_getChecks___closed__0));
v___x_433_ = lean_box(0);
v___x_434_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_431_, v___x_428_, v_env_427_, v_asyncMode_430_, v___x_433_);
v___x_435_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Linter_EnvLinter_getChecks_spec__2(v_runOnly_422_, v_scope_421_, v_result_432_, v___x_434_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_444_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v_a_440_; lean_object* v___x_442_; 
v_a_440_ = lean_ctor_get(v_a_436_, 0);
lean_inc(v_a_440_);
lean_dec(v_a_436_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v_a_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_452_; 
v_a_445_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_452_ == 0)
{
v___x_447_ = v___x_435_;
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_435_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_452_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v___x_450_; 
if (v_isShared_448_ == 0)
{
v___x_450_ = v___x_447_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_a_445_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getChecks___boxed(lean_object* v_scope_453_, lean_object* v_runOnly_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
uint8_t v_scope_boxed_458_; lean_object* v_res_459_; 
v_scope_boxed_458_ = lean_unbox(v_scope_453_);
v_res_459_ = l_Lean_Linter_EnvLinter_getChecks(v_scope_boxed_458_, v_runOnly_454_, v_a_455_, v_a_456_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
lean_dec(v_runOnly_454_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0(lean_object* v_a_460_, lean_object* v_as_461_, lean_object* v_k_462_, lean_object* v_x_463_, lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___redArg(v_a_460_, v_as_461_, v_k_462_, v_x_463_, v_x_464_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0___boxed(lean_object* v_a_468_, lean_object* v_as_469_, lean_object* v_k_470_, lean_object* v_x_471_, lean_object* v_x_472_, lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00Lean_Linter_EnvLinter_getChecks_spec__0_spec__0(v_a_468_, v_as_469_, v_k_470_, v_x_471_, v_x_472_, v_x_473_, v_x_474_);
lean_dec_ref(v_k_470_);
return v_res_475_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(lean_object* v_a_476_, lean_object* v_as_477_, size_t v_i_478_, size_t v_stop_479_){
_start:
{
uint8_t v___x_480_; 
v___x_480_ = lean_usize_dec_eq(v_i_478_, v_stop_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_481_ = lean_array_uget_borrowed(v_as_477_, v_i_478_);
v___x_482_ = lean_name_eq(v_a_476_, v___x_481_);
if (v___x_482_ == 0)
{
size_t v___x_483_; size_t v___x_484_; 
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_add(v_i_478_, v___x_483_);
v_i_478_ = v___x_484_;
goto _start;
}
else
{
return v___x_482_;
}
}
else
{
uint8_t v___x_486_; 
v___x_486_ = 0;
return v___x_486_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8___boxed(lean_object* v_a_487_, lean_object* v_as_488_, lean_object* v_i_489_, lean_object* v_stop_490_){
_start:
{
size_t v_i_boxed_491_; size_t v_stop_boxed_492_; uint8_t v_res_493_; lean_object* v_r_494_; 
v_i_boxed_491_ = lean_unbox_usize(v_i_489_);
lean_dec(v_i_489_);
v_stop_boxed_492_ = lean_unbox_usize(v_stop_490_);
lean_dec(v_stop_490_);
v_res_493_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(v_a_487_, v_as_488_, v_i_boxed_491_, v_stop_boxed_492_);
lean_dec_ref(v_as_488_);
lean_dec(v_a_487_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(lean_object* v_as_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_array_get_size(v_as_495_);
v___x_499_ = lean_nat_dec_lt(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
return v___x_499_;
}
else
{
if (v___x_499_ == 0)
{
return v___x_499_;
}
else
{
size_t v___x_500_; size_t v___x_501_; uint8_t v___x_502_; 
v___x_500_ = ((size_t)0ULL);
v___x_501_ = lean_usize_of_nat(v___x_498_);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6_spec__8(v_a_496_, v_as_495_, v___x_500_, v___x_501_);
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6___boxed(lean_object* v_as_503_, lean_object* v_a_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(v_as_503_, v_a_504_);
lean_dec(v_a_504_);
lean_dec_ref(v_as_503_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Array_instInhabited(lean_box(0));
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(lean_object* v_linter_510_, lean_object* v_decl_511_, lean_object* v___y_512_){
_start:
{
lean_object* v___x_514_; lean_object* v___y_516_; lean_object* v_env_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_514_ = lean_st_ref_get(v___y_512_);
v_env_524_ = lean_ctor_get(v___x_514_, 0);
lean_inc_ref(v_env_524_);
lean_dec(v___x_514_);
v___x_525_ = lean_obj_once(&l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0, &l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0_once, _init_l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__0);
v___x_526_ = l_Lean_Linter_EnvLinter_builtinNolintAttr;
v___x_527_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_525_, v___x_526_, v_env_524_, v_decl_511_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_528_; 
v___x_528_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___y_516_ = v___x_528_;
goto v___jp_515_;
}
else
{
lean_object* v_val_529_; 
v_val_529_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_val_529_);
lean_dec_ref_known(v___x_527_, 1);
v___y_516_ = v_val_529_;
goto v___jp_515_;
}
v___jp_515_:
{
uint8_t v___x_517_; 
v___x_517_ = l_Array_contains___at___00Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3_spec__6(v___y_516_, v_linter_510_);
lean_dec_ref(v___y_516_);
if (v___x_517_ == 0)
{
uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_518_ = 1;
v___x_519_ = lean_box(v___x_518_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
else
{
uint8_t v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_521_ = 0;
v___x_522_ = lean_box(v___x_521_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___boxed(lean_object* v_linter_530_, lean_object* v_decl_531_, lean_object* v___y_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v_linter_530_, v_decl_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec(v_linter_530_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(lean_object* v___x_535_, lean_object* v_as_536_, size_t v_i_537_, size_t v_stop_538_, lean_object* v_b_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = lean_usize_dec_eq(v_i_537_, v_stop_538_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_array_uget_borrowed(v_as_536_, v_i_537_);
lean_inc(v___x_544_);
v___x_545_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v___x_535_, v___x_544_, v___y_541_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v_a_546_; lean_object* v_a_548_; uint8_t v___x_552_; 
v_a_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v___x_545_, 1);
v___x_552_ = lean_unbox(v_a_546_);
lean_dec(v_a_546_);
if (v___x_552_ == 0)
{
v_a_548_ = v_b_539_;
goto v___jp_547_;
}
else
{
lean_object* v___x_553_; 
lean_inc(v___x_544_);
v___x_553_ = lean_array_push(v_b_539_, v___x_544_);
v_a_548_ = v___x_553_;
goto v___jp_547_;
}
v___jp_547_:
{
size_t v___x_549_; size_t v___x_550_; 
v___x_549_ = ((size_t)1ULL);
v___x_550_ = lean_usize_add(v_i_537_, v___x_549_);
v_i_537_ = v___x_550_;
v_b_539_ = v_a_548_;
goto _start;
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec_ref(v_b_539_);
v_a_554_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_545_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_545_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
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
else
{
lean_object* v___x_562_; 
v___x_562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_562_, 0, v_b_539_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4___boxed(lean_object* v___x_563_, lean_object* v_as_564_, lean_object* v_i_565_, lean_object* v_stop_566_, lean_object* v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
size_t v_i_boxed_571_; size_t v_stop_boxed_572_; lean_object* v_res_573_; 
v_i_boxed_571_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_stop_boxed_572_ = lean_unbox_usize(v_stop_566_);
lean_dec(v_stop_566_);
v_res_573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v___x_563_, v_as_564_, v_i_boxed_571_, v_stop_boxed_572_, v_b_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec_ref(v_as_564_);
lean_dec(v___x_563_);
return v_res_573_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0(void){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_574_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__0);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2(void){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_578_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
lean_ctor_set(v___x_578_, 2, v___x_577_);
lean_ctor_set(v___x_578_, 3, v___x_577_);
lean_ctor_set(v___x_578_, 4, v___x_577_);
lean_ctor_set(v___x_578_, 5, v___x_577_);
return v___x_578_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_unsigned_to_nat(32u);
v___x_580_ = lean_mk_empty_array_with_capacity(v___x_579_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
lean_ctor_set(v___x_583_, 2, v___x_582_);
lean_ctor_set(v___x_583_, 3, v___x_582_);
lean_ctor_set(v___x_583_, 4, v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(lean_object* v___x_584_, lean_object* v___x_585_, lean_object* v_test_586_, lean_object* v_v_587_, lean_object* v_x_588_, lean_object* v___y_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; size_t v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_592_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
lean_inc_n(v___x_584_, 5);
v___x_593_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_593_, 0, v___x_584_);
lean_ctor_set(v___x_593_, 1, v___x_584_);
lean_ctor_set(v___x_593_, 2, v___x_584_);
lean_ctor_set(v___x_593_, 3, v___x_584_);
lean_ctor_set(v___x_593_, 4, v___x_592_);
lean_ctor_set(v___x_593_, 5, v___x_592_);
lean_ctor_set(v___x_593_, 6, v___x_592_);
lean_ctor_set(v___x_593_, 7, v___x_592_);
lean_ctor_set(v___x_593_, 8, v___x_592_);
lean_ctor_set(v___x_593_, 9, v___x_592_);
v___x_594_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__2);
v___x_595_ = lean_unsigned_to_nat(32u);
v___x_596_ = lean_mk_empty_array_with_capacity(v___x_595_);
v___x_597_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__3);
v___x_598_ = ((size_t)5ULL);
v___x_599_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_596_);
lean_ctor_set(v___x_599_, 2, v___x_584_);
lean_ctor_set(v___x_599_, 3, v___x_584_);
lean_ctor_set_usize(v___x_599_, 4, v___x_598_);
v___x_600_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__4);
v___x_601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_601_, 0, v___x_593_);
lean_ctor_set(v___x_601_, 1, v___x_594_);
lean_ctor_set(v___x_601_, 2, v___x_585_);
lean_ctor_set(v___x_601_, 3, v___x_599_);
lean_ctor_set(v___x_601_, 4, v___x_600_);
v___x_602_ = lean_st_mk_ref(v___x_601_);
v___x_603_ = l_Lean_Elab_Command_mkMetaContext;
lean_inc(v___y_590_);
lean_inc_ref(v___y_589_);
lean_inc(v___x_602_);
v___x_604_ = lean_apply_6(v_test_586_, v_v_587_, v___x_603_, v___x_602_, v___y_589_, v___y_590_, lean_box(0));
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_613_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_613_ == 0)
{
v___x_607_ = v___x_604_;
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_604_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_613_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_st_ref_get(v___x_602_);
lean_dec(v___x_602_);
lean_dec(v___x_609_);
if (v_isShared_608_ == 0)
{
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_605_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
else
{
lean_dec(v___x_602_);
return v___x_604_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed(lean_object* v___x_614_, lean_object* v___x_615_, lean_object* v_test_616_, lean_object* v_v_617_, lean_object* v_x_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0(v___x_614_, v___x_615_, v_test_616_, v_v_617_, v_x_618_, v___y_619_, v___y_620_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(lean_object* v_a_623_, lean_object* v___x_624_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = lean_apply_2(v_a_623_, v___x_624_, lean_box(0));
if (lean_obj_tag(v___x_626_) == 0)
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
v_a_627_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_626_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_626_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
lean_ctor_set_tag(v___x_629_, 1);
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
v_a_635_ = lean_ctor_get(v___x_626_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_626_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_626_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_626_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 0);
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed(lean_object* v_a_643_, lean_object* v___x_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1(v_a_643_, v___x_644_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(lean_object* v_linter_647_, size_t v_sz_648_, size_t v_i_649_, lean_object* v_bs_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
uint8_t v___x_654_; 
v___x_654_ = lean_usize_dec_lt(v_i_649_, v_sz_648_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec_ref(v_linter_647_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_bs_650_);
return v___x_655_;
}
else
{
lean_object* v_toEnvLinter_656_; lean_object* v_test_657_; lean_object* v_v_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___f_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v_toEnvLinter_656_ = lean_ctor_get(v_linter_647_, 0);
v_test_657_ = lean_ctor_get(v_toEnvLinter_656_, 0);
v_v_658_ = lean_array_uget(v_bs_650_, v_i_649_);
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_box(1);
lean_inc(v_v_658_);
lean_inc_ref(v_test_657_);
v___f_661_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___boxed), 8, 4);
lean_closure_set(v___f_661_, 0, v___x_659_);
lean_closure_set(v___f_661_, 1, v___x_660_);
lean_closure_set(v___f_661_, 2, v_test_657_);
lean_closure_set(v___f_661_, 3, v_v_658_);
v___x_662_ = lean_box(0);
v___x_663_ = l_Lean_Core_wrapAsync___redArg(v___f_661_, v___x_662_, v___y_651_, v___y_652_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_665_; lean_object* v___f_666_; lean_object* v___x_667_; lean_object* v_bs_x27_668_; lean_object* v___x_669_; size_t v___x_670_; size_t v___x_671_; lean_object* v___x_672_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
v___x_665_ = lean_box(0);
v___f_666_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__1___boxed), 3, 2);
lean_closure_set(v___f_666_, 0, v_a_664_);
lean_closure_set(v___f_666_, 1, v___x_665_);
v___x_667_ = lean_io_as_task(v___f_666_, v___x_659_);
v_bs_x27_668_ = lean_array_uset(v_bs_650_, v_i_649_, v___x_659_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_v_658_);
lean_ctor_set(v___x_669_, 1, v___x_667_);
v___x_670_ = ((size_t)1ULL);
v___x_671_ = lean_usize_add(v_i_649_, v___x_670_);
v___x_672_ = lean_array_uset(v_bs_x27_668_, v_i_649_, v___x_669_);
v_i_649_ = v___x_671_;
v_bs_650_ = v___x_672_;
goto _start;
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_v_658_);
lean_dec_ref(v_bs_650_);
lean_dec_ref(v_linter_647_);
v_a_674_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_663_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_663_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___boxed(lean_object* v_linter_682_, lean_object* v_sz_683_, lean_object* v_i_684_, lean_object* v_bs_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
size_t v_sz_boxed_689_; size_t v_i_boxed_690_; lean_object* v_res_691_; 
v_sz_boxed_689_ = lean_unbox_usize(v_sz_683_);
lean_dec(v_sz_683_);
v_i_boxed_690_ = lean_unbox_usize(v_i_684_);
lean_dec(v_i_684_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_linter_682_, v_sz_boxed_689_, v_i_boxed_690_, v_bs_685_, v___y_686_, v___y_687_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(lean_object* v_decls_692_, size_t v_sz_693_, size_t v_i_694_, lean_object* v_bs_695_, lean_object* v___y_696_, lean_object* v___y_697_){
_start:
{
uint8_t v___x_699_; 
v___x_699_ = lean_usize_dec_lt(v_i_694_, v_sz_693_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v_bs_695_);
return v___x_700_;
}
else
{
lean_object* v_v_701_; lean_object* v___x_702_; lean_object* v_bs_x27_703_; lean_object* v_a_705_; lean_object* v___y_716_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_v_701_ = lean_array_uget(v_bs_695_, v_i_694_);
v___x_702_ = lean_unsigned_to_nat(0u);
v_bs_x27_703_ = lean_array_uset(v_bs_695_, v_i_694_, v___x_702_);
v___x_726_ = lean_array_get_size(v_decls_692_);
v___x_727_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___x_728_ = lean_nat_dec_lt(v___x_702_, v___x_726_);
if (v___x_728_ == 0)
{
v_a_705_ = v___x_727_;
goto v___jp_704_;
}
else
{
lean_object* v_name_729_; uint8_t v___x_730_; 
v_name_729_ = lean_ctor_get(v_v_701_, 1);
v___x_730_ = lean_nat_dec_le(v___x_726_, v___x_726_);
if (v___x_730_ == 0)
{
if (v___x_728_ == 0)
{
v_a_705_ = v___x_727_;
goto v___jp_704_;
}
else
{
size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; 
v___x_731_ = ((size_t)0ULL);
v___x_732_ = lean_usize_of_nat(v___x_726_);
v___x_733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v_name_729_, v_decls_692_, v___x_731_, v___x_732_, v___x_727_, v___y_696_, v___y_697_);
v___y_716_ = v___x_733_;
goto v___jp_715_;
}
}
else
{
size_t v___x_734_; size_t v___x_735_; lean_object* v___x_736_; 
v___x_734_ = ((size_t)0ULL);
v___x_735_ = lean_usize_of_nat(v___x_726_);
v___x_736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_lintCore_spec__4(v_name_729_, v_decls_692_, v___x_734_, v___x_735_, v___x_727_, v___y_696_, v___y_697_);
v___y_716_ = v___x_736_;
goto v___jp_715_;
}
}
v___jp_704_:
{
size_t v_sz_706_; size_t v___x_707_; lean_object* v___x_708_; 
v_sz_706_ = lean_array_size(v_a_705_);
v___x_707_ = ((size_t)0ULL);
lean_inc(v_v_701_);
v___x_708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2(v_v_701_, v_sz_706_, v___x_707_, v_a_705_, v___y_696_, v___y_697_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; size_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v_v_701_);
lean_ctor_set(v___x_710_, 1, v_a_709_);
v___x_711_ = ((size_t)1ULL);
v___x_712_ = lean_usize_add(v_i_694_, v___x_711_);
v___x_713_ = lean_array_uset(v_bs_x27_703_, v_i_694_, v___x_710_);
v_i_694_ = v___x_712_;
v_bs_695_ = v___x_713_;
goto _start;
}
else
{
lean_dec_ref(v_bs_x27_703_);
lean_dec(v_v_701_);
return v___x_708_;
}
}
v___jp_715_:
{
if (lean_obj_tag(v___y_716_) == 0)
{
lean_object* v_a_717_; 
v_a_717_ = lean_ctor_get(v___y_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___y_716_, 1);
v_a_705_ = v_a_717_;
goto v___jp_704_;
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v_bs_x27_703_);
lean_dec(v_v_701_);
v_a_718_ = lean_ctor_get(v___y_716_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___y_716_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___y_716_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___y_716_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5___boxed(lean_object* v_decls_737_, lean_object* v_sz_738_, lean_object* v_i_739_, lean_object* v_bs_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
size_t v_sz_boxed_744_; size_t v_i_boxed_745_; lean_object* v_res_746_; 
v_sz_boxed_744_ = lean_unbox_usize(v_sz_738_);
lean_dec(v_sz_738_);
v_i_boxed_745_ = lean_unbox_usize(v_i_739_);
lean_dec(v_i_739_);
v_res_746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_decls_737_, v_sz_boxed_744_, v_i_boxed_745_, v_bs_740_, v___y_741_, v___y_742_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec_ref(v_decls_737_);
return v_res_746_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_747_; uint64_t v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(1723u);
v___x_748_ = lean_uint64_of_nat(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(lean_object* v_x_749_, lean_object* v_x_750_){
_start:
{
if (lean_obj_tag(v_x_750_) == 0)
{
return v_x_749_;
}
else
{
lean_object* v_key_751_; lean_object* v_value_752_; lean_object* v_tail_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_779_; 
v_key_751_ = lean_ctor_get(v_x_750_, 0);
v_value_752_ = lean_ctor_get(v_x_750_, 1);
v_tail_753_ = lean_ctor_get(v_x_750_, 2);
v_isSharedCheck_779_ = !lean_is_exclusive(v_x_750_);
if (v_isSharedCheck_779_ == 0)
{
v___x_755_ = v_x_750_;
v_isShared_756_ = v_isSharedCheck_779_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_tail_753_);
lean_inc(v_value_752_);
lean_inc(v_key_751_);
lean_dec(v_x_750_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_779_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; uint64_t v___y_759_; 
v___x_757_ = lean_array_get_size(v_x_749_);
if (lean_obj_tag(v_key_751_) == 0)
{
uint64_t v___x_777_; 
v___x_777_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_759_ = v___x_777_;
goto v___jp_758_;
}
else
{
uint64_t v_hash_778_; 
v_hash_778_ = lean_ctor_get_uint64(v_key_751_, sizeof(void*)*2);
v___y_759_ = v_hash_778_;
goto v___jp_758_;
}
v___jp_758_:
{
uint64_t v___x_760_; uint64_t v___x_761_; uint64_t v_fold_762_; uint64_t v___x_763_; uint64_t v___x_764_; uint64_t v___x_765_; size_t v___x_766_; size_t v___x_767_; size_t v___x_768_; size_t v___x_769_; size_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_760_ = 32ULL;
v___x_761_ = lean_uint64_shift_right(v___y_759_, v___x_760_);
v_fold_762_ = lean_uint64_xor(v___y_759_, v___x_761_);
v___x_763_ = 16ULL;
v___x_764_ = lean_uint64_shift_right(v_fold_762_, v___x_763_);
v___x_765_ = lean_uint64_xor(v_fold_762_, v___x_764_);
v___x_766_ = lean_uint64_to_usize(v___x_765_);
v___x_767_ = lean_usize_of_nat(v___x_757_);
v___x_768_ = ((size_t)1ULL);
v___x_769_ = lean_usize_sub(v___x_767_, v___x_768_);
v___x_770_ = lean_usize_land(v___x_766_, v___x_769_);
v___x_771_ = lean_array_uget_borrowed(v_x_749_, v___x_770_);
lean_inc(v___x_771_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 2, v___x_771_);
v___x_773_ = v___x_755_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_key_751_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_value_752_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v___x_771_);
v___x_773_ = v_reuseFailAlloc_776_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = lean_array_uset(v_x_749_, v___x_770_, v___x_773_);
v_x_749_ = v___x_774_;
v_x_750_ = v_tail_753_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(lean_object* v_i_780_, lean_object* v_source_781_, lean_object* v_target_782_){
_start:
{
lean_object* v___x_783_; uint8_t v___x_784_; 
v___x_783_ = lean_array_get_size(v_source_781_);
v___x_784_ = lean_nat_dec_lt(v_i_780_, v___x_783_);
if (v___x_784_ == 0)
{
lean_dec_ref(v_source_781_);
lean_dec(v_i_780_);
return v_target_782_;
}
else
{
lean_object* v_es_785_; lean_object* v___x_786_; lean_object* v_source_787_; lean_object* v_target_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v_es_785_ = lean_array_fget(v_source_781_, v_i_780_);
v___x_786_ = lean_box(0);
v_source_787_ = lean_array_fset(v_source_781_, v_i_780_, v___x_786_);
v_target_788_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(v_target_782_, v_es_785_);
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_add(v_i_780_, v___x_789_);
lean_dec(v_i_780_);
v_i_780_ = v___x_790_;
v_source_781_ = v_source_787_;
v_target_782_ = v_target_788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(lean_object* v_data_792_){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_nbuckets_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_793_ = lean_array_get_size(v_data_792_);
v___x_794_ = lean_unsigned_to_nat(2u);
v_nbuckets_795_ = lean_nat_mul(v___x_793_, v___x_794_);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_box(0);
v___x_798_ = lean_mk_array(v_nbuckets_795_, v___x_797_);
v___x_799_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v___x_796_, v_data_792_, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(lean_object* v_a_800_, lean_object* v_b_801_, lean_object* v_x_802_){
_start:
{
if (lean_obj_tag(v_x_802_) == 0)
{
lean_dec(v_b_801_);
lean_dec(v_a_800_);
return v_x_802_;
}
else
{
lean_object* v_key_803_; lean_object* v_value_804_; lean_object* v_tail_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_817_; 
v_key_803_ = lean_ctor_get(v_x_802_, 0);
v_value_804_ = lean_ctor_get(v_x_802_, 1);
v_tail_805_ = lean_ctor_get(v_x_802_, 2);
v_isSharedCheck_817_ = !lean_is_exclusive(v_x_802_);
if (v_isSharedCheck_817_ == 0)
{
v___x_807_ = v_x_802_;
v_isShared_808_ = v_isSharedCheck_817_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_tail_805_);
lean_inc(v_value_804_);
lean_inc(v_key_803_);
lean_dec(v_x_802_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_817_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
uint8_t v___x_809_; 
v___x_809_ = lean_name_eq(v_key_803_, v_a_800_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_810_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_800_, v_b_801_, v_tail_805_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 2, v___x_810_);
v___x_812_ = v___x_807_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_key_803_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v_value_804_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v___x_810_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
else
{
lean_object* v___x_815_; 
lean_dec(v_value_804_);
lean_dec(v_key_803_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v_b_801_);
lean_ctor_set(v___x_807_, 0, v_a_800_);
v___x_815_ = v___x_807_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_800_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_b_801_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_tail_805_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(lean_object* v_a_818_, lean_object* v_x_819_){
_start:
{
if (lean_obj_tag(v_x_819_) == 0)
{
uint8_t v___x_820_; 
v___x_820_ = 0;
return v___x_820_;
}
else
{
lean_object* v_key_821_; lean_object* v_tail_822_; uint8_t v___x_823_; 
v_key_821_ = lean_ctor_get(v_x_819_, 0);
v_tail_822_ = lean_ctor_get(v_x_819_, 2);
v___x_823_ = lean_name_eq(v_key_821_, v_a_818_);
if (v___x_823_ == 0)
{
v_x_819_ = v_tail_822_;
goto _start;
}
else
{
return v___x_823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg___boxed(lean_object* v_a_825_, lean_object* v_x_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_825_, v_x_826_);
lean_dec(v_x_826_);
lean_dec(v_a_825_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(lean_object* v_m_829_, lean_object* v_a_830_, lean_object* v_b_831_){
_start:
{
lean_object* v_size_832_; lean_object* v_buckets_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_879_; 
v_size_832_ = lean_ctor_get(v_m_829_, 0);
v_buckets_833_ = lean_ctor_get(v_m_829_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_m_829_);
if (v_isSharedCheck_879_ == 0)
{
v___x_835_ = v_m_829_;
v_isShared_836_ = v_isSharedCheck_879_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_buckets_833_);
lean_inc(v_size_832_);
lean_dec(v_m_829_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_879_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; uint64_t v___y_839_; 
v___x_837_ = lean_array_get_size(v_buckets_833_);
if (lean_obj_tag(v_a_830_) == 0)
{
uint64_t v___x_877_; 
v___x_877_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_839_ = v___x_877_;
goto v___jp_838_;
}
else
{
uint64_t v_hash_878_; 
v_hash_878_ = lean_ctor_get_uint64(v_a_830_, sizeof(void*)*2);
v___y_839_ = v_hash_878_;
goto v___jp_838_;
}
v___jp_838_:
{
uint64_t v___x_840_; uint64_t v___x_841_; uint64_t v_fold_842_; uint64_t v___x_843_; uint64_t v___x_844_; uint64_t v___x_845_; size_t v___x_846_; size_t v___x_847_; size_t v___x_848_; size_t v___x_849_; size_t v___x_850_; lean_object* v_bkt_851_; uint8_t v___x_852_; 
v___x_840_ = 32ULL;
v___x_841_ = lean_uint64_shift_right(v___y_839_, v___x_840_);
v_fold_842_ = lean_uint64_xor(v___y_839_, v___x_841_);
v___x_843_ = 16ULL;
v___x_844_ = lean_uint64_shift_right(v_fold_842_, v___x_843_);
v___x_845_ = lean_uint64_xor(v_fold_842_, v___x_844_);
v___x_846_ = lean_uint64_to_usize(v___x_845_);
v___x_847_ = lean_usize_of_nat(v___x_837_);
v___x_848_ = ((size_t)1ULL);
v___x_849_ = lean_usize_sub(v___x_847_, v___x_848_);
v___x_850_ = lean_usize_land(v___x_846_, v___x_849_);
v_bkt_851_ = lean_array_uget_borrowed(v_buckets_833_, v___x_850_);
v___x_852_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_830_, v_bkt_851_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; lean_object* v_size_x27_854_; lean_object* v___x_855_; lean_object* v_buckets_x27_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_853_ = lean_unsigned_to_nat(1u);
v_size_x27_854_ = lean_nat_add(v_size_832_, v___x_853_);
lean_dec(v_size_832_);
lean_inc(v_bkt_851_);
v___x_855_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_855_, 0, v_a_830_);
lean_ctor_set(v___x_855_, 1, v_b_831_);
lean_ctor_set(v___x_855_, 2, v_bkt_851_);
v_buckets_x27_856_ = lean_array_uset(v_buckets_833_, v___x_850_, v___x_855_);
v___x_857_ = lean_unsigned_to_nat(4u);
v___x_858_ = lean_nat_mul(v_size_x27_854_, v___x_857_);
v___x_859_ = lean_unsigned_to_nat(3u);
v___x_860_ = lean_nat_div(v___x_858_, v___x_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_array_get_size(v_buckets_x27_856_);
v___x_862_ = lean_nat_dec_le(v___x_860_, v___x_861_);
lean_dec(v___x_860_);
if (v___x_862_ == 0)
{
lean_object* v_val_863_; lean_object* v___x_865_; 
v_val_863_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_buckets_x27_856_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v_val_863_);
lean_ctor_set(v___x_835_, 0, v_size_x27_854_);
v___x_865_ = v___x_835_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_size_x27_854_);
lean_ctor_set(v_reuseFailAlloc_866_, 1, v_val_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
else
{
lean_object* v___x_868_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v_buckets_x27_856_);
lean_ctor_set(v___x_835_, 0, v_size_x27_854_);
v___x_868_ = v___x_835_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_size_x27_854_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v_buckets_x27_856_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
else
{
lean_object* v___x_870_; lean_object* v_buckets_x27_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_875_; 
lean_inc(v_bkt_851_);
v___x_870_ = lean_box(0);
v_buckets_x27_871_ = lean_array_uset(v_buckets_833_, v___x_850_, v___x_870_);
v___x_872_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_830_, v_b_831_, v_bkt_851_);
v___x_873_ = lean_array_uset(v_buckets_x27_871_, v___x_850_, v___x_872_);
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 1, v___x_873_);
v___x_875_ = v___x_835_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_size_832_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v___x_873_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__0));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(lean_object* v_as_883_, size_t v_sz_884_, size_t v_i_885_, lean_object* v_b_886_){
_start:
{
lean_object* v_a_889_; uint8_t v___x_893_; 
v___x_893_ = lean_usize_dec_lt(v_i_885_, v_sz_884_);
if (v___x_893_ == 0)
{
lean_object* v___x_894_; 
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v_b_886_);
return v___x_894_;
}
else
{
lean_object* v_a_895_; lean_object* v_fst_896_; lean_object* v_snd_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_913_; 
v_a_895_ = lean_array_uget(v_as_883_, v_i_885_);
v_fst_896_ = lean_ctor_get(v_a_895_, 0);
v_snd_897_ = lean_ctor_get(v_a_895_, 1);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_895_);
if (v_isSharedCheck_913_ == 0)
{
v___x_899_ = v_a_895_;
v_isShared_900_ = v_isSharedCheck_913_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_snd_897_);
lean_inc(v_fst_896_);
lean_dec(v_a_895_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_913_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v_val_902_; lean_object* v___x_904_; 
v___x_904_ = lean_task_get_own(v_snd_897_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_905_);
lean_dec_ref_known(v___x_904_, 1);
v___x_906_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___closed__1);
v___x_907_ = l_Lean_Exception_toMessageData(v_a_905_);
if (v_isShared_900_ == 0)
{
lean_ctor_set_tag(v___x_899_, 7);
lean_ctor_set(v___x_899_, 1, v___x_907_);
lean_ctor_set(v___x_899_, 0, v___x_906_);
v___x_909_ = v___x_899_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
v_val_902_ = v___x_909_;
goto v___jp_901_;
}
}
else
{
lean_object* v_a_911_; 
lean_del_object(v___x_899_);
v_a_911_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_904_, 1);
if (lean_obj_tag(v_a_911_) == 1)
{
lean_object* v_val_912_; 
v_val_912_ = lean_ctor_get(v_a_911_, 0);
lean_inc(v_val_912_);
lean_dec_ref_known(v_a_911_, 1);
v_val_902_ = v_val_912_;
goto v___jp_901_;
}
else
{
lean_dec(v_a_911_);
lean_dec(v_fst_896_);
v_a_889_ = v_b_886_;
goto v___jp_888_;
}
}
v___jp_901_:
{
lean_object* v___x_903_; 
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_886_, v_fst_896_, v_val_902_);
v_a_889_ = v___x_903_;
goto v___jp_888_;
}
}
}
v___jp_888_:
{
size_t v___x_890_; size_t v___x_891_; 
v___x_890_ = ((size_t)1ULL);
v___x_891_ = lean_usize_add(v_i_885_, v___x_890_);
v_i_885_ = v___x_891_;
v_b_886_ = v_a_889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg___boxed(lean_object* v_as_914_, lean_object* v_sz_915_, lean_object* v_i_916_, lean_object* v_b_917_, lean_object* v___y_918_){
_start:
{
size_t v_sz_boxed_919_; size_t v_i_boxed_920_; lean_object* v_res_921_; 
v_sz_boxed_919_ = lean_unbox_usize(v_sz_915_);
lean_dec(v_sz_915_);
v_i_boxed_920_ = lean_unbox_usize(v_i_916_);
lean_dec(v_i_916_);
v_res_921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_914_, v_sz_boxed_919_, v_i_boxed_920_, v_b_917_);
lean_dec_ref(v_as_914_);
return v_res_921_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_box(0);
v___x_923_ = lean_unsigned_to_nat(16u);
v___x_924_ = lean_mk_array(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___x_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(size_t v_sz_928_, size_t v_i_929_, lean_object* v_bs_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; 
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v_bs_930_);
return v___x_935_;
}
else
{
lean_object* v_v_936_; lean_object* v_fst_937_; lean_object* v_snd_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_964_; 
v_v_936_ = lean_array_uget(v_bs_930_, v_i_929_);
v_fst_937_ = lean_ctor_get(v_v_936_, 0);
v_snd_938_ = lean_ctor_get(v_v_936_, 1);
v_isSharedCheck_964_ = !lean_is_exclusive(v_v_936_);
if (v_isSharedCheck_964_ == 0)
{
v___x_940_ = v_v_936_;
v_isShared_941_ = v_isSharedCheck_964_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_snd_938_);
lean_inc(v_fst_937_);
lean_dec(v_v_936_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_964_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; size_t v_sz_944_; size_t v___x_945_; lean_object* v___x_946_; 
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v_sz_944_ = lean_array_size(v_snd_938_);
v___x_945_ = ((size_t)0ULL);
v___x_946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_snd_938_, v_sz_944_, v___x_945_, v___x_943_);
lean_dec(v_snd_938_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v_bs_x27_948_; lean_object* v___x_950_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v_bs_x27_948_ = lean_array_uset(v_bs_930_, v_i_929_, v___x_942_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 1, v_a_947_);
v___x_950_ = v___x_940_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_fst_937_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_a_947_);
v___x_950_ = v_reuseFailAlloc_955_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_929_, v___x_951_);
v___x_953_ = lean_array_uset(v_bs_x27_948_, v_i_929_, v___x_950_);
v_i_929_ = v___x_952_;
v_bs_930_ = v___x_953_;
goto _start;
}
}
else
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_963_; 
lean_del_object(v___x_940_);
lean_dec(v_fst_937_);
lean_dec_ref(v_bs_930_);
v_a_956_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_963_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_963_ == 0)
{
v___x_958_ = v___x_946_;
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_946_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_963_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_961_; 
if (v_isShared_959_ == 0)
{
v___x_961_ = v___x_958_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___boxed(lean_object* v_sz_965_, lean_object* v_i_966_, lean_object* v_bs_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
size_t v_sz_boxed_971_; size_t v_i_boxed_972_; lean_object* v_res_973_; 
v_sz_boxed_971_ = lean_unbox_usize(v_sz_965_);
lean_dec(v_sz_965_);
v_i_boxed_972_ = lean_unbox_usize(v_i_966_);
lean_dec(v_i_966_);
v_res_973_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(v_sz_boxed_971_, v_i_boxed_972_, v_bs_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore(lean_object* v_decls_974_, lean_object* v_linters_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
size_t v_sz_979_; size_t v___x_980_; lean_object* v___x_981_; 
v_sz_979_ = lean_array_size(v_linters_975_);
v___x_980_ = ((size_t)0ULL);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__5(v_decls_974_, v_sz_979_, v___x_980_, v_linters_975_, v_a_976_, v_a_977_);
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; size_t v_sz_983_; lean_object* v___x_984_; 
v_a_982_ = lean_ctor_get(v___x_981_, 0);
lean_inc(v_a_982_);
lean_dec_ref_known(v___x_981_, 1);
v_sz_983_ = lean_array_size(v_a_982_);
v___x_984_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6(v_sz_983_, v___x_980_, v_a_982_, v_a_976_, v_a_977_);
return v___x_984_;
}
else
{
lean_object* v_a_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_992_; 
v_a_985_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_992_ == 0)
{
v___x_987_ = v___x_981_;
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_a_985_);
lean_dec(v___x_981_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_992_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_990_; 
if (v_isShared_988_ == 0)
{
v___x_990_ = v___x_987_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_lintCore___boxed(lean_object* v_decls_993_, lean_object* v_linters_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Linter_EnvLinter_lintCore(v_decls_993_, v_linters_994_, v_a_995_, v_a_996_);
lean_dec(v_a_996_);
lean_dec_ref(v_a_995_);
lean_dec_ref(v_decls_993_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0(lean_object* v_00_u03b2_999_, lean_object* v_m_1000_, lean_object* v_a_1001_, lean_object* v_b_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_m_1000_, v_a_1001_, v_b_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(lean_object* v_as_1004_, size_t v_sz_1005_, size_t v_i_1006_, lean_object* v_b_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___redArg(v_as_1004_, v_sz_1005_, v_i_1006_, v_b_1007_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1___boxed(lean_object* v_as_1012_, lean_object* v_sz_1013_, lean_object* v_i_1014_, lean_object* v_b_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
size_t v_sz_boxed_1019_; size_t v_i_boxed_1020_; lean_object* v_res_1021_; 
v_sz_boxed_1019_ = lean_unbox_usize(v_sz_1013_);
lean_dec(v_sz_1013_);
v_i_boxed_1020_ = lean_unbox_usize(v_i_1014_);
lean_dec(v_i_1014_);
v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_lintCore_spec__1(v_as_1012_, v_sz_boxed_1019_, v_i_boxed_1020_, v_b_1015_, v___y_1016_, v___y_1017_);
lean_dec(v___y_1017_);
lean_dec_ref(v___y_1016_);
lean_dec_ref(v_as_1012_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3(lean_object* v_linter_1022_, lean_object* v_decl_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg(v_linter_1022_, v_decl_1023_, v___y_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___boxed(lean_object* v_linter_1028_, lean_object* v_decl_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3(v_linter_1028_, v_decl_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v_linter_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(lean_object* v_00_u03b2_1034_, lean_object* v_a_1035_, lean_object* v_x_1036_){
_start:
{
uint8_t v___x_1037_; 
v___x_1037_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___redArg(v_a_1035_, v_x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1038_, lean_object* v_a_1039_, lean_object* v_x_1040_){
_start:
{
uint8_t v_res_1041_; lean_object* v_r_1042_; 
v_res_1041_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__0(v_00_u03b2_1038_, v_a_1039_, v_x_1040_);
lean_dec(v_x_1040_);
lean_dec(v_a_1039_);
v_r_1042_ = lean_box(v_res_1041_);
return v_r_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1(lean_object* v_00_u03b2_1043_, lean_object* v_data_1044_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1___redArg(v_data_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2(lean_object* v_00_u03b2_1046_, lean_object* v_a_1047_, lean_object* v_b_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__2___redArg(v_a_1047_, v_b_1048_, v_x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_1051_, lean_object* v_i_1052_, lean_object* v_source_1053_, lean_object* v_target_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2___redArg(v_i_1052_, v_source_1053_, v_target_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9(lean_object* v_00_u03b2_1056_, lean_object* v_x_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg(v_x_1057_, v_x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(lean_object* v_a_1060_, lean_object* v_fallback_1061_, lean_object* v_x_1062_){
_start:
{
if (lean_obj_tag(v_x_1062_) == 0)
{
lean_inc(v_fallback_1061_);
return v_fallback_1061_;
}
else
{
lean_object* v_key_1063_; lean_object* v_value_1064_; lean_object* v_tail_1065_; uint8_t v___x_1066_; 
v_key_1063_ = lean_ctor_get(v_x_1062_, 0);
v_value_1064_ = lean_ctor_get(v_x_1062_, 1);
v_tail_1065_ = lean_ctor_get(v_x_1062_, 2);
v___x_1066_ = lean_name_eq(v_key_1063_, v_a_1060_);
if (v___x_1066_ == 0)
{
v_x_1062_ = v_tail_1065_;
goto _start;
}
else
{
lean_inc(v_value_1064_);
return v_value_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg___boxed(lean_object* v_a_1068_, lean_object* v_fallback_1069_, lean_object* v_x_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_1068_, v_fallback_1069_, v_x_1070_);
lean_dec(v_x_1070_);
lean_dec(v_fallback_1069_);
lean_dec(v_a_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(lean_object* v_m_1072_, lean_object* v_a_1073_, lean_object* v_fallback_1074_){
_start:
{
lean_object* v_buckets_1075_; lean_object* v___x_1076_; uint64_t v___y_1078_; 
v_buckets_1075_ = lean_ctor_get(v_m_1072_, 1);
v___x_1076_ = lean_array_get_size(v_buckets_1075_);
if (lean_obj_tag(v_a_1073_) == 0)
{
uint64_t v___x_1092_; 
v___x_1092_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_1078_ = v___x_1092_;
goto v___jp_1077_;
}
else
{
uint64_t v_hash_1093_; 
v_hash_1093_ = lean_ctor_get_uint64(v_a_1073_, sizeof(void*)*2);
v___y_1078_ = v_hash_1093_;
goto v___jp_1077_;
}
v___jp_1077_:
{
uint64_t v___x_1079_; uint64_t v___x_1080_; uint64_t v_fold_1081_; uint64_t v___x_1082_; uint64_t v___x_1083_; uint64_t v___x_1084_; size_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1079_ = 32ULL;
v___x_1080_ = lean_uint64_shift_right(v___y_1078_, v___x_1079_);
v_fold_1081_ = lean_uint64_xor(v___y_1078_, v___x_1080_);
v___x_1082_ = 16ULL;
v___x_1083_ = lean_uint64_shift_right(v_fold_1081_, v___x_1082_);
v___x_1084_ = lean_uint64_xor(v_fold_1081_, v___x_1083_);
v___x_1085_ = lean_uint64_to_usize(v___x_1084_);
v___x_1086_ = lean_usize_of_nat(v___x_1076_);
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_sub(v___x_1086_, v___x_1087_);
v___x_1089_ = lean_usize_land(v___x_1085_, v___x_1088_);
v___x_1090_ = lean_array_uget_borrowed(v_buckets_1075_, v___x_1089_);
v___x_1091_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_1073_, v_fallback_1074_, v___x_1090_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg___boxed(lean_object* v_m_1094_, lean_object* v_a_1095_, lean_object* v_fallback_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_1094_, v_a_1095_, v_fallback_1096_);
lean_dec(v_fallback_1096_);
lean_dec(v_a_1095_);
lean_dec_ref(v_m_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(lean_object* v_a_1098_, lean_object* v_hi_1099_, lean_object* v_pivot_1100_, lean_object* v_as_1101_, lean_object* v_i_1102_, lean_object* v_k_1103_){
_start:
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_nat_dec_lt(v_k_1103_, v_hi_1099_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
lean_dec(v_k_1103_);
v___x_1105_ = lean_array_fswap(v_as_1101_, v_i_1102_, v_hi_1099_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_i_1102_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; lean_object* v_fst_1108_; lean_object* v_fst_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1107_ = lean_array_fget_borrowed(v_as_1101_, v_k_1103_);
v_fst_1108_ = lean_ctor_get(v___x_1107_, 0);
v_fst_1109_ = lean_ctor_get(v_pivot_1100_, 0);
v___x_1110_ = lean_unsigned_to_nat(0u);
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_1098_, v_fst_1108_, v___x_1110_);
v___x_1112_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_1098_, v_fst_1109_, v___x_1110_);
v___x_1113_ = lean_nat_dec_lt(v___x_1111_, v___x_1112_);
lean_dec(v___x_1112_);
lean_dec(v___x_1111_);
if (v___x_1113_ == 0)
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_unsigned_to_nat(1u);
v___x_1115_ = lean_nat_add(v_k_1103_, v___x_1114_);
lean_dec(v_k_1103_);
v_k_1103_ = v___x_1115_;
goto _start;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1117_ = lean_array_fswap(v_as_1101_, v_i_1102_, v_k_1103_);
v___x_1118_ = lean_unsigned_to_nat(1u);
v___x_1119_ = lean_nat_add(v_i_1102_, v___x_1118_);
lean_dec(v_i_1102_);
v___x_1120_ = lean_nat_add(v_k_1103_, v___x_1118_);
lean_dec(v_k_1103_);
v_as_1101_ = v___x_1117_;
v_i_1102_ = v___x_1119_;
v_k_1103_ = v___x_1120_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg___boxed(lean_object* v_a_1122_, lean_object* v_hi_1123_, lean_object* v_pivot_1124_, lean_object* v_as_1125_, lean_object* v_i_1126_, lean_object* v_k_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_1122_, v_hi_1123_, v_pivot_1124_, v_as_1125_, v_i_1126_, v_k_1127_);
lean_dec_ref(v_pivot_1124_);
lean_dec(v_hi_1123_);
lean_dec_ref(v_a_1122_);
return v_res_1128_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(lean_object* v_a_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_){
_start:
{
lean_object* v_fst_1132_; lean_object* v_fst_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_fst_1132_ = lean_ctor_get(v_x_1130_, 0);
v_fst_1133_ = lean_ctor_get(v_x_1131_, 0);
v___x_1134_ = lean_unsigned_to_nat(0u);
v___x_1135_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_1129_, v_fst_1132_, v___x_1134_);
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_a_1129_, v_fst_1133_, v___x_1134_);
v___x_1137_ = lean_nat_dec_lt(v___x_1135_, v___x_1136_);
lean_dec(v___x_1136_);
lean_dec(v___x_1135_);
return v___x_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0___boxed(lean_object* v_a_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_){
_start:
{
uint8_t v_res_1141_; lean_object* v_r_1142_; 
v_res_1141_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1138_, v_x_1139_, v_x_1140_);
lean_dec_ref(v_x_1140_);
lean_dec_ref(v_x_1139_);
lean_dec_ref(v_a_1138_);
v_r_1142_ = lean_box(v_res_1141_);
return v_r_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(lean_object* v_a_1143_, lean_object* v_n_1144_, lean_object* v_as_1145_, lean_object* v_lo_1146_, lean_object* v_hi_1147_){
_start:
{
lean_object* v___y_1149_; uint8_t v___x_1159_; 
v___x_1159_ = lean_nat_dec_lt(v_lo_1146_, v_hi_1147_);
if (v___x_1159_ == 0)
{
lean_dec(v_lo_1146_);
return v_as_1145_;
}
else
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v_mid_1162_; lean_object* v___y_1164_; lean_object* v___y_1170_; lean_object* v___x_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1160_ = lean_nat_add(v_lo_1146_, v_hi_1147_);
v___x_1161_ = lean_unsigned_to_nat(1u);
v_mid_1162_ = lean_nat_shiftr(v___x_1160_, v___x_1161_);
lean_dec(v___x_1160_);
v___x_1175_ = lean_array_fget_borrowed(v_as_1145_, v_mid_1162_);
v___x_1176_ = lean_array_fget_borrowed(v_as_1145_, v_lo_1146_);
v___x_1177_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1143_, v___x_1175_, v___x_1176_);
if (v___x_1177_ == 0)
{
v___y_1170_ = v_as_1145_;
goto v___jp_1169_;
}
else
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_array_fswap(v_as_1145_, v_lo_1146_, v_mid_1162_);
v___y_1170_ = v___x_1178_;
goto v___jp_1169_;
}
v___jp_1163_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v___x_1165_ = lean_array_fget_borrowed(v___y_1164_, v_mid_1162_);
v___x_1166_ = lean_array_fget_borrowed(v___y_1164_, v_hi_1147_);
v___x_1167_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1143_, v___x_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_dec(v_mid_1162_);
v___y_1149_ = v___y_1164_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_array_fswap(v___y_1164_, v_mid_1162_, v_hi_1147_);
lean_dec(v_mid_1162_);
v___y_1149_ = v___x_1168_;
goto v___jp_1148_;
}
}
v___jp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v___x_1171_ = lean_array_fget_borrowed(v___y_1170_, v_hi_1147_);
v___x_1172_ = lean_array_fget_borrowed(v___y_1170_, v_lo_1146_);
v___x_1173_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___lam__0(v_a_1143_, v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
v___y_1164_ = v___y_1170_;
goto v___jp_1163_;
}
else
{
lean_object* v___x_1174_; 
v___x_1174_ = lean_array_fswap(v___y_1170_, v_lo_1146_, v_hi_1147_);
v___y_1164_ = v___x_1174_;
goto v___jp_1163_;
}
}
}
v___jp_1148_:
{
lean_object* v_pivot_1150_; lean_object* v___x_1151_; lean_object* v_fst_1152_; lean_object* v_snd_1153_; uint8_t v___x_1154_; 
v_pivot_1150_ = lean_array_fget(v___y_1149_, v_hi_1147_);
lean_inc_n(v_lo_1146_, 2);
v___x_1151_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_1143_, v_hi_1147_, v_pivot_1150_, v___y_1149_, v_lo_1146_, v_lo_1146_);
lean_dec(v_pivot_1150_);
v_fst_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_fst_1152_);
v_snd_1153_ = lean_ctor_get(v___x_1151_, 1);
lean_inc(v_snd_1153_);
lean_dec_ref(v___x_1151_);
v___x_1154_ = lean_nat_dec_le(v_hi_1147_, v_fst_1152_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1143_, v_n_1144_, v_snd_1153_, v_lo_1146_, v_fst_1152_);
v___x_1156_ = lean_unsigned_to_nat(1u);
v___x_1157_ = lean_nat_add(v_fst_1152_, v___x_1156_);
lean_dec(v_fst_1152_);
v_as_1145_ = v___x_1155_;
v_lo_1146_ = v___x_1157_;
goto _start;
}
else
{
lean_dec(v_fst_1152_);
lean_dec(v_lo_1146_);
return v_snd_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg___boxed(lean_object* v_a_1179_, lean_object* v_n_1180_, lean_object* v_as_1181_, lean_object* v_lo_1182_, lean_object* v_hi_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1179_, v_n_1180_, v_as_1181_, v_lo_1182_, v_hi_1183_);
lean_dec(v_hi_1183_);
lean_dec(v_n_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(lean_object* v_declName_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v_env_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1188_ = lean_st_ref_get(v___y_1186_);
v_env_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc_ref(v_env_1189_);
lean_dec(v___x_1188_);
v___x_1190_ = l_Lean_isRecCore(v_env_1189_, v_declName_1185_);
v___x_1191_ = lean_box(v___x_1190_);
v___x_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1193_, v___y_1194_);
lean_dec(v___y_1194_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(lean_object* v_declName_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; lean_object* v_env_1201_; lean_object* v___x_1202_; lean_object* v_env_1203_; lean_object* v___x_1204_; lean_object* v_toEnvExtension_1205_; lean_object* v_asyncMode_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1200_ = lean_st_ref_get(v___y_1198_);
v_env_1201_ = lean_ctor_get(v___x_1200_, 0);
lean_inc_ref(v_env_1201_);
lean_dec(v___x_1200_);
v___x_1202_ = lean_st_ref_get(v___y_1198_);
v_env_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc_ref(v_env_1203_);
lean_dec(v___x_1202_);
v___x_1204_ = l_Lean_declRangeExt;
v_toEnvExtension_1205_ = lean_ctor_get(v___x_1204_, 0);
v_asyncMode_1206_ = lean_ctor_get(v_toEnvExtension_1205_, 2);
v___x_1207_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1208_ = 0;
lean_inc(v_declName_1197_);
v___x_1209_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1207_, v___x_1204_, v_env_1201_, v_declName_1197_, v_asyncMode_1206_, v___x_1208_);
if (lean_obj_tag(v___x_1209_) == 0)
{
uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1210_ = 1;
v___x_1211_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_1207_, v___x_1204_, v_env_1203_, v_declName_1197_, v_asyncMode_1206_, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
else
{
lean_object* v___x_1213_; 
lean_dec_ref(v_env_1203_);
lean_dec(v_declName_1197_);
v___x_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1209_);
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg___boxed(lean_object* v_declName_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1214_, v___y_1215_);
lean_dec(v___y_1215_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(lean_object* v_declName_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_ranges_1223_; lean_object* v___x_1229_; lean_object* v_env_1230_; lean_object* v___x_1231_; lean_object* v_a_1232_; uint8_t v___y_1238_; uint8_t v___x_1242_; 
v___x_1229_ = lean_st_ref_get(v___y_1220_);
v_env_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc_ref_n(v_env_1230_, 2);
lean_dec(v___x_1229_);
lean_inc_n(v_declName_1218_, 2);
v___x_1231_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1218_, v___y_1220_);
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref(v___x_1231_);
v___x_1242_ = l_Lean_isAuxRecursor(v_env_1230_, v_declName_1218_);
if (v___x_1242_ == 0)
{
uint8_t v___x_1243_; 
lean_inc(v_declName_1218_);
v___x_1243_ = l_Lean_isNoConfusion(v_env_1230_, v_declName_1218_);
v___y_1238_ = v___x_1243_;
goto v___jp_1237_;
}
else
{
lean_dec_ref(v_env_1230_);
v___y_1238_ = v___x_1242_;
goto v___jp_1237_;
}
v___jp_1222_:
{
if (lean_obj_tag(v_ranges_1223_) == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1224_ = l_Lean_builtinDeclRanges;
v___x_1225_ = lean_st_ref_get(v___x_1224_);
v___x_1226_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_1225_, v_declName_1218_);
lean_dec(v_declName_1218_);
lean_dec(v___x_1225_);
v___x_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
return v___x_1227_;
}
else
{
lean_object* v___x_1228_; 
lean_dec(v_declName_1218_);
v___x_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1228_, 0, v_ranges_1223_);
return v___x_1228_;
}
}
v___jp_1233_:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v_a_1236_; 
v___x_1234_ = l_Lean_Name_getPrefix(v_declName_1218_);
v___x_1235_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v___x_1234_, v___y_1220_);
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
lean_inc(v_a_1236_);
lean_dec_ref(v___x_1235_);
v_ranges_1223_ = v_a_1236_;
goto v___jp_1222_;
}
v___jp_1237_:
{
if (v___y_1238_ == 0)
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_unbox(v_a_1232_);
lean_dec(v_a_1232_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v_a_1241_; 
lean_inc(v_declName_1218_);
v___x_1240_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1218_, v___y_1220_);
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1240_);
v_ranges_1223_ = v_a_1241_;
goto v___jp_1222_;
}
else
{
goto v___jp_1233_;
}
}
else
{
lean_dec(v_a_1232_);
goto v___jp_1233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0___boxed(lean_object* v_declName_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(lean_object* v_as_1249_, size_t v_sz_1250_, size_t v_i_1251_, lean_object* v_b_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_usize_dec_lt(v_i_1251_, v_sz_1250_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_b_1252_);
return v___x_1257_;
}
else
{
lean_object* v_a_1258_; lean_object* v_fst_1259_; lean_object* v___x_1260_; 
v_a_1258_ = lean_array_uget_borrowed(v_as_1249_, v_i_1251_);
v_fst_1259_ = lean_ctor_get(v_a_1258_, 0);
lean_inc(v_fst_1259_);
v___x_1260_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_fst_1259_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v_a_1263_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
if (lean_obj_tag(v_a_1261_) == 1)
{
lean_object* v_val_1267_; lean_object* v_range_1268_; lean_object* v_pos_1269_; lean_object* v_line_1270_; lean_object* v___x_1271_; 
v_val_1267_ = lean_ctor_get(v_a_1261_, 0);
lean_inc(v_val_1267_);
lean_dec_ref_known(v_a_1261_, 1);
v_range_1268_ = lean_ctor_get(v_val_1267_, 0);
lean_inc_ref(v_range_1268_);
lean_dec(v_val_1267_);
v_pos_1269_ = lean_ctor_get(v_range_1268_, 0);
lean_inc_ref(v_pos_1269_);
lean_dec_ref(v_range_1268_);
v_line_1270_ = lean_ctor_get(v_pos_1269_, 0);
lean_inc(v_line_1270_);
lean_dec_ref(v_pos_1269_);
lean_inc(v_fst_1259_);
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_b_1252_, v_fst_1259_, v_line_1270_);
v_a_1263_ = v___x_1271_;
goto v___jp_1262_;
}
else
{
lean_dec(v_a_1261_);
v_a_1263_ = v_b_1252_;
goto v___jp_1262_;
}
v___jp_1262_:
{
size_t v___x_1264_; size_t v___x_1265_; 
v___x_1264_ = ((size_t)1ULL);
v___x_1265_ = lean_usize_add(v_i_1251_, v___x_1264_);
v_i_1251_ = v___x_1265_;
v_b_1252_ = v_a_1263_;
goto _start;
}
}
else
{
lean_object* v_a_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1279_; 
lean_dec_ref(v_b_1252_);
v_a_1272_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1274_ = v___x_1260_;
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_a_1272_);
lean_dec(v___x_1260_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1279_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1277_; 
if (v_isShared_1275_ == 0)
{
v___x_1277_ = v___x_1274_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg___boxed(lean_object* v_as_1280_, lean_object* v_sz_1281_, lean_object* v_i_1282_, lean_object* v_b_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
size_t v_sz_boxed_1287_; size_t v_i_boxed_1288_; lean_object* v_res_1289_; 
v_sz_boxed_1287_ = lean_unbox_usize(v_sz_1281_);
lean_dec(v_sz_1281_);
v_i_boxed_1288_ = lean_unbox_usize(v_i_1282_);
lean_dec(v_i_1282_);
v_res_1289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_1280_, v_sz_boxed_1287_, v_i_boxed_1288_, v_b_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec_ref(v_as_1280_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1291_) == 0)
{
return v_x_1290_;
}
else
{
lean_object* v_key_1292_; lean_object* v_value_1293_; lean_object* v_tail_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
v_key_1292_ = lean_ctor_get(v_x_1291_, 0);
v_value_1293_ = lean_ctor_get(v_x_1291_, 1);
v_tail_1294_ = lean_ctor_get(v_x_1291_, 2);
lean_inc(v_value_1293_);
lean_inc(v_key_1292_);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_key_1292_);
lean_ctor_set(v___x_1295_, 1, v_value_1293_);
v___x_1296_ = lean_array_push(v_x_1290_, v___x_1295_);
v_x_1290_ = v___x_1296_;
v_x_1291_ = v_tail_1294_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg___boxed(lean_object* v_x_1298_, lean_object* v_x_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_1298_, v_x_1299_);
lean_dec(v_x_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(lean_object* v_as_1301_, size_t v_i_1302_, size_t v_stop_1303_, lean_object* v_b_1304_){
_start:
{
uint8_t v___x_1305_; 
v___x_1305_ = lean_usize_dec_eq(v_i_1302_, v_stop_1303_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1307_; size_t v___x_1308_; size_t v___x_1309_; 
v___x_1306_ = lean_array_uget_borrowed(v_as_1301_, v_i_1302_);
v___x_1307_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_b_1304_, v___x_1306_);
v___x_1308_ = ((size_t)1ULL);
v___x_1309_ = lean_usize_add(v_i_1302_, v___x_1308_);
v_i_1302_ = v___x_1309_;
v_b_1304_ = v___x_1307_;
goto _start;
}
else
{
return v_b_1304_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg___boxed(lean_object* v_as_1311_, lean_object* v_i_1312_, lean_object* v_stop_1313_, lean_object* v_b_1314_){
_start:
{
size_t v_i_boxed_1315_; size_t v_stop_boxed_1316_; lean_object* v_res_1317_; 
v_i_boxed_1315_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_stop_boxed_1316_ = lean_unbox_usize(v_stop_1313_);
lean_dec(v_stop_1313_);
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_1311_, v_i_boxed_1315_, v_stop_boxed_1316_, v_b_1314_);
lean_dec_ref(v_as_1311_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg(lean_object* v_results_1318_, lean_object* v_a_1319_, lean_object* v_a_1320_){
_start:
{
lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v_size_1337_; lean_object* v_buckets_1338_; lean_object* v___x_1339_; lean_object* v_key_1340_; lean_object* v___y_1342_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_size_1337_ = lean_ctor_get(v_results_1318_, 0);
v_buckets_1338_ = lean_ctor_get(v_results_1318_, 1);
v___x_1339_ = lean_unsigned_to_nat(0u);
v_key_1340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v___x_1367_ = lean_mk_empty_array_with_capacity(v_size_1337_);
v___x_1368_ = lean_array_get_size(v_buckets_1338_);
v___x_1369_ = lean_nat_dec_lt(v___x_1339_, v___x_1368_);
if (v___x_1369_ == 0)
{
v___y_1342_ = v___x_1367_;
goto v___jp_1341_;
}
else
{
uint8_t v___x_1370_; 
v___x_1370_ = lean_nat_dec_le(v___x_1368_, v___x_1368_);
if (v___x_1370_ == 0)
{
if (v___x_1369_ == 0)
{
v___y_1342_ = v___x_1367_;
goto v___jp_1341_;
}
else
{
size_t v___x_1371_; size_t v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = ((size_t)0ULL);
v___x_1372_ = lean_usize_of_nat(v___x_1368_);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_1338_, v___x_1371_, v___x_1372_, v___x_1367_);
v___y_1342_ = v___x_1373_;
goto v___jp_1341_;
}
}
else
{
size_t v___x_1374_; size_t v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = ((size_t)0ULL);
v___x_1375_ = lean_usize_of_nat(v___x_1368_);
v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_buckets_1338_, v___x_1374_, v___x_1375_, v___x_1367_);
v___y_1342_ = v___x_1376_;
goto v___jp_1341_;
}
}
v___jp_1322_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v___y_1325_, v___y_1324_, v___y_1326_, v___y_1323_, v___y_1327_);
lean_dec(v___y_1327_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1325_);
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
return v___x_1329_;
}
v___jp_1330_:
{
uint8_t v___x_1336_; 
v___x_1336_ = lean_nat_dec_le(v___y_1335_, v___y_1332_);
if (v___x_1336_ == 0)
{
lean_dec(v___y_1332_);
lean_inc(v___y_1335_);
v___y_1323_ = v___y_1335_;
v___y_1324_ = v___y_1331_;
v___y_1325_ = v___y_1333_;
v___y_1326_ = v___y_1334_;
v___y_1327_ = v___y_1335_;
goto v___jp_1322_;
}
else
{
v___y_1323_ = v___y_1335_;
v___y_1324_ = v___y_1331_;
v___y_1325_ = v___y_1333_;
v___y_1326_ = v___y_1334_;
v___y_1327_ = v___y_1332_;
goto v___jp_1322_;
}
}
v___jp_1341_:
{
size_t v_sz_1343_; size_t v___x_1344_; lean_object* v___x_1345_; 
v_sz_1343_ = lean_array_size(v___y_1342_);
v___x_1344_ = ((size_t)0ULL);
v___x_1345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v___y_1342_, v_sz_1343_, v___x_1344_, v_key_1340_, v_a_1319_, v_a_1320_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1358_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1358_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1358_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = lean_array_get_size(v___y_1342_);
v___x_1351_ = lean_nat_dec_eq(v___x_1350_, v___x_1339_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; uint8_t v___x_1354_; 
lean_del_object(v___x_1348_);
v___x_1352_ = lean_unsigned_to_nat(1u);
v___x_1353_ = lean_nat_sub(v___x_1350_, v___x_1352_);
v___x_1354_ = lean_nat_dec_le(v___x_1339_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_inc(v___x_1353_);
v___y_1331_ = v___x_1350_;
v___y_1332_ = v___x_1353_;
v___y_1333_ = v_a_1346_;
v___y_1334_ = v___y_1342_;
v___y_1335_ = v___x_1353_;
goto v___jp_1330_;
}
else
{
v___y_1331_ = v___x_1350_;
v___y_1332_ = v___x_1353_;
v___y_1333_ = v_a_1346_;
v___y_1334_ = v___y_1342_;
v___y_1335_ = v___x_1339_;
goto v___jp_1330_;
}
}
else
{
lean_object* v___x_1356_; 
lean_dec(v_a_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___y_1342_);
v___x_1356_ = v___x_1348_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___y_1342_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec_ref(v___y_1342_);
v_a_1359_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1345_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1345_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___redArg___boxed(lean_object* v_results_1377_, lean_object* v_a_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1377_, v_a_1378_, v_a_1379_);
lean_dec(v_a_1379_);
lean_dec_ref(v_a_1378_);
lean_dec_ref(v_results_1377_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults(lean_object* v_00_u03b1_1382_, lean_object* v_results_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_1383_, v_a_1384_, v_a_1385_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_sortResults___boxed(lean_object* v_00_u03b1_1388_, lean_object* v_results_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_Linter_EnvLinter_sortResults(v_00_u03b1_1388_, v_results_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
lean_dec_ref(v_results_1389_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(lean_object* v_declName_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___redArg(v_declName_1394_, v___y_1396_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0___boxed(lean_object* v_declName_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_isRec___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__0(v_declName_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(lean_object* v_declName_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___redArg(v_declName_1404_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1___boxed(lean_object* v_declName_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_Lean_findDeclarationRangesCore_x3f___at___00Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0_spec__1(v_declName_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(lean_object* v_00_u03b1_1414_, lean_object* v_as_1415_, size_t v_sz_1416_, size_t v_i_1417_, lean_object* v_b_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___redArg(v_as_1415_, v_sz_1416_, v_i_1417_, v_b_1418_, v___y_1419_, v___y_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1___boxed(lean_object* v_00_u03b1_1423_, lean_object* v_as_1424_, lean_object* v_sz_1425_, lean_object* v_i_1426_, lean_object* v_b_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
size_t v_sz_boxed_1431_; size_t v_i_boxed_1432_; lean_object* v_res_1433_; 
v_sz_boxed_1431_ = lean_unbox_usize(v_sz_1425_);
lean_dec(v_sz_1425_);
v_i_boxed_1432_ = lean_unbox_usize(v_i_1426_);
lean_dec(v_i_1426_);
v_res_1433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Linter_EnvLinter_sortResults_spec__1(v_00_u03b1_1423_, v_as_1424_, v_sz_boxed_1431_, v_i_boxed_1432_, v_b_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec_ref(v_as_1424_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(lean_object* v_00_u03b2_1434_, lean_object* v_m_1435_, lean_object* v_a_1436_, lean_object* v_fallback_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___redArg(v_m_1435_, v_a_1436_, v_fallback_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2___boxed(lean_object* v_00_u03b2_1439_, lean_object* v_m_1440_, lean_object* v_a_1441_, lean_object* v_fallback_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2(v_00_u03b2_1439_, v_m_1440_, v_a_1441_, v_fallback_1442_);
lean_dec(v_fallback_1442_);
lean_dec(v_a_1441_);
lean_dec_ref(v_m_1440_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(lean_object* v_00_u03b1_1444_, lean_object* v_a_1445_, lean_object* v_n_1446_, lean_object* v_as_1447_, lean_object* v_lo_1448_, lean_object* v_hi_1449_, lean_object* v_w_1450_, lean_object* v_hlo_1451_, lean_object* v_hhi_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___redArg(v_a_1445_, v_n_1446_, v_as_1447_, v_lo_1448_, v_hi_1449_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3___boxed(lean_object* v_00_u03b1_1454_, lean_object* v_a_1455_, lean_object* v_n_1456_, lean_object* v_as_1457_, lean_object* v_lo_1458_, lean_object* v_hi_1459_, lean_object* v_w_1460_, lean_object* v_hlo_1461_, lean_object* v_hhi_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3(v_00_u03b1_1454_, v_a_1455_, v_n_1456_, v_as_1457_, v_lo_1458_, v_hi_1459_, v_w_1460_, v_hlo_1461_, v_hhi_1462_);
lean_dec(v_hi_1459_);
lean_dec(v_n_1456_);
lean_dec_ref(v_a_1455_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(lean_object* v_00_u03b1_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___redArg(v_x_1465_, v_x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_x_1469_, lean_object* v_x_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_sortResults_spec__4(v_00_u03b1_1468_, v_x_1469_, v_x_1470_);
lean_dec(v_x_1470_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(lean_object* v_00_u03b1_1472_, lean_object* v_as_1473_, size_t v_i_1474_, size_t v_stop_1475_, lean_object* v_b_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___redArg(v_as_1473_, v_i_1474_, v_stop_1475_, v_b_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5___boxed(lean_object* v_00_u03b1_1478_, lean_object* v_as_1479_, lean_object* v_i_1480_, lean_object* v_stop_1481_, lean_object* v_b_1482_){
_start:
{
size_t v_i_boxed_1483_; size_t v_stop_boxed_1484_; lean_object* v_res_1485_; 
v_i_boxed_1483_ = lean_unbox_usize(v_i_1480_);
lean_dec(v_i_1480_);
v_stop_boxed_1484_ = lean_unbox_usize(v_stop_1481_);
lean_dec(v_stop_1481_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_sortResults_spec__5(v_00_u03b1_1478_, v_as_1479_, v_i_boxed_1483_, v_stop_boxed_1484_, v_b_1482_);
lean_dec_ref(v_as_1479_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(lean_object* v_00_u03b2_1486_, lean_object* v_a_1487_, lean_object* v_fallback_1488_, lean_object* v_x_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___redArg(v_a_1487_, v_fallback_1488_, v_x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4___boxed(lean_object* v_00_u03b2_1491_, lean_object* v_a_1492_, lean_object* v_fallback_1493_, lean_object* v_x_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Std_DHashMap_Internal_AssocList_getD___at___00Std_DHashMap_Internal_Raw_u2080_Const_getD___at___00Lean_Linter_EnvLinter_sortResults_spec__2_spec__4(v_00_u03b2_1491_, v_a_1492_, v_fallback_1493_, v_x_1494_);
lean_dec(v_x_1494_);
lean_dec(v_fallback_1493_);
lean_dec(v_a_1492_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(lean_object* v_00_u03b1_1496_, lean_object* v_a_1497_, lean_object* v_n_1498_, lean_object* v_lo_1499_, lean_object* v_hi_1500_, lean_object* v_hhi_1501_, lean_object* v_pivot_1502_, lean_object* v_as_1503_, lean_object* v_i_1504_, lean_object* v_k_1505_, lean_object* v_ilo_1506_, lean_object* v_ik_1507_, lean_object* v_w_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___redArg(v_a_1497_, v_hi_1500_, v_pivot_1502_, v_as_1503_, v_i_1504_, v_k_1505_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6___boxed(lean_object* v_00_u03b1_1510_, lean_object* v_a_1511_, lean_object* v_n_1512_, lean_object* v_lo_1513_, lean_object* v_hi_1514_, lean_object* v_hhi_1515_, lean_object* v_pivot_1516_, lean_object* v_as_1517_, lean_object* v_i_1518_, lean_object* v_k_1519_, lean_object* v_ilo_1520_, lean_object* v_ik_1521_, lean_object* v_w_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_sortResults_spec__3_spec__6(v_00_u03b1_1510_, v_a_1511_, v_n_1512_, v_lo_1513_, v_hi_1514_, v_hhi_1515_, v_pivot_1516_, v_as_1517_, v_i_1518_, v_k_1519_, v_ilo_1520_, v_ik_1521_, v_w_1522_);
lean_dec_ref(v_pivot_1516_);
lean_dec(v_hi_1514_);
lean_dec(v_lo_1513_);
lean_dec(v_n_1512_);
lean_dec_ref(v_a_1511_);
return v_res_1523_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_1525_ = lean_unsigned_to_nat(0u);
v___x_1526_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
lean_ctor_set(v___x_1526_, 2, v___x_1525_);
lean_ctor_set(v___x_1526_, 3, v___x_1525_);
lean_ctor_set(v___x_1526_, 4, v___x_1524_);
lean_ctor_set(v___x_1526_, 5, v___x_1524_);
lean_ctor_set(v___x_1526_, 6, v___x_1524_);
lean_ctor_set(v___x_1526_, 7, v___x_1524_);
lean_ctor_set(v___x_1526_, 8, v___x_1524_);
lean_ctor_set(v___x_1526_, 9, v___x_1524_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_unsigned_to_nat(32u);
v___x_1528_ = lean_mk_empty_array_with_capacity(v___x_1527_);
v___x_1529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2(void){
_start:
{
size_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1530_ = ((size_t)5ULL);
v___x_1531_ = lean_unsigned_to_nat(0u);
v___x_1532_ = lean_unsigned_to_nat(32u);
v___x_1533_ = lean_mk_empty_array_with_capacity(v___x_1532_);
v___x_1534_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__1);
v___x_1535_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v___x_1533_);
lean_ctor_set(v___x_1535_, 2, v___x_1531_);
lean_ctor_set(v___x_1535_, 3, v___x_1531_);
lean_ctor_set_usize(v___x_1535_, 4, v___x_1530_);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1536_ = lean_box(1);
v___x_1537_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__2);
v___x_1538_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__2___lam__0___closed__1);
v___x_1539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v___x_1537_);
lean_ctor_set(v___x_1539_, 2, v___x_1536_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(lean_object* v_msgData_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v_env_1545_; lean_object* v_options_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1544_ = lean_st_ref_get(v___y_1542_);
v_env_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc_ref(v_env_1545_);
lean_dec(v___x_1544_);
v_options_1546_ = lean_ctor_get(v___y_1541_, 2);
v___x_1547_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
v___x_1548_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
lean_inc_ref(v_options_1546_);
v___x_1549_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1549_, 0, v_env_1545_);
lean_ctor_set(v___x_1549_, 1, v___x_1547_);
lean_ctor_set(v___x_1549_, 2, v___x_1548_);
lean_ctor_set(v___x_1549_, 3, v_options_1546_);
v___x_1550_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v_msgData_1540_);
v___x_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___boxed(lean_object* v_msgData_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msgData_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
if (lean_obj_tag(v_a_1557_) == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = l_List_reverse___redArg(v_a_1558_);
return v___x_1559_;
}
else
{
lean_object* v_head_1560_; lean_object* v_tail_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1570_; 
v_head_1560_ = lean_ctor_get(v_a_1557_, 0);
v_tail_1561_ = lean_ctor_get(v_a_1557_, 1);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_a_1557_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1563_ = v_a_1557_;
v_isShared_1564_ = v_isSharedCheck_1570_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_tail_1561_);
lean_inc(v_head_1560_);
lean_dec(v_a_1557_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1570_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1565_ = l_Lean_mkLevelParam(v_head_1560_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 1, v_a_1558_);
lean_ctor_set(v___x_1563_, 0, v___x_1565_);
v___x_1567_ = v___x_1563_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_a_1558_);
v___x_1567_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
v_a_1557_ = v_tail_1561_;
v_a_1558_ = v___x_1567_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(lean_object* v_msg_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v_ref_1575_; lean_object* v___x_1576_; lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1585_; 
v_ref_1575_ = lean_ctor_get(v___y_1572_, 5);
v___x_1576_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v_msg_1571_, v___y_1572_, v___y_1573_);
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1585_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1581_; lean_object* v___x_1583_; 
lean_inc(v_ref_1575_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v_ref_1575_);
lean_ctor_set(v___x_1581_, 1, v_a_1577_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 1);
lean_ctor_set(v___x_1579_, 0, v___x_1581_);
v___x_1583_ = v___x_1579_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg___boxed(lean_object* v_msg_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
return v_res_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_ref_1591_, lean_object* v_msg_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_fileName_1596_; lean_object* v_fileMap_1597_; lean_object* v_options_1598_; lean_object* v_currRecDepth_1599_; lean_object* v_maxRecDepth_1600_; lean_object* v_ref_1601_; lean_object* v_currNamespace_1602_; lean_object* v_openDecls_1603_; lean_object* v_initHeartbeats_1604_; lean_object* v_maxHeartbeats_1605_; lean_object* v_quotContext_1606_; lean_object* v_currMacroScope_1607_; uint8_t v_diag_1608_; lean_object* v_cancelTk_x3f_1609_; uint8_t v_suppressElabErrors_1610_; lean_object* v_inheritedTraceOptions_1611_; lean_object* v_ref_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_fileName_1596_ = lean_ctor_get(v___y_1593_, 0);
v_fileMap_1597_ = lean_ctor_get(v___y_1593_, 1);
v_options_1598_ = lean_ctor_get(v___y_1593_, 2);
v_currRecDepth_1599_ = lean_ctor_get(v___y_1593_, 3);
v_maxRecDepth_1600_ = lean_ctor_get(v___y_1593_, 4);
v_ref_1601_ = lean_ctor_get(v___y_1593_, 5);
v_currNamespace_1602_ = lean_ctor_get(v___y_1593_, 6);
v_openDecls_1603_ = lean_ctor_get(v___y_1593_, 7);
v_initHeartbeats_1604_ = lean_ctor_get(v___y_1593_, 8);
v_maxHeartbeats_1605_ = lean_ctor_get(v___y_1593_, 9);
v_quotContext_1606_ = lean_ctor_get(v___y_1593_, 10);
v_currMacroScope_1607_ = lean_ctor_get(v___y_1593_, 11);
v_diag_1608_ = lean_ctor_get_uint8(v___y_1593_, sizeof(void*)*14);
v_cancelTk_x3f_1609_ = lean_ctor_get(v___y_1593_, 12);
v_suppressElabErrors_1610_ = lean_ctor_get_uint8(v___y_1593_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1611_ = lean_ctor_get(v___y_1593_, 13);
v_ref_1612_ = l_Lean_replaceRef(v_ref_1591_, v_ref_1601_);
lean_inc_ref(v_inheritedTraceOptions_1611_);
lean_inc(v_cancelTk_x3f_1609_);
lean_inc(v_currMacroScope_1607_);
lean_inc(v_quotContext_1606_);
lean_inc(v_maxHeartbeats_1605_);
lean_inc(v_initHeartbeats_1604_);
lean_inc(v_openDecls_1603_);
lean_inc(v_currNamespace_1602_);
lean_inc(v_maxRecDepth_1600_);
lean_inc(v_currRecDepth_1599_);
lean_inc_ref(v_options_1598_);
lean_inc_ref(v_fileMap_1597_);
lean_inc_ref(v_fileName_1596_);
v___x_1613_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1613_, 0, v_fileName_1596_);
lean_ctor_set(v___x_1613_, 1, v_fileMap_1597_);
lean_ctor_set(v___x_1613_, 2, v_options_1598_);
lean_ctor_set(v___x_1613_, 3, v_currRecDepth_1599_);
lean_ctor_set(v___x_1613_, 4, v_maxRecDepth_1600_);
lean_ctor_set(v___x_1613_, 5, v_ref_1612_);
lean_ctor_set(v___x_1613_, 6, v_currNamespace_1602_);
lean_ctor_set(v___x_1613_, 7, v_openDecls_1603_);
lean_ctor_set(v___x_1613_, 8, v_initHeartbeats_1604_);
lean_ctor_set(v___x_1613_, 9, v_maxHeartbeats_1605_);
lean_ctor_set(v___x_1613_, 10, v_quotContext_1606_);
lean_ctor_set(v___x_1613_, 11, v_currMacroScope_1607_);
lean_ctor_set(v___x_1613_, 12, v_cancelTk_x3f_1609_);
lean_ctor_set(v___x_1613_, 13, v_inheritedTraceOptions_1611_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*14, v_diag_1608_);
lean_ctor_set_uint8(v___x_1613_, sizeof(void*)*14 + 1, v_suppressElabErrors_1610_);
v___x_1614_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_1592_, v___x_1613_, v___y_1594_);
lean_dec_ref_known(v___x_1613_, 14);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1615_, lean_object* v_msg_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1615_, v_msg_1616_, v___y_1617_, v___y_1618_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v_ref_1615_);
return v_res_1620_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__0));
v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
return v___x_1623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__2));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__4));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__6));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__8));
v___x_1635_ = l_Lean_stringToMessageData(v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__10));
v___x_1638_ = l_Lean_stringToMessageData(v___x_1637_);
return v___x_1638_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__12));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(lean_object* v_msg_1642_, lean_object* v_declHint_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v___x_1646_; lean_object* v_env_1647_; uint8_t v___x_1648_; 
v___x_1646_ = lean_st_ref_get(v___y_1644_);
v_env_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc_ref(v_env_1647_);
lean_dec(v___x_1646_);
v___x_1648_ = l_Lean_Name_isAnonymous(v_declHint_1643_);
if (v___x_1648_ == 0)
{
uint8_t v_isExporting_1649_; 
v_isExporting_1649_ = lean_ctor_get_uint8(v_env_1647_, sizeof(void*)*8);
if (v_isExporting_1649_ == 0)
{
lean_object* v___x_1650_; 
lean_dec_ref(v_env_1647_);
lean_dec(v_declHint_1643_);
v___x_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_msg_1642_);
return v___x_1650_;
}
else
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
lean_inc_ref(v_env_1647_);
v___x_1651_ = l_Lean_Environment_setExporting(v_env_1647_, v___x_1648_);
lean_inc(v_declHint_1643_);
lean_inc_ref(v___x_1651_);
v___x_1652_ = l_Lean_Environment_contains(v___x_1651_, v_declHint_1643_, v_isExporting_1649_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; 
lean_dec_ref(v___x_1651_);
lean_dec_ref(v_env_1647_);
lean_dec(v_declHint_1643_);
v___x_1653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1653_, 0, v_msg_1642_);
return v___x_1653_;
}
else
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v_c_1659_; lean_object* v___x_1660_; 
v___x_1654_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__0);
v___x_1655_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1___closed__3);
v___x_1656_ = l_Lean_Options_empty;
v___x_1657_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1651_);
lean_ctor_set(v___x_1657_, 1, v___x_1654_);
lean_ctor_set(v___x_1657_, 2, v___x_1655_);
lean_ctor_set(v___x_1657_, 3, v___x_1656_);
lean_inc(v_declHint_1643_);
v___x_1658_ = l_Lean_MessageData_ofConstName(v_declHint_1643_, v___x_1648_);
v_c_1659_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1659_, 0, v___x_1657_);
lean_ctor_set(v_c_1659_, 1, v___x_1658_);
v___x_1660_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1647_, v_declHint_1643_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
lean_dec_ref(v_env_1647_);
lean_dec(v_declHint_1643_);
v___x_1661_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set(v___x_1662_, 1, v_c_1659_);
v___x_1663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__3);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = l_Lean_MessageData_note(v___x_1664_);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v_msg_1642_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1666_);
return v___x_1667_;
}
else
{
lean_object* v_val_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1703_; 
v_val_1668_ = lean_ctor_get(v___x_1660_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1660_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1670_ = v___x_1660_;
v_isShared_1671_ = v_isSharedCheck_1703_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_val_1668_);
lean_dec(v___x_1660_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1703_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v_mod_1675_; uint8_t v___x_1676_; 
v___x_1672_ = lean_box(0);
v___x_1673_ = l_Lean_Environment_header(v_env_1647_);
lean_dec_ref(v_env_1647_);
v___x_1674_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1673_);
v_mod_1675_ = lean_array_get(v___x_1672_, v___x_1674_, v_val_1668_);
lean_dec(v_val_1668_);
lean_dec_ref(v___x_1674_);
v___x_1676_ = l_Lean_isPrivateName(v_declHint_1643_);
lean_dec(v_declHint_1643_);
if (v___x_1676_ == 0)
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__5);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v_c_1659_);
v___x_1679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__7);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Lean_MessageData_ofName(v_mod_1675_);
v___x_1682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
v___x_1683_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__9);
v___x_1684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1682_);
lean_ctor_set(v___x_1684_, 1, v___x_1683_);
v___x_1685_ = l_Lean_MessageData_note(v___x_1684_);
v___x_1686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1686_, 0, v_msg_1642_);
lean_ctor_set(v___x_1686_, 1, v___x_1685_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1686_);
v___x_1688_ = v___x_1670_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
else
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1701_; 
v___x_1690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__1);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1690_);
lean_ctor_set(v___x_1691_, 1, v_c_1659_);
v___x_1692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__11);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Lean_MessageData_ofName(v_mod_1675_);
v___x_1695_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1693_);
lean_ctor_set(v___x_1695_, 1, v___x_1694_);
v___x_1696_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___closed__13);
v___x_1697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1695_);
lean_ctor_set(v___x_1697_, 1, v___x_1696_);
v___x_1698_ = l_Lean_MessageData_note(v___x_1697_);
v___x_1699_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_msg_1642_);
lean_ctor_set(v___x_1699_, 1, v___x_1698_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1699_);
v___x_1701_ = v___x_1670_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1704_; 
lean_dec_ref(v_env_1647_);
lean_dec(v_declHint_1643_);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_msg_1642_);
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg___boxed(lean_object* v_msg_1705_, lean_object* v_declHint_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1705_, v_declHint_1706_, v___y_1707_);
lean_dec(v___y_1707_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(lean_object* v_msg_1710_, lean_object* v_declHint_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1725_; 
v___x_1715_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_1710_, v_declHint_1711_, v___y_1713_);
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1718_ = v___x_1715_;
v_isShared_1719_ = v_isSharedCheck_1725_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1715_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1725_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1720_ = l_Lean_unknownIdentifierMessageTag;
v___x_1721_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1720_);
lean_ctor_set(v___x_1721_, 1, v_a_1716_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 0, v___x_1721_);
v___x_1723_ = v___x_1718_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_msg_1726_, lean_object* v_declHint_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_1726_, v_declHint_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1732_, lean_object* v_msg_1733_, lean_object* v_declHint_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
lean_object* v___x_1738_; lean_object* v_a_1739_; lean_object* v___x_1740_; 
v___x_1738_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6(v_msg_1733_, v_declHint_1734_, v___y_1735_, v___y_1736_);
v_a_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___x_1738_);
v___x_1740_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_1732_, v_a_1739_, v___y_1735_, v___y_1736_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1741_, lean_object* v_msg_1742_, lean_object* v_declHint_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1741_, v_msg_1742_, v_declHint_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v_ref_1741_);
return v_res_1747_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1749_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_1750_ = l_Lean_stringToMessageData(v___x_1749_);
return v___x_1750_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__2));
v___x_1753_ = l_Lean_stringToMessageData(v___x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1754_, lean_object* v_constName_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v___x_1759_; uint8_t v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1759_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__1);
v___x_1760_ = 0;
lean_inc(v_constName_1755_);
v___x_1761_ = l_Lean_MessageData_ofConstName(v_constName_1755_, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1759_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
v___x_1763_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___closed__3);
v___x_1764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1762_);
lean_ctor_set(v___x_1764_, 1, v___x_1763_);
v___x_1765_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1754_, v___x_1764_, v_constName_1755_, v___y_1756_, v___y_1757_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1766_, lean_object* v_constName_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1766_, v_constName_1767_, v___y_1768_, v___y_1769_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
lean_dec(v_ref_1766_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(lean_object* v_constName_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_ref_1776_; lean_object* v___x_1777_; 
v_ref_1776_ = lean_ctor_get(v___y_1773_, 5);
v___x_1777_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1776_, v_constName_1772_, v___y_1773_, v___y_1774_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_constName_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1778_, v___y_1779_, v___y_1780_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(lean_object* v_constName_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_){
_start:
{
lean_object* v___x_1787_; lean_object* v_env_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; 
v___x_1787_ = lean_st_ref_get(v___y_1785_);
v_env_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc_ref(v_env_1788_);
lean_dec(v___x_1787_);
v___x_1789_ = 0;
lean_inc(v_constName_1783_);
v___x_1790_ = l_Lean_Environment_findConstVal_x3f(v_env_1788_, v_constName_1783_, v___x_1789_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1783_, v___y_1784_, v___y_1785_);
return v___x_1791_;
}
else
{
lean_object* v_val_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1799_; 
lean_dec(v_constName_1783_);
v_val_1792_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1794_ = v___x_1790_;
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_val_1792_);
lean_dec(v___x_1790_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1799_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___x_1797_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set_tag(v___x_1794_, 0);
v___x_1797_ = v___x_1794_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_val_1792_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0___boxed(lean_object* v_constName_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(lean_object* v_constName_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
lean_inc(v_constName_1805_);
v___x_1809_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0(v_constName_1805_, v___y_1806_, v___y_1807_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1821_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1821_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1821_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1821_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v_levelParams_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1819_; 
v_levelParams_1814_ = lean_ctor_get(v_a_1810_, 1);
lean_inc(v_levelParams_1814_);
lean_dec(v_a_1810_);
v___x_1815_ = lean_box(0);
v___x_1816_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__1(v_levelParams_1814_, v___x_1815_);
v___x_1817_ = l_Lean_mkConst(v_constName_1805_, v___x_1816_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1817_);
v___x_1819_ = v___x_1812_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
v___x_1819_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
return v___x_1819_;
}
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
lean_dec(v_constName_1805_);
v_a_1822_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1809_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1809_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0___boxed(lean_object* v_constName_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_constName_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1834_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__1(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__0));
v___x_1837_ = l_Lean_stringToMessageData(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__3(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__2));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__5(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__4));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__7(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__6));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__9(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__8));
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarning___closed__11(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_Lean_Linter_EnvLinter_printWarning___closed__10));
v___x_1852_ = l_Lean_stringToMessageData(v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning(lean_object* v_declName_1853_, lean_object* v_warning_1854_, uint8_t v_useErrorFormat_1855_, lean_object* v_filePath_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_){
_start:
{
lean_object* v___y_1861_; lean_object* v___y_1862_; 
if (v_useErrorFormat_1855_ == 0)
{
lean_dec_ref(v_filePath_1856_);
v___y_1861_ = v_a_1857_;
v___y_1862_ = v_a_1858_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1882_; 
lean_inc(v_declName_1853_);
v___x_1882_ = l_Lean_findDeclarationRanges_x3f___at___00Lean_Linter_EnvLinter_sortResults_spec__0(v_declName_1853_, v_a_1857_, v_a_1858_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
if (lean_obj_tag(v_a_1883_) == 1)
{
lean_object* v_val_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1940_; 
v_val_1884_ = lean_ctor_get(v_a_1883_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_a_1883_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1886_ = v_a_1883_;
v_isShared_1887_ = v_isSharedCheck_1940_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_val_1884_);
lean_dec(v_a_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1940_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_1853_, v_a_1857_, v_a_1858_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_range_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1930_; 
v_range_1889_ = lean_ctor_get(v_val_1884_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v_val_1884_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v_val_1884_, 1);
lean_dec(v_unused_1931_);
v___x_1891_ = v_val_1884_;
v_isShared_1892_ = v_isSharedCheck_1930_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_range_1889_);
lean_dec(v_val_1884_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1930_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v_pos_1893_; lean_object* v_a_1894_; lean_object* v_line_1895_; lean_object* v_column_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1929_; 
v_pos_1893_ = lean_ctor_get(v_range_1889_, 0);
lean_inc_ref(v_pos_1893_);
lean_dec_ref(v_range_1889_);
v_a_1894_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1894_);
lean_dec_ref_known(v___x_1888_, 1);
v_line_1895_ = lean_ctor_get(v_pos_1893_, 0);
v_column_1896_ = lean_ctor_get(v_pos_1893_, 1);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_pos_1893_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1898_ = v_pos_1893_;
v_isShared_1899_ = v_isSharedCheck_1929_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_column_1896_);
lean_inc(v_line_1895_);
lean_dec(v_pos_1893_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1929_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1887_ == 0)
{
lean_ctor_set_tag(v___x_1886_, 3);
lean_ctor_set(v___x_1886_, 0, v_filePath_1856_);
v___x_1901_ = v___x_1886_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_filePath_1856_);
v___x_1901_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1902_ = l_Lean_MessageData_ofFormat(v___x_1901_);
v___x_1903_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__7, &l_Lean_Linter_EnvLinter_printWarning___closed__7_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__7);
if (v_isShared_1899_ == 0)
{
lean_ctor_set_tag(v___x_1898_, 7);
lean_ctor_set(v___x_1898_, 1, v___x_1903_);
lean_ctor_set(v___x_1898_, 0, v___x_1902_);
v___x_1905_ = v___x_1898_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1902_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1903_);
v___x_1905_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1906_ = l_Nat_reprFast(v_line_1895_);
v___x_1907_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1906_);
v___x_1908_ = l_Lean_MessageData_ofFormat(v___x_1907_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set_tag(v___x_1891_, 7);
lean_ctor_set(v___x_1891_, 1, v___x_1908_);
lean_ctor_set(v___x_1891_, 0, v___x_1905_);
v___x_1910_ = v___x_1891_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1903_);
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = lean_nat_add(v_column_1896_, v___x_1912_);
lean_dec(v_column_1896_);
v___x_1914_ = l_Nat_reprFast(v___x_1913_);
v___x_1915_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
v___x_1916_ = l_Lean_MessageData_ofFormat(v___x_1915_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1911_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__9, &l_Lean_Linter_EnvLinter_printWarning___closed__9_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__9);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = l_Lean_MessageData_ofExpr(v_a_1894_);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__11, &l_Lean_Linter_EnvLinter_printWarning___closed__11_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__11);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1923_);
lean_ctor_set(v___x_1924_, 1, v_warning_1854_);
v___x_1925_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_1924_, v_a_1857_, v_a_1858_);
return v___x_1925_;
}
}
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_del_object(v___x_1886_);
lean_dec(v_val_1884_);
lean_dec_ref(v_filePath_1856_);
lean_dec_ref(v_warning_1854_);
v_a_1932_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1888_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1888_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_a_1932_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
}
}
}
else
{
lean_dec(v_a_1883_);
lean_dec_ref(v_filePath_1856_);
v___y_1861_ = v_a_1857_;
v___y_1862_ = v_a_1858_;
goto v___jp_1860_;
}
}
else
{
lean_object* v_a_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1948_; 
lean_dec_ref(v_filePath_1856_);
lean_dec_ref(v_warning_1854_);
lean_dec(v_declName_1853_);
v_a_1941_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1943_ = v___x_1882_;
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_a_1941_);
lean_dec(v___x_1882_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1948_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_a_1941_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
v___jp_1860_:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0(v_declName_1853_, v___y_1861_, v___y_1862_);
if (lean_obj_tag(v___x_1863_) == 0)
{
lean_object* v_a_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_a_1864_ = lean_ctor_get(v___x_1863_, 0);
lean_inc(v_a_1864_);
lean_dec_ref_known(v___x_1863_, 1);
v___x_1865_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__1, &l_Lean_Linter_EnvLinter_printWarning___closed__1_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__1);
v___x_1866_ = l_Lean_MessageData_ofExpr(v_a_1864_);
v___x_1867_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__3, &l_Lean_Linter_EnvLinter_printWarning___closed__3_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__3);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v_warning_1854_);
v___x_1871_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__5, &l_Lean_Linter_EnvLinter_printWarning___closed__5_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__5);
v___x_1872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
v___x_1873_ = l_Lean_addMessageContextPartial___at___00Lean_Linter_EnvLinter_printWarning_spec__1(v___x_1872_, v___y_1861_, v___y_1862_);
return v___x_1873_;
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_dec_ref(v_warning_1854_);
v_a_1874_ = lean_ctor_get(v___x_1863_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1863_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1863_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1863_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarning___boxed(lean_object* v_declName_1949_, lean_object* v_warning_1950_, lean_object* v_useErrorFormat_1951_, lean_object* v_filePath_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
uint8_t v_useErrorFormat_boxed_1956_; lean_object* v_res_1957_; 
v_useErrorFormat_boxed_1956_ = lean_unbox(v_useErrorFormat_1951_);
v_res_1957_ = l_Lean_Linter_EnvLinter_printWarning(v_declName_1949_, v_warning_1950_, v_useErrorFormat_boxed_1956_, v_filePath_1952_, v_a_1953_, v_a_1954_);
lean_dec(v_a_1954_);
lean_dec_ref(v_a_1953_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1958_, lean_object* v_constName_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_1959_, v___y_1960_, v___y_1961_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1964_, lean_object* v_constName_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2(v_00_u03b1_1964_, v_constName_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1970_, lean_object* v_ref_1971_, lean_object* v_constName_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v___x_1976_; 
v___x_1976_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1971_, v_constName_1972_, v___y_1973_, v___y_1974_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1977_, lean_object* v_ref_1978_, lean_object* v_constName_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1977_, v_ref_1978_, v_constName_1979_, v___y_1980_, v___y_1981_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v_ref_1978_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1984_, lean_object* v_ref_1985_, lean_object* v_msg_1986_, lean_object* v_declHint_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1991_; 
v___x_1991_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1985_, v_msg_1986_, v_declHint_1987_, v___y_1988_, v___y_1989_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1992_, lean_object* v_ref_1993_, lean_object* v_msg_1994_, lean_object* v_declHint_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1992_, v_ref_1993_, v_msg_1994_, v_declHint_1995_, v___y_1996_, v___y_1997_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
lean_dec(v_ref_1993_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(lean_object* v_msg_2000_, lean_object* v_declHint_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___redArg(v_msg_2000_, v_declHint_2001_, v___y_2003_);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7___boxed(lean_object* v_msg_2006_, lean_object* v_declHint_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__6_spec__7(v_msg_2006_, v_declHint_2007_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_2012_, lean_object* v_ref_2013_, lean_object* v_msg_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_ref_2013_, v_msg_2014_, v___y_2015_, v___y_2016_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2019_, lean_object* v_ref_2020_, lean_object* v_msg_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_2019_, v_ref_2020_, v_msg_2021_, v___y_2022_, v___y_2023_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec(v_ref_2020_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(lean_object* v_00_u03b1_2026_, lean_object* v_msg_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v___x_2031_; 
v___x_2031_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___redArg(v_msg_2027_, v___y_2028_, v___y_2029_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9___boxed(lean_object* v_00_u03b1_2032_, lean_object* v_msg_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__9(v_00_u03b1_2032_, v_msg_2033_, v___y_2034_, v___y_2035_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(uint8_t v_useErrorFormat_2038_, lean_object* v_filePath_2039_, size_t v_sz_2040_, size_t v_i_2041_, lean_object* v_bs_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_usize_dec_lt(v_i_2041_, v_sz_2040_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
lean_dec_ref(v_filePath_2039_);
v___x_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2047_, 0, v_bs_2042_);
return v___x_2047_;
}
else
{
lean_object* v_v_2048_; lean_object* v_fst_2049_; lean_object* v_snd_2050_; lean_object* v___x_2051_; 
v_v_2048_ = lean_array_uget_borrowed(v_bs_2042_, v_i_2041_);
v_fst_2049_ = lean_ctor_get(v_v_2048_, 0);
v_snd_2050_ = lean_ctor_get(v_v_2048_, 1);
lean_inc_ref(v_filePath_2039_);
lean_inc(v_snd_2050_);
lean_inc(v_fst_2049_);
v___x_2051_ = l_Lean_Linter_EnvLinter_printWarning(v_fst_2049_, v_snd_2050_, v_useErrorFormat_2038_, v_filePath_2039_, v___y_2043_, v___y_2044_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; lean_object* v___x_2053_; lean_object* v_bs_x27_2054_; size_t v___x_2055_; size_t v___x_2056_; lean_object* v___x_2057_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
v___x_2053_ = lean_unsigned_to_nat(0u);
v_bs_x27_2054_ = lean_array_uset(v_bs_2042_, v_i_2041_, v___x_2053_);
v___x_2055_ = ((size_t)1ULL);
v___x_2056_ = lean_usize_add(v_i_2041_, v___x_2055_);
v___x_2057_ = lean_array_uset(v_bs_x27_2054_, v_i_2041_, v_a_2052_);
v_i_2041_ = v___x_2056_;
v_bs_2042_ = v___x_2057_;
goto _start;
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec_ref(v_bs_2042_);
lean_dec_ref(v_filePath_2039_);
v_a_2059_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2051_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2051_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0___boxed(lean_object* v_useErrorFormat_2067_, lean_object* v_filePath_2068_, lean_object* v_sz_2069_, lean_object* v_i_2070_, lean_object* v_bs_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
uint8_t v_useErrorFormat_boxed_2075_; size_t v_sz_boxed_2076_; size_t v_i_boxed_2077_; lean_object* v_res_2078_; 
v_useErrorFormat_boxed_2075_ = lean_unbox(v_useErrorFormat_2067_);
v_sz_boxed_2076_ = lean_unbox_usize(v_sz_2069_);
lean_dec(v_sz_2069_);
v_i_boxed_2077_ = lean_unbox_usize(v_i_2070_);
lean_dec(v_i_2070_);
v_res_2078_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_boxed_2075_, v_filePath_2068_, v_sz_boxed_2076_, v_i_boxed_2077_, v_bs_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
return v_res_2078_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0(void){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_box(1);
v___x_2080_ = l_Lean_MessageData_ofFormat(v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings(lean_object* v_results_2081_, lean_object* v_filePath_2082_, uint8_t v_useErrorFormat_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_Linter_EnvLinter_sortResults___redArg(v_results_2081_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; size_t v_sz_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
lean_inc(v_a_2088_);
lean_dec_ref_known(v___x_2087_, 1);
v_sz_2089_ = lean_array_size(v_a_2088_);
v___x_2090_ = ((size_t)0ULL);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_printWarnings_spec__0(v_useErrorFormat_2083_, v_filePath_2082_, v_sz_2089_, v___x_2090_, v_a_2088_, v_a_2084_, v_a_2085_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2102_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2102_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2102_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2096_ = lean_array_to_list(v_a_2092_);
v___x_2097_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2098_ = l_Lean_MessageData_joinSep(v___x_2096_, v___x_2097_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2098_);
v___x_2100_ = v___x_2094_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
v_a_2103_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2091_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2091_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
lean_dec_ref(v_filePath_2082_);
v_a_2111_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2087_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2087_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_printWarnings___boxed(lean_object* v_results_2119_, lean_object* v_filePath_2120_, lean_object* v_useErrorFormat_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
uint8_t v_useErrorFormat_boxed_2125_; lean_object* v_res_2126_; 
v_useErrorFormat_boxed_2125_ = lean_unbox(v_useErrorFormat_2121_);
v_res_2126_ = l_Lean_Linter_EnvLinter_printWarnings(v_results_2119_, v_filePath_2120_, v_useErrorFormat_boxed_2125_, v_a_2122_, v_a_2123_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2122_);
lean_dec_ref(v_results_2119_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(lean_object* v_x_2127_, lean_object* v_x_2128_){
_start:
{
if (lean_obj_tag(v_x_2128_) == 0)
{
return v_x_2127_;
}
else
{
lean_object* v_key_2129_; lean_object* v_value_2130_; lean_object* v_tail_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_key_2129_ = lean_ctor_get(v_x_2128_, 0);
v_value_2130_ = lean_ctor_get(v_x_2128_, 1);
v_tail_2131_ = lean_ctor_get(v_x_2128_, 2);
lean_inc(v_value_2130_);
lean_inc(v_key_2129_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v_key_2129_);
lean_ctor_set(v___x_2132_, 1, v_value_2130_);
v___x_2133_ = lean_array_push(v_x_2127_, v___x_2132_);
v_x_2127_ = v___x_2133_;
v_x_2128_ = v_tail_2131_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2___boxed(lean_object* v_x_2135_, lean_object* v_x_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_x_2135_, v_x_2136_);
lean_dec(v_x_2136_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(lean_object* v_as_2138_, size_t v_i_2139_, size_t v_stop_2140_, lean_object* v_b_2141_){
_start:
{
uint8_t v___x_2142_; 
v___x_2142_ = lean_usize_dec_eq(v_i_2139_, v_stop_2140_);
if (v___x_2142_ == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2144_; size_t v___x_2145_; size_t v___x_2146_; 
v___x_2143_ = lean_array_uget_borrowed(v_as_2138_, v_i_2139_);
v___x_2144_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__2(v_b_2141_, v___x_2143_);
v___x_2145_ = ((size_t)1ULL);
v___x_2146_ = lean_usize_add(v_i_2139_, v___x_2145_);
v_i_2139_ = v___x_2146_;
v_b_2141_ = v___x_2144_;
goto _start;
}
else
{
return v_b_2141_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3___boxed(lean_object* v_as_2148_, lean_object* v_i_2149_, lean_object* v_stop_2150_, lean_object* v_b_2151_){
_start:
{
size_t v_i_boxed_2152_; size_t v_stop_boxed_2153_; lean_object* v_res_2154_; 
v_i_boxed_2152_ = lean_unbox_usize(v_i_2149_);
lean_dec(v_i_2149_);
v_stop_boxed_2153_ = lean_unbox_usize(v_stop_2150_);
lean_dec(v_stop_2150_);
v_res_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_as_2148_, v_i_boxed_2152_, v_stop_boxed_2153_, v_b_2151_);
lean_dec_ref(v_as_2148_);
return v_res_2154_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2156_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__0));
v___x_2157_ = l_Lean_stringToMessageData(v___x_2156_);
return v___x_2157_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2159_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__2));
v___x_2160_ = l_Lean_stringToMessageData(v___x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(uint8_t v_useErrorFormat_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
if (lean_obj_tag(v_x_2162_) == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = l_List_reverse___redArg(v_x_2163_);
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
return v___x_2168_;
}
else
{
lean_object* v_head_2169_; lean_object* v_tail_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2213_; 
v_head_2169_ = lean_ctor_get(v_x_2162_, 0);
v_tail_2170_ = lean_ctor_get(v_x_2162_, 1);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_x_2162_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2172_ = v_x_2162_;
v_isShared_2173_ = v_isSharedCheck_2213_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_tail_2170_);
lean_inc(v_head_2169_);
lean_dec(v_x_2162_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2213_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v_a_2175_; lean_object* v_snd_2180_; lean_object* v_fst_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2212_; 
v_snd_2180_ = lean_ctor_get(v_head_2169_, 1);
v_fst_2181_ = lean_ctor_get(v_head_2169_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_head_2169_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2183_ = v_head_2169_;
v_isShared_2184_ = v_isSharedCheck_2212_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_snd_2180_);
lean_inc(v_fst_2181_);
lean_dec(v_head_2169_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2212_;
goto v_resetjp_2182_;
}
v___jp_2174_:
{
lean_object* v___x_2177_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 1, v_x_2163_);
lean_ctor_set(v___x_2172_, 0, v_a_2175_);
v___x_2177_ = v___x_2172_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2175_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_x_2163_);
v___x_2177_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
v_x_2162_ = v_tail_2170_;
v_x_2163_ = v___x_2177_;
goto _start;
}
}
v_resetjp_2182_:
{
lean_object* v_fst_2185_; lean_object* v_snd_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2211_; 
v_fst_2185_ = lean_ctor_get(v_snd_2180_, 0);
v_snd_2186_ = lean_ctor_get(v_snd_2180_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_snd_2180_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2188_ = v_snd_2180_;
v_isShared_2189_ = v_isSharedCheck_2211_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_snd_2186_);
lean_inc(v_fst_2185_);
lean_dec(v_snd_2180_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2211_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_Linter_EnvLinter_printWarnings(v_snd_2186_, v_fst_2185_, v_useErrorFormat_2161_, v___y_2164_, v___y_2165_);
lean_dec(v_snd_2186_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2191_);
lean_dec_ref_known(v___x_2190_, 1);
v___x_2192_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__1);
v___x_2193_ = l_Lean_MessageData_ofName(v_fst_2181_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set_tag(v___x_2188_, 7);
lean_ctor_set(v___x_2188_, 1, v___x_2193_);
lean_ctor_set(v___x_2188_, 0, v___x_2192_);
v___x_2195_ = v___x_2188_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2196_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
if (v_isShared_2184_ == 0)
{
lean_ctor_set_tag(v___x_2183_, 7);
lean_ctor_set(v___x_2183_, 1, v___x_2196_);
lean_ctor_set(v___x_2183_, 0, v___x_2195_);
v___x_2198_ = v___x_2183_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
lean_ctor_set(v___x_2199_, 1, v_a_2191_);
v_a_2175_ = v___x_2199_;
goto v___jp_2174_;
}
}
}
else
{
lean_del_object(v___x_2188_);
lean_del_object(v___x_2183_);
lean_dec(v_fst_2181_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2202_; 
v_a_2202_ = lean_ctor_get(v___x_2190_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2190_, 1);
v_a_2175_ = v_a_2202_;
goto v___jp_2174_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
lean_del_object(v___x_2172_);
lean_dec(v_tail_2170_);
lean_dec(v_x_2163_);
v_a_2203_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2190_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2190_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___boxed(lean_object* v_useErrorFormat_2214_, lean_object* v_x_2215_, lean_object* v_x_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
uint8_t v_useErrorFormat_boxed_2220_; lean_object* v_res_2221_; 
v_useErrorFormat_boxed_2220_ = lean_unbox(v_useErrorFormat_2214_);
v_res_2221_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(v_useErrorFormat_boxed_2220_, v_x_2215_, v_x_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(lean_object* v_a_2222_, lean_object* v_x_2223_){
_start:
{
if (lean_obj_tag(v_x_2223_) == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_box(0);
return v___x_2224_;
}
else
{
lean_object* v_key_2225_; lean_object* v_value_2226_; lean_object* v_tail_2227_; uint8_t v___x_2228_; 
v_key_2225_ = lean_ctor_get(v_x_2223_, 0);
v_value_2226_ = lean_ctor_get(v_x_2223_, 1);
v_tail_2227_ = lean_ctor_get(v_x_2223_, 2);
v___x_2228_ = lean_name_eq(v_key_2225_, v_a_2222_);
if (v___x_2228_ == 0)
{
v_x_2223_ = v_tail_2227_;
goto _start;
}
else
{
lean_object* v___x_2230_; 
lean_inc(v_value_2226_);
v___x_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2230_, 0, v_value_2226_);
return v___x_2230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg___boxed(lean_object* v_a_2231_, lean_object* v_x_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2231_, v_x_2232_);
lean_dec(v_x_2232_);
lean_dec(v_a_2231_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(lean_object* v_m_2234_, lean_object* v_a_2235_){
_start:
{
lean_object* v_buckets_2236_; lean_object* v___x_2237_; uint64_t v___y_2239_; 
v_buckets_2236_ = lean_ctor_get(v_m_2234_, 1);
v___x_2237_ = lean_array_get_size(v_buckets_2236_);
if (lean_obj_tag(v_a_2235_) == 0)
{
uint64_t v___x_2253_; 
v___x_2253_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0_spec__1_spec__2_spec__9___redArg___closed__0);
v___y_2239_ = v___x_2253_;
goto v___jp_2238_;
}
else
{
uint64_t v_hash_2254_; 
v_hash_2254_ = lean_ctor_get_uint64(v_a_2235_, sizeof(void*)*2);
v___y_2239_ = v_hash_2254_;
goto v___jp_2238_;
}
v___jp_2238_:
{
uint64_t v___x_2240_; uint64_t v___x_2241_; uint64_t v_fold_2242_; uint64_t v___x_2243_; uint64_t v___x_2244_; uint64_t v___x_2245_; size_t v___x_2246_; size_t v___x_2247_; size_t v___x_2248_; size_t v___x_2249_; size_t v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2240_ = 32ULL;
v___x_2241_ = lean_uint64_shift_right(v___y_2239_, v___x_2240_);
v_fold_2242_ = lean_uint64_xor(v___y_2239_, v___x_2241_);
v___x_2243_ = 16ULL;
v___x_2244_ = lean_uint64_shift_right(v_fold_2242_, v___x_2243_);
v___x_2245_ = lean_uint64_xor(v_fold_2242_, v___x_2244_);
v___x_2246_ = lean_uint64_to_usize(v___x_2245_);
v___x_2247_ = lean_usize_of_nat(v___x_2237_);
v___x_2248_ = ((size_t)1ULL);
v___x_2249_ = lean_usize_sub(v___x_2247_, v___x_2248_);
v___x_2250_ = lean_usize_land(v___x_2246_, v___x_2249_);
v___x_2251_ = lean_array_uget_borrowed(v_buckets_2236_, v___x_2250_);
v___x_2252_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2235_, v___x_2251_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg___boxed(lean_object* v_m_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_m_2255_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(lean_object* v_key_2258_, lean_object* v_value_2259_, lean_object* v_fp_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2264_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v___x_2265_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v___x_2264_, v_key_2258_, v_value_2259_);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v_fp_2260_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0___boxed(lean_object* v_key_2268_, lean_object* v_value_2269_, lean_object* v_fp_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2268_, v_value_2269_, v_fp_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(lean_object* v_constName_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; lean_object* v_env_2280_; uint8_t v___x_2281_; lean_object* v___x_2282_; 
v___x_2279_ = lean_st_ref_get(v___y_2277_);
v_env_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc_ref(v_env_2280_);
lean_dec(v___x_2279_);
v___x_2281_ = 0;
lean_inc(v_constName_2275_);
v___x_2282_ = l_Lean_Environment_find_x3f(v_env_2280_, v_constName_2275_, v___x_2281_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Linter_EnvLinter_printWarning_spec__0_spec__0_spec__2___redArg(v_constName_2275_, v___y_2276_, v___y_2277_);
return v___x_2283_;
}
else
{
lean_object* v_val_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v_constName_2275_);
v_val_2284_ = lean_ctor_get(v___x_2282_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2282_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2282_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_val_2284_);
lean_dec(v___x_2282_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
lean_ctor_set_tag(v___x_2286_, 0);
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_val_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5___boxed(lean_object* v_constName_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_constName_2292_, v___y_2293_, v___y_2294_);
lean_dec(v___y_2294_);
lean_dec_ref(v___y_2293_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(lean_object* v_declName_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; 
lean_inc(v_declName_2297_);
v___x_2301_ = l_Lean_getConstInfo___at___00Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4_spec__5(v_declName_2297_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2328_; 
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2328_ == 0)
{
lean_object* v_unused_2329_; 
v_unused_2329_ = lean_ctor_get(v___x_2301_, 0);
lean_dec(v_unused_2329_);
v___x_2303_ = v___x_2301_;
v_isShared_2304_ = v_isSharedCheck_2328_;
goto v_resetjp_2302_;
}
else
{
lean_dec(v___x_2301_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2328_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v_env_2306_; lean_object* v___x_2307_; 
v___x_2305_ = lean_st_ref_get(v___y_2299_);
v_env_2306_ = lean_ctor_get(v___x_2305_, 0);
lean_inc_ref(v_env_2306_);
lean_dec(v___x_2305_);
v___x_2307_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2306_, v_declName_2297_);
lean_dec(v_declName_2297_);
lean_dec_ref(v_env_2306_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2308_ = lean_box(0);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2308_);
v___x_2310_ = v___x_2303_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
else
{
lean_object* v_val_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2327_; 
v_val_2312_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2314_ = v___x_2307_;
v_isShared_2315_ = v_isSharedCheck_2327_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_val_2312_);
lean_dec(v___x_2307_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2327_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2316_; lean_object* v_env_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2322_; 
v___x_2316_ = lean_st_ref_get(v___y_2299_);
v_env_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc_ref(v_env_2317_);
lean_dec(v___x_2316_);
v___x_2318_ = lean_box(0);
v___x_2319_ = l_Lean_Environment_allImportedModuleNames(v_env_2317_);
lean_dec_ref(v_env_2317_);
v___x_2320_ = lean_array_get(v___x_2318_, v___x_2319_, v_val_2312_);
lean_dec(v_val_2312_);
lean_dec_ref(v___x_2319_);
if (v_isShared_2315_ == 0)
{
lean_ctor_set(v___x_2314_, 0, v___x_2320_);
v___x_2322_ = v___x_2314_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2320_);
v___x_2322_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
lean_object* v___x_2324_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 0, v___x_2322_);
v___x_2324_ = v___x_2303_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v___x_2322_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
lean_dec(v_declName_2297_);
v_a_2330_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2301_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2301_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4___boxed(lean_object* v_declName_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_declName_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(uint8_t v_useErrorFormat_2346_, lean_object* v_sp_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
if (lean_obj_tag(v_x_2349_) == 0)
{
lean_object* v___x_2353_; 
lean_dec(v_sp_2347_);
v___x_2353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_x_2348_);
return v___x_2353_;
}
else
{
lean_object* v_key_2354_; lean_object* v_value_2355_; lean_object* v_tail_2356_; lean_object* v___y_2358_; lean_object* v_a_2359_; lean_object* v___y_2363_; lean_object* v___y_2364_; lean_object* v___x_2366_; 
v_key_2354_ = lean_ctor_get(v_x_2349_, 0);
lean_inc_n(v_key_2354_, 2);
v_value_2355_ = lean_ctor_get(v_x_2349_, 1);
lean_inc(v_value_2355_);
v_tail_2356_ = lean_ctor_get(v_x_2349_, 2);
lean_inc(v_tail_2356_);
lean_dec_ref_known(v_x_2349_, 3);
v___x_2366_ = l_Lean_findModuleOf_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__4(v_key_2354_, v___y_2350_, v___y_2351_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; lean_object* v___y_2370_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = lean_st_ref_get(v___y_2351_);
if (lean_obj_tag(v_a_2367_) == 0)
{
lean_object* v_env_2406_; lean_object* v___x_2407_; 
v_env_2406_ = lean_ctor_get(v___x_2368_, 0);
lean_inc_ref(v_env_2406_);
lean_dec(v___x_2368_);
v___x_2407_ = l_Lean_Environment_mainModule(v_env_2406_);
lean_dec_ref(v_env_2406_);
v___y_2370_ = v___x_2407_;
goto v___jp_2369_;
}
else
{
lean_object* v_val_2408_; 
lean_dec(v___x_2368_);
v_val_2408_ = lean_ctor_get(v_a_2367_, 0);
lean_inc(v_val_2408_);
lean_dec_ref_known(v_a_2367_, 1);
v___y_2370_ = v_val_2408_;
goto v___jp_2369_;
}
v___jp_2369_:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_x_2348_, v___y_2370_);
if (lean_obj_tag(v___x_2371_) == 0)
{
if (v_useErrorFormat_2346_ == 0)
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___x_2373_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2354_, v_value_2355_, v___x_2372_, v___y_2350_, v___y_2351_);
v___y_2363_ = v___y_2370_;
v___y_2364_ = v___x_2373_;
goto v___jp_2362_;
}
else
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__1));
lean_inc(v___y_2370_);
lean_inc(v_sp_2347_);
v___x_2375_ = l_Lean_SearchPath_findWithExt(v_sp_2347_, v___x_2374_, v___y_2370_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
lean_inc(v_a_2376_);
lean_dec_ref_known(v___x_2375_, 1);
if (lean_obj_tag(v_a_2376_) == 0)
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__2));
lean_inc(v___y_2370_);
v___x_2378_ = l_Lean_modToFilePath(v___x_2377_, v___y_2370_, v___x_2374_);
v___x_2379_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2354_, v_value_2355_, v___x_2378_, v___y_2350_, v___y_2351_);
v___y_2363_ = v___y_2370_;
v___y_2364_ = v___x_2379_;
goto v___jp_2362_;
}
else
{
lean_object* v_val_2380_; lean_object* v___x_2381_; 
v_val_2380_ = lean_ctor_get(v_a_2376_, 0);
lean_inc(v_val_2380_);
lean_dec_ref_known(v_a_2376_, 1);
v___x_2381_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___lam__0(v_key_2354_, v_value_2355_, v_val_2380_, v___y_2350_, v___y_2351_);
v___y_2363_ = v___y_2370_;
v___y_2364_ = v___x_2381_;
goto v___jp_2362_;
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v___y_2370_);
lean_dec(v_tail_2356_);
lean_dec(v_value_2355_);
lean_dec(v_key_2354_);
lean_dec_ref(v_x_2348_);
lean_dec(v_sp_2347_);
v_a_2382_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2384_ = v___x_2375_;
v_isShared_2385_ = v_isSharedCheck_2394_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2375_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2394_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_ref_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2392_; 
v_ref_2386_ = lean_ctor_get(v___y_2350_, 5);
v___x_2387_ = lean_io_error_to_string(v_a_2382_);
v___x_2388_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
v___x_2389_ = l_Lean_MessageData_ofFormat(v___x_2388_);
lean_inc(v_ref_2386_);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_ref_2386_);
lean_ctor_set(v___x_2390_, 1, v___x_2389_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 0, v___x_2390_);
v___x_2392_ = v___x_2384_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
else
{
lean_object* v_val_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2405_; 
v_val_2395_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_val_2395_);
lean_dec_ref_known(v___x_2371_, 1);
v_fst_2396_ = lean_ctor_get(v_val_2395_, 0);
v_snd_2397_ = lean_ctor_get(v_val_2395_, 1);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_val_2395_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2399_ = v_val_2395_;
v_isShared_2400_ = v_isSharedCheck_2405_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_snd_2397_);
lean_inc(v_fst_2396_);
lean_dec(v_val_2395_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2405_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2401_; lean_object* v___x_2403_; 
v___x_2401_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_snd_2397_, v_key_2354_, v_value_2355_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 1, v___x_2401_);
v___x_2403_ = v___x_2399_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_fst_2396_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
v___y_2358_ = v___y_2370_;
v_a_2359_ = v___x_2403_;
goto v___jp_2357_;
}
}
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
lean_dec(v_tail_2356_);
lean_dec(v_value_2355_);
lean_dec(v_key_2354_);
lean_dec_ref(v_x_2348_);
lean_dec(v_sp_2347_);
v_a_2409_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2366_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2366_);
v___x_2411_ = lean_box(0);
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
v_resetjp_2410_:
{
lean_object* v___x_2414_; 
if (v_isShared_2412_ == 0)
{
v___x_2414_ = v___x_2411_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_a_2409_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
v___jp_2357_:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Linter_EnvLinter_lintCore_spec__0___redArg(v_x_2348_, v___y_2358_, v_a_2359_);
v_x_2348_ = v___x_2360_;
v_x_2349_ = v_tail_2356_;
goto _start;
}
v___jp_2362_:
{
lean_object* v_a_2365_; 
v_a_2365_ = lean_ctor_get(v___y_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref(v___y_2364_);
v___y_2358_ = v___y_2363_;
v_a_2359_ = v_a_2365_;
goto v___jp_2357_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___boxed(lean_object* v_useErrorFormat_2417_, lean_object* v_sp_2418_, lean_object* v_x_2419_, lean_object* v_x_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
uint8_t v_useErrorFormat_boxed_2424_; lean_object* v_res_2425_; 
v_useErrorFormat_boxed_2424_ = lean_unbox(v_useErrorFormat_2417_);
v_res_2425_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_boxed_2424_, v_sp_2418_, v_x_2419_, v_x_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(uint8_t v_useErrorFormat_2426_, lean_object* v_sp_2427_, lean_object* v_as_2428_, size_t v_i_2429_, size_t v_stop_2430_, lean_object* v_b_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
uint8_t v___x_2435_; 
v___x_2435_ = lean_usize_dec_eq(v_i_2429_, v_stop_2430_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_array_uget_borrowed(v_as_2428_, v_i_2429_);
lean_inc(v___x_2436_);
lean_inc(v_sp_2427_);
v___x_2437_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6(v_useErrorFormat_2426_, v_sp_2427_, v_b_2431_, v___x_2436_, v___y_2432_, v___y_2433_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; size_t v___x_2439_; size_t v___x_2440_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = ((size_t)1ULL);
v___x_2440_ = lean_usize_add(v_i_2429_, v___x_2439_);
v_i_2429_ = v___x_2440_;
v_b_2431_ = v_a_2438_;
goto _start;
}
else
{
lean_dec(v_sp_2427_);
return v___x_2437_;
}
}
else
{
lean_object* v___x_2442_; 
lean_dec(v_sp_2427_);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v_b_2431_);
return v___x_2442_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7___boxed(lean_object* v_useErrorFormat_2443_, lean_object* v_sp_2444_, lean_object* v_as_2445_, lean_object* v_i_2446_, lean_object* v_stop_2447_, lean_object* v_b_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
uint8_t v_useErrorFormat_boxed_2452_; size_t v_i_boxed_2453_; size_t v_stop_boxed_2454_; lean_object* v_res_2455_; 
v_useErrorFormat_boxed_2452_ = lean_unbox(v_useErrorFormat_2443_);
v_i_boxed_2453_ = lean_unbox_usize(v_i_2446_);
lean_dec(v_i_2446_);
v_stop_boxed_2454_ = lean_unbox_usize(v_stop_2447_);
lean_dec(v_stop_2447_);
v_res_2455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_boxed_2452_, v_sp_2444_, v_as_2445_, v_i_boxed_2453_, v_stop_boxed_2454_, v_b_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec_ref(v_as_2445_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(lean_object* v_hi_2456_, lean_object* v_pivot_2457_, lean_object* v_as_2458_, lean_object* v_i_2459_, lean_object* v_k_2460_){
_start:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_nat_dec_lt(v_k_2460_, v_hi_2456_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_dec(v_k_2460_);
lean_dec_ref(v_pivot_2457_);
v___x_2462_ = lean_array_fswap(v_as_2458_, v_i_2459_, v_hi_2456_);
v___x_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2463_, 0, v_i_2459_);
lean_ctor_set(v___x_2463_, 1, v___x_2462_);
return v___x_2463_;
}
else
{
lean_object* v___x_2464_; lean_object* v_fst_2465_; lean_object* v_fst_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2464_ = lean_array_fget_borrowed(v_as_2458_, v_k_2460_);
v_fst_2465_ = lean_ctor_get(v___x_2464_, 0);
v_fst_2466_ = lean_ctor_get(v_pivot_2457_, 0);
lean_inc(v_fst_2465_);
v___x_2467_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2465_, v___x_2461_);
lean_inc(v_fst_2466_);
v___x_2468_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2466_, v___x_2461_);
v___x_2469_ = lean_string_dec_lt(v___x_2467_, v___x_2468_);
lean_dec_ref(v___x_2468_);
lean_dec_ref(v___x_2467_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2471_; 
v___x_2470_ = lean_unsigned_to_nat(1u);
v___x_2471_ = lean_nat_add(v_k_2460_, v___x_2470_);
lean_dec(v_k_2460_);
v_k_2460_ = v___x_2471_;
goto _start;
}
else
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2473_ = lean_array_fswap(v_as_2458_, v_i_2459_, v_k_2460_);
v___x_2474_ = lean_unsigned_to_nat(1u);
v___x_2475_ = lean_nat_add(v_i_2459_, v___x_2474_);
lean_dec(v_i_2459_);
v___x_2476_ = lean_nat_add(v_k_2460_, v___x_2474_);
lean_dec(v_k_2460_);
v_as_2458_ = v___x_2473_;
v_i_2459_ = v___x_2475_;
v_k_2460_ = v___x_2476_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg___boxed(lean_object* v_hi_2478_, lean_object* v_pivot_2479_, lean_object* v_as_2480_, lean_object* v_i_2481_, lean_object* v_k_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2478_, v_pivot_2479_, v_as_2480_, v_i_2481_, v_k_2482_);
lean_dec(v_hi_2478_);
return v_res_2483_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(uint8_t v___x_2484_, lean_object* v_x_2485_, lean_object* v_x_2486_){
_start:
{
lean_object* v_fst_2487_; lean_object* v_fst_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; 
v_fst_2487_ = lean_ctor_get(v_x_2485_, 0);
lean_inc(v_fst_2487_);
lean_dec_ref(v_x_2485_);
v_fst_2488_ = lean_ctor_get(v_x_2486_, 0);
lean_inc(v_fst_2488_);
lean_dec_ref(v_x_2486_);
v___x_2489_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2487_, v___x_2484_);
v___x_2490_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fst_2488_, v___x_2484_);
v___x_2491_ = lean_string_dec_lt(v___x_2489_, v___x_2490_);
lean_dec_ref(v___x_2490_);
lean_dec_ref(v___x_2489_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0___boxed(lean_object* v___x_2492_, lean_object* v_x_2493_, lean_object* v_x_2494_){
_start:
{
uint8_t v___x_5444__boxed_2495_; uint8_t v_res_2496_; lean_object* v_r_2497_; 
v___x_5444__boxed_2495_ = lean_unbox(v___x_2492_);
v_res_2496_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_5444__boxed_2495_, v_x_2493_, v_x_2494_);
v_r_2497_ = lean_box(v_res_2496_);
return v_r_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(lean_object* v_n_2498_, lean_object* v_as_2499_, lean_object* v_lo_2500_, lean_object* v_hi_2501_){
_start:
{
lean_object* v___y_2503_; uint8_t v___x_2513_; 
v___x_2513_ = lean_nat_dec_lt(v_lo_2500_, v_hi_2501_);
if (v___x_2513_ == 0)
{
lean_dec(v_lo_2500_);
return v_as_2499_;
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v_mid_2516_; lean_object* v___y_2518_; lean_object* v___y_2524_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2514_ = lean_nat_add(v_lo_2500_, v_hi_2501_);
v___x_2515_ = lean_unsigned_to_nat(1u);
v_mid_2516_ = lean_nat_shiftr(v___x_2514_, v___x_2515_);
lean_dec(v___x_2514_);
v___x_2529_ = lean_array_fget_borrowed(v_as_2499_, v_mid_2516_);
v___x_2530_ = lean_array_fget_borrowed(v_as_2499_, v_lo_2500_);
lean_inc(v___x_2530_);
lean_inc(v___x_2529_);
v___x_2531_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2513_, v___x_2529_, v___x_2530_);
if (v___x_2531_ == 0)
{
v___y_2524_ = v_as_2499_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2532_; 
v___x_2532_ = lean_array_fswap(v_as_2499_, v_lo_2500_, v_mid_2516_);
v___y_2524_ = v___x_2532_;
goto v___jp_2523_;
}
v___jp_2517_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v___x_2519_ = lean_array_fget_borrowed(v___y_2518_, v_mid_2516_);
v___x_2520_ = lean_array_fget_borrowed(v___y_2518_, v_hi_2501_);
lean_inc(v___x_2520_);
lean_inc(v___x_2519_);
v___x_2521_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2513_, v___x_2519_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_dec(v_mid_2516_);
v___y_2503_ = v___y_2518_;
goto v___jp_2502_;
}
else
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_array_fswap(v___y_2518_, v_mid_2516_, v_hi_2501_);
lean_dec(v_mid_2516_);
v___y_2503_ = v___x_2522_;
goto v___jp_2502_;
}
}
v___jp_2523_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v___x_2525_ = lean_array_fget_borrowed(v___y_2524_, v_hi_2501_);
v___x_2526_ = lean_array_fget_borrowed(v___y_2524_, v_lo_2500_);
lean_inc(v___x_2526_);
lean_inc(v___x_2525_);
v___x_2527_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___lam__0(v___x_2513_, v___x_2525_, v___x_2526_);
if (v___x_2527_ == 0)
{
v___y_2518_ = v___y_2524_;
goto v___jp_2517_;
}
else
{
lean_object* v___x_2528_; 
v___x_2528_ = lean_array_fswap(v___y_2524_, v_lo_2500_, v_hi_2501_);
v___y_2518_ = v___x_2528_;
goto v___jp_2517_;
}
}
}
v___jp_2502_:
{
lean_object* v_pivot_2504_; lean_object* v___x_2505_; lean_object* v_fst_2506_; lean_object* v_snd_2507_; uint8_t v___x_2508_; 
v_pivot_2504_ = lean_array_fget(v___y_2503_, v_hi_2501_);
lean_inc_n(v_lo_2500_, 2);
v___x_2505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2501_, v_pivot_2504_, v___y_2503_, v_lo_2500_, v_lo_2500_);
v_fst_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_fst_2506_);
v_snd_2507_ = lean_ctor_get(v___x_2505_, 1);
lean_inc(v_snd_2507_);
lean_dec_ref(v___x_2505_);
v___x_2508_ = lean_nat_dec_le(v_hi_2501_, v_fst_2506_);
if (v___x_2508_ == 0)
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2498_, v_snd_2507_, v_lo_2500_, v_fst_2506_);
v___x_2510_ = lean_unsigned_to_nat(1u);
v___x_2511_ = lean_nat_add(v_fst_2506_, v___x_2510_);
lean_dec(v_fst_2506_);
v_as_2499_ = v___x_2509_;
v_lo_2500_ = v___x_2511_;
goto _start;
}
else
{
lean_dec(v_fst_2506_);
lean_dec(v_lo_2500_);
return v_snd_2507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg___boxed(lean_object* v_n_2533_, lean_object* v_as_2534_, lean_object* v_lo_2535_, lean_object* v_hi_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2533_, v_as_2534_, v_lo_2535_, v_hi_2536_);
lean_dec(v_hi_2536_);
lean_dec(v_n_2533_);
return v_res_2537_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename(lean_object* v_results_2540_, uint8_t v_useErrorFormat_2541_, lean_object* v_a_2542_, lean_object* v_a_2543_){
_start:
{
lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v_size_2599_; lean_object* v_buckets_2600_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v_sp_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; 
if (v_useErrorFormat_2541_ == 0)
{
lean_object* v___x_2644_; 
v___x_2644_ = lean_box(0);
v_sp_2628_ = v___x_2644_;
v___y_2629_ = v_a_2542_;
v___y_2630_ = v_a_2543_;
goto v___jp_2627_;
}
else
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_getSrcSearchPath();
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2645_, 1);
v_sp_2628_ = v_a_2646_;
v___y_2629_ = v_a_2542_;
v___y_2630_ = v_a_2543_;
goto v___jp_2627_;
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2659_; 
v_a_2647_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2649_ = v___x_2645_;
v_isShared_2650_ = v_isSharedCheck_2659_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2645_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2659_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v_ref_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2657_; 
v_ref_2651_ = lean_ctor_get(v_a_2542_, 5);
v___x_2652_ = lean_io_error_to_string(v_a_2647_);
v___x_2653_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
v___x_2654_ = l_Lean_MessageData_ofFormat(v___x_2653_);
lean_inc(v_ref_2651_);
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v_ref_2651_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
if (v_isShared_2650_ == 0)
{
lean_ctor_set(v___x_2649_, 0, v___x_2655_);
v___x_2657_ = v___x_2649_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2655_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
v___jp_2545_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2549_ = lean_array_to_list(v___y_2548_);
v___x_2550_ = lean_box(0);
v___x_2551_ = l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0(v_useErrorFormat_2541_, v___x_2549_, v___x_2550_, v___y_2546_, v___y_2547_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2561_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2554_ = v___x_2551_;
v_isShared_2555_ = v_isSharedCheck_2561_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2561_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2556_ = lean_obj_once(&l_Lean_Linter_EnvLinter_groupedByFilename___closed__0, &l_Lean_Linter_EnvLinter_groupedByFilename___closed__0_once, _init_l_Lean_Linter_EnvLinter_groupedByFilename___closed__0);
v___x_2557_ = l_Lean_MessageData_joinSep(v_a_2552_, v___x_2556_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2557_);
v___x_2559_ = v___x_2554_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
v_a_2562_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2551_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2551_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
v___jp_2570_:
{
lean_object* v___x_2577_; 
v___x_2577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v___y_2573_, v___y_2571_, v___y_2572_, v___y_2576_);
lean_dec(v___y_2576_);
lean_dec(v___y_2573_);
v___y_2546_ = v___y_2574_;
v___y_2547_ = v___y_2575_;
v___y_2548_ = v___x_2577_;
goto v___jp_2545_;
}
v___jp_2578_:
{
uint8_t v___x_2585_; 
v___x_2585_ = lean_nat_dec_le(v___y_2584_, v___y_2583_);
if (v___x_2585_ == 0)
{
lean_dec(v___y_2583_);
lean_inc(v___y_2584_);
v___y_2571_ = v___y_2579_;
v___y_2572_ = v___y_2584_;
v___y_2573_ = v___y_2580_;
v___y_2574_ = v___y_2581_;
v___y_2575_ = v___y_2582_;
v___y_2576_ = v___y_2584_;
goto v___jp_2570_;
}
else
{
v___y_2571_ = v___y_2579_;
v___y_2572_ = v___y_2584_;
v___y_2573_ = v___y_2580_;
v___y_2574_ = v___y_2581_;
v___y_2575_ = v___y_2582_;
v___y_2576_ = v___y_2583_;
goto v___jp_2570_;
}
}
v___jp_2586_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v___x_2590_ = lean_array_get_size(v___y_2589_);
v___x_2591_ = lean_unsigned_to_nat(0u);
v___x_2592_ = lean_nat_dec_eq(v___x_2590_, v___x_2591_);
if (v___x_2592_ == 0)
{
lean_object* v___x_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; 
v___x_2593_ = lean_unsigned_to_nat(1u);
v___x_2594_ = lean_nat_sub(v___x_2590_, v___x_2593_);
v___x_2595_ = lean_nat_dec_le(v___x_2591_, v___x_2594_);
if (v___x_2595_ == 0)
{
lean_inc(v___x_2594_);
v___y_2579_ = v___y_2589_;
v___y_2580_ = v___x_2590_;
v___y_2581_ = v___y_2587_;
v___y_2582_ = v___y_2588_;
v___y_2583_ = v___x_2594_;
v___y_2584_ = v___x_2594_;
goto v___jp_2578_;
}
else
{
v___y_2579_ = v___y_2589_;
v___y_2580_ = v___x_2590_;
v___y_2581_ = v___y_2587_;
v___y_2582_ = v___y_2588_;
v___y_2583_ = v___x_2594_;
v___y_2584_ = v___x_2591_;
goto v___jp_2578_;
}
}
else
{
v___y_2546_ = v___y_2587_;
v___y_2547_ = v___y_2588_;
v___y_2548_ = v___y_2589_;
goto v___jp_2545_;
}
}
v___jp_2596_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2601_ = lean_mk_empty_array_with_capacity(v_size_2599_);
lean_dec(v_size_2599_);
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = lean_array_get_size(v_buckets_2600_);
v___x_2604_ = lean_nat_dec_lt(v___x_2602_, v___x_2603_);
if (v___x_2604_ == 0)
{
lean_dec_ref(v_buckets_2600_);
v___y_2587_ = v___y_2597_;
v___y_2588_ = v___y_2598_;
v___y_2589_ = v___x_2601_;
goto v___jp_2586_;
}
else
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_nat_dec_le(v___x_2603_, v___x_2603_);
if (v___x_2605_ == 0)
{
if (v___x_2604_ == 0)
{
lean_dec_ref(v_buckets_2600_);
v___y_2587_ = v___y_2597_;
v___y_2588_ = v___y_2598_;
v___y_2589_ = v___x_2601_;
goto v___jp_2586_;
}
else
{
size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = ((size_t)0ULL);
v___x_2607_ = lean_usize_of_nat(v___x_2603_);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_2600_, v___x_2606_, v___x_2607_, v___x_2601_);
lean_dec_ref(v_buckets_2600_);
v___y_2587_ = v___y_2597_;
v___y_2588_ = v___y_2598_;
v___y_2589_ = v___x_2608_;
goto v___jp_2586_;
}
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = lean_usize_of_nat(v___x_2603_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__3(v_buckets_2600_, v___x_2609_, v___x_2610_, v___x_2601_);
lean_dec_ref(v_buckets_2600_);
v___y_2587_ = v___y_2597_;
v___y_2588_ = v___y_2598_;
v___y_2589_ = v___x_2611_;
goto v___jp_2586_;
}
}
}
v___jp_2612_:
{
if (lean_obj_tag(v___y_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v_size_2617_; lean_object* v_buckets_2618_; 
v_a_2616_ = lean_ctor_get(v___y_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref_known(v___y_2615_, 1);
v_size_2617_ = lean_ctor_get(v_a_2616_, 0);
lean_inc(v_size_2617_);
v_buckets_2618_ = lean_ctor_get(v_a_2616_, 1);
lean_inc_ref(v_buckets_2618_);
lean_dec(v_a_2616_);
v___y_2597_ = v___y_2613_;
v___y_2598_ = v___y_2614_;
v_size_2599_ = v_size_2617_;
v_buckets_2600_ = v_buckets_2618_;
goto v___jp_2596_;
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
v_a_2619_ = lean_ctor_get(v___y_2615_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___y_2615_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___y_2615_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___y_2615_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
v___jp_2627_:
{
lean_object* v_buckets_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; uint8_t v___x_2635_; 
v_buckets_2631_ = lean_ctor_get(v_results_2540_, 1);
v___x_2632_ = lean_unsigned_to_nat(0u);
v___x_2633_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__0);
v___x_2634_ = lean_array_get_size(v_buckets_2631_);
v___x_2635_ = lean_nat_dec_lt(v___x_2632_, v___x_2634_);
if (v___x_2635_ == 0)
{
lean_dec(v_sp_2628_);
v___y_2597_ = v___y_2629_;
v___y_2598_ = v___y_2630_;
v_size_2599_ = v___x_2632_;
v_buckets_2600_ = v___x_2633_;
goto v___jp_2596_;
}
else
{
lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2636_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_lintCore_spec__6___closed__1);
v___x_2637_ = lean_nat_dec_le(v___x_2634_, v___x_2634_);
if (v___x_2637_ == 0)
{
if (v___x_2635_ == 0)
{
lean_dec(v_sp_2628_);
v___y_2597_ = v___y_2629_;
v___y_2598_ = v___y_2630_;
v_size_2599_ = v___x_2632_;
v_buckets_2600_ = v___x_2633_;
goto v___jp_2596_;
}
else
{
size_t v___x_2638_; size_t v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = ((size_t)0ULL);
v___x_2639_ = lean_usize_of_nat(v___x_2634_);
v___x_2640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_2541_, v_sp_2628_, v_buckets_2631_, v___x_2638_, v___x_2639_, v___x_2636_, v___y_2629_, v___y_2630_);
v___y_2613_ = v___y_2629_;
v___y_2614_ = v___y_2630_;
v___y_2615_ = v___x_2640_;
goto v___jp_2612_;
}
}
else
{
size_t v___x_2641_; size_t v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = ((size_t)0ULL);
v___x_2642_ = lean_usize_of_nat(v___x_2634_);
v___x_2643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__7(v_useErrorFormat_2541_, v_sp_2628_, v_buckets_2631_, v___x_2641_, v___x_2642_, v___x_2636_, v___y_2629_, v___y_2630_);
v___y_2613_ = v___y_2629_;
v___y_2614_ = v___y_2630_;
v___y_2615_ = v___x_2643_;
goto v___jp_2612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_groupedByFilename___boxed(lean_object* v_results_2660_, lean_object* v_useErrorFormat_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
uint8_t v_useErrorFormat_boxed_2665_; lean_object* v_res_2666_; 
v_useErrorFormat_boxed_2665_ = lean_unbox(v_useErrorFormat_2661_);
v_res_2666_ = l_Lean_Linter_EnvLinter_groupedByFilename(v_results_2660_, v_useErrorFormat_boxed_2665_, v_a_2662_, v_a_2663_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec_ref(v_results_2660_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(lean_object* v_n_2667_, lean_object* v_as_2668_, lean_object* v_lo_2669_, lean_object* v_hi_2670_, lean_object* v_w_2671_, lean_object* v_hlo_2672_, lean_object* v_hhi_2673_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___redArg(v_n_2667_, v_as_2668_, v_lo_2669_, v_hi_2670_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1___boxed(lean_object* v_n_2675_, lean_object* v_as_2676_, lean_object* v_lo_2677_, lean_object* v_hi_2678_, lean_object* v_w_2679_, lean_object* v_hlo_2680_, lean_object* v_hhi_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1(v_n_2675_, v_as_2676_, v_lo_2677_, v_hi_2678_, v_w_2679_, v_hlo_2680_, v_hhi_2681_);
lean_dec(v_hi_2678_);
lean_dec(v_n_2675_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(lean_object* v_00_u03b2_2683_, lean_object* v_m_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v_m_2684_, v_a_2685_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___boxed(lean_object* v_00_u03b2_2687_, lean_object* v_m_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v_res_2690_; 
v_res_2690_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5(v_00_u03b2_2687_, v_m_2688_, v_a_2689_);
lean_dec(v_a_2689_);
lean_dec_ref(v_m_2688_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(lean_object* v_n_2691_, lean_object* v_lo_2692_, lean_object* v_hi_2693_, lean_object* v_hhi_2694_, lean_object* v_pivot_2695_, lean_object* v_as_2696_, lean_object* v_i_2697_, lean_object* v_k_2698_, lean_object* v_ilo_2699_, lean_object* v_ik_2700_, lean_object* v_w_2701_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___redArg(v_hi_2693_, v_pivot_2695_, v_as_2696_, v_i_2697_, v_k_2698_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1___boxed(lean_object* v_n_2703_, lean_object* v_lo_2704_, lean_object* v_hi_2705_, lean_object* v_hhi_2706_, lean_object* v_pivot_2707_, lean_object* v_as_2708_, lean_object* v_i_2709_, lean_object* v_k_2710_, lean_object* v_ilo_2711_, lean_object* v_ik_2712_, lean_object* v_w_2713_){
_start:
{
lean_object* v_res_2714_; 
v_res_2714_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__1_spec__1(v_n_2703_, v_lo_2704_, v_hi_2705_, v_hhi_2706_, v_pivot_2707_, v_as_2708_, v_i_2709_, v_k_2710_, v_ilo_2711_, v_ik_2712_, v_w_2713_);
lean_dec(v_hi_2705_);
lean_dec(v_lo_2704_);
lean_dec(v_n_2703_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(lean_object* v_00_u03b2_2715_, lean_object* v_a_2716_, lean_object* v_x_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___redArg(v_a_2716_, v_x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7___boxed(lean_object* v_00_u03b2_2719_, lean_object* v_a_2720_, lean_object* v_x_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5_spec__7(v_00_u03b2_2719_, v_a_2720_, v_x_2721_);
lean_dec(v_x_2721_);
lean_dec(v_a_2720_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(size_t v_sz_2723_, size_t v_i_2724_, lean_object* v_bs_2725_){
_start:
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_usize_dec_lt(v_i_2724_, v_sz_2723_);
if (v___x_2726_ == 0)
{
return v_bs_2725_;
}
else
{
lean_object* v_v_2727_; lean_object* v_snd_2728_; lean_object* v_size_2729_; lean_object* v___x_2730_; lean_object* v_bs_x27_2731_; size_t v___x_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
v_v_2727_ = lean_array_uget_borrowed(v_bs_2725_, v_i_2724_);
v_snd_2728_ = lean_ctor_get(v_v_2727_, 1);
v_size_2729_ = lean_ctor_get(v_snd_2728_, 0);
lean_inc(v_size_2729_);
v___x_2730_ = lean_unsigned_to_nat(0u);
v_bs_x27_2731_ = lean_array_uset(v_bs_2725_, v_i_2724_, v___x_2730_);
v___x_2732_ = ((size_t)1ULL);
v___x_2733_ = lean_usize_add(v_i_2724_, v___x_2732_);
v___x_2734_ = lean_array_uset(v_bs_x27_2731_, v_i_2724_, v_size_2729_);
v_i_2724_ = v___x_2733_;
v_bs_2725_ = v___x_2734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1___boxed(lean_object* v_sz_2736_, lean_object* v_i_2737_, lean_object* v_bs_2738_){
_start:
{
size_t v_sz_boxed_2739_; size_t v_i_boxed_2740_; lean_object* v_res_2741_; 
v_sz_boxed_2739_ = lean_unbox_usize(v_sz_2736_);
lean_dec(v_sz_2736_);
v_i_boxed_2740_ = lean_unbox_usize(v_i_2737_);
lean_dec(v_i_2737_);
v_res_2741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_boxed_2739_, v_i_boxed_2740_, v_bs_2738_);
return v_res_2741_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__0));
v___x_2744_ = l_Lean_stringToMessageData(v___x_2743_);
return v___x_2744_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__2));
v___x_2747_ = l_Lean_stringToMessageData(v___x_2746_);
return v___x_2747_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__4));
v___x_2750_ = l_Lean_stringToMessageData(v___x_2749_);
return v___x_2750_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__6));
v___x_2753_ = l_Lean_stringToMessageData(v___x_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(uint8_t v_useErrorFormat_2754_, uint8_t v_groupByFilename_2755_, uint8_t v_verbose_2756_, lean_object* v_as_2757_, size_t v_i_2758_, size_t v_stop_2759_, lean_object* v_b_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_a_2765_; lean_object* v_val_2770_; uint8_t v___x_2772_; 
v___x_2772_ = lean_usize_dec_eq(v_i_2758_, v_stop_2759_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; lean_object* v_fst_2774_; lean_object* v_snd_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2838_; 
v___x_2773_ = lean_array_uget(v_as_2757_, v_i_2758_);
v_fst_2774_ = lean_ctor_get(v___x_2773_, 0);
v_snd_2775_ = lean_ctor_get(v___x_2773_, 1);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2777_ = v___x_2773_;
v_isShared_2778_ = v_isSharedCheck_2838_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_snd_2775_);
lean_inc(v_fst_2774_);
lean_dec(v___x_2773_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2838_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v_warnings_2780_; lean_object* v_size_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
v_size_2808_ = lean_ctor_get(v_snd_2775_, 0);
v___x_2809_ = lean_unsigned_to_nat(0u);
v___x_2810_ = lean_nat_dec_eq(v_size_2808_, v___x_2809_);
if (v___x_2810_ == 0)
{
if (v_groupByFilename_2755_ == 0)
{
if (v_useErrorFormat_2754_ == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___x_2812_ = l_Lean_Linter_EnvLinter_printWarnings(v_snd_2775_, v___x_2811_, v_useErrorFormat_2754_, v___y_2761_, v___y_2762_);
lean_dec(v_snd_2775_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v_warnings_2780_ = v_a_2813_;
goto v___jp_2779_;
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_del_object(v___x_2777_);
lean_dec(v_fst_2774_);
lean_dec_ref(v_b_2760_);
v_a_2814_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2812_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2812_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
else
{
goto v___jp_2797_;
}
}
else
{
goto v___jp_2797_;
}
}
else
{
lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2835_; 
lean_del_object(v___x_2777_);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_snd_2775_);
if (v_isSharedCheck_2835_ == 0)
{
lean_object* v_unused_2836_; lean_object* v_unused_2837_; 
v_unused_2836_ = lean_ctor_get(v_snd_2775_, 1);
lean_dec(v_unused_2836_);
v_unused_2837_ = lean_ctor_get(v_snd_2775_, 0);
lean_dec(v_unused_2837_);
v___x_2823_ = v_snd_2775_;
v_isShared_2824_ = v_isSharedCheck_2835_;
goto v_resetjp_2822_;
}
else
{
lean_dec(v_snd_2775_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2835_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
uint8_t v___x_2825_; uint8_t v___x_2826_; 
v___x_2825_ = 2;
v___x_2826_ = l_Lean_Linter_EnvLinter_instDecidableEqLintVerbosity(v_verbose_2756_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_del_object(v___x_2823_);
lean_dec(v_fst_2774_);
v_a_2765_ = v_b_2760_;
goto v___jp_2764_;
}
else
{
lean_object* v_toEnvLinter_2827_; lean_object* v_noErrorsFound_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
v_toEnvLinter_2827_ = lean_ctor_get(v_fst_2774_, 0);
lean_inc_ref(v_toEnvLinter_2827_);
lean_dec(v_fst_2774_);
v_noErrorsFound_2828_ = lean_ctor_get(v_toEnvLinter_2827_, 1);
lean_inc_ref(v_noErrorsFound_2828_);
lean_dec_ref(v_toEnvLinter_2827_);
v___x_2829_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__7);
if (v_isShared_2824_ == 0)
{
lean_ctor_set_tag(v___x_2823_, 7);
lean_ctor_set(v___x_2823_, 1, v_noErrorsFound_2828_);
lean_ctor_set(v___x_2823_, 0, v___x_2829_);
v___x_2831_ = v___x_2823_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2834_, 1, v_noErrorsFound_2828_);
v___x_2831_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarning___closed__5, &l_Lean_Linter_EnvLinter_printWarning___closed__5_once, _init_l_Lean_Linter_EnvLinter_printWarning___closed__5);
v___x_2833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v_val_2770_ = v___x_2833_;
goto v___jp_2769_;
}
}
}
}
v___jp_2779_:
{
lean_object* v_toEnvLinter_2781_; lean_object* v_name_2782_; lean_object* v_errorsFound_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2787_; 
v_toEnvLinter_2781_ = lean_ctor_get(v_fst_2774_, 0);
lean_inc_ref(v_toEnvLinter_2781_);
v_name_2782_ = lean_ctor_get(v_fst_2774_, 1);
lean_inc(v_name_2782_);
lean_dec(v_fst_2774_);
v_errorsFound_2783_ = lean_ctor_get(v_toEnvLinter_2781_, 2);
lean_inc_ref(v_errorsFound_2783_);
lean_dec_ref(v_toEnvLinter_2781_);
v___x_2784_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__1);
v___x_2785_ = l_Lean_MessageData_ofName(v_name_2782_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set_tag(v___x_2777_, 7);
lean_ctor_set(v___x_2777_, 1, v___x_2785_);
lean_ctor_set(v___x_2777_, 0, v___x_2784_);
v___x_2787_ = v___x_2777_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2788_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__3);
v___x_2789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2787_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v_errorsFound_2783_);
v___x_2791_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___closed__5);
v___x_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2790_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v_warnings_2780_);
v___x_2794_ = lean_obj_once(&l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3, &l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3_once, _init_l_List_mapM_loop___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__0___closed__3);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v_val_2770_ = v___x_2795_;
goto v___jp_2769_;
}
}
v___jp_2797_:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Lean_Linter_EnvLinter_groupedByFilename(v_snd_2775_, v_useErrorFormat_2754_, v___y_2761_, v___y_2762_);
lean_dec(v_snd_2775_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2798_, 1);
v_warnings_2780_ = v_a_2799_;
goto v___jp_2779_;
}
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_del_object(v___x_2777_);
lean_dec(v_fst_2774_);
lean_dec_ref(v_b_2760_);
v_a_2800_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2798_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2798_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
}
}
else
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2839_, 0, v_b_2760_);
return v___x_2839_;
}
v___jp_2764_:
{
size_t v___x_2766_; size_t v___x_2767_; 
v___x_2766_ = ((size_t)1ULL);
v___x_2767_ = lean_usize_add(v_i_2758_, v___x_2766_);
v_i_2758_ = v___x_2767_;
v_b_2760_ = v_a_2765_;
goto _start;
}
v___jp_2769_:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_array_push(v_b_2760_, v_val_2770_);
v_a_2765_ = v___x_2771_;
goto v___jp_2764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0___boxed(lean_object* v_useErrorFormat_2840_, lean_object* v_groupByFilename_2841_, lean_object* v_verbose_2842_, lean_object* v_as_2843_, lean_object* v_i_2844_, lean_object* v_stop_2845_, lean_object* v_b_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_){
_start:
{
uint8_t v_useErrorFormat_boxed_2850_; uint8_t v_groupByFilename_boxed_2851_; uint8_t v_verbose_boxed_2852_; size_t v_i_boxed_2853_; size_t v_stop_boxed_2854_; lean_object* v_res_2855_; 
v_useErrorFormat_boxed_2850_ = lean_unbox(v_useErrorFormat_2840_);
v_groupByFilename_boxed_2851_ = lean_unbox(v_groupByFilename_2841_);
v_verbose_boxed_2852_ = lean_unbox(v_verbose_2842_);
v_i_boxed_2853_ = lean_unbox_usize(v_i_2844_);
lean_dec(v_i_2844_);
v_stop_boxed_2854_ = lean_unbox_usize(v_stop_2845_);
lean_dec(v_stop_2845_);
v_res_2855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_boxed_2850_, v_groupByFilename_boxed_2851_, v_verbose_boxed_2852_, v_as_2843_, v_i_boxed_2853_, v_stop_boxed_2854_, v_b_2846_, v___y_2847_, v___y_2848_);
lean_dec(v___y_2848_);
lean_dec_ref(v___y_2847_);
lean_dec_ref(v_as_2843_);
return v_res_2855_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(uint8_t v_useErrorFormat_2858_, uint8_t v_groupByFilename_2859_, uint8_t v_verbose_2860_, lean_object* v_as_2861_, lean_object* v_start_2862_, lean_object* v_stop_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2867_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___closed__0));
v___x_2868_ = lean_nat_dec_lt(v_start_2862_, v_stop_2863_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; 
v___x_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
return v___x_2869_;
}
else
{
lean_object* v___x_2870_; uint8_t v___x_2871_; 
v___x_2870_ = lean_array_get_size(v_as_2861_);
v___x_2871_ = lean_nat_dec_le(v_stop_2863_, v___x_2870_);
if (v___x_2871_ == 0)
{
uint8_t v___x_2872_; 
v___x_2872_ = lean_nat_dec_lt(v_start_2862_, v___x_2870_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; 
v___x_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2873_, 0, v___x_2867_);
return v___x_2873_;
}
else
{
size_t v___x_2874_; size_t v___x_2875_; lean_object* v___x_2876_; 
v___x_2874_ = lean_usize_of_nat(v_start_2862_);
v___x_2875_ = lean_usize_of_nat(v___x_2870_);
v___x_2876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_2858_, v_groupByFilename_2859_, v_verbose_2860_, v_as_2861_, v___x_2874_, v___x_2875_, v___x_2867_, v___y_2864_, v___y_2865_);
return v___x_2876_;
}
}
else
{
size_t v___x_2877_; size_t v___x_2878_; lean_object* v___x_2879_; 
v___x_2877_ = lean_usize_of_nat(v_start_2862_);
v___x_2878_ = lean_usize_of_nat(v_stop_2863_);
v___x_2879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0_spec__0(v_useErrorFormat_2858_, v_groupByFilename_2859_, v_verbose_2860_, v_as_2861_, v___x_2877_, v___x_2878_, v___x_2867_, v___y_2864_, v___y_2865_);
return v___x_2879_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0___boxed(lean_object* v_useErrorFormat_2880_, lean_object* v_groupByFilename_2881_, lean_object* v_verbose_2882_, lean_object* v_as_2883_, lean_object* v_start_2884_, lean_object* v_stop_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
uint8_t v_useErrorFormat_boxed_2889_; uint8_t v_groupByFilename_boxed_2890_; uint8_t v_verbose_boxed_2891_; lean_object* v_res_2892_; 
v_useErrorFormat_boxed_2889_ = lean_unbox(v_useErrorFormat_2880_);
v_groupByFilename_boxed_2890_ = lean_unbox(v_groupByFilename_2881_);
v_verbose_boxed_2891_ = lean_unbox(v_verbose_2882_);
v_res_2892_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(v_useErrorFormat_boxed_2889_, v_groupByFilename_boxed_2890_, v_verbose_boxed_2891_, v_as_2883_, v_start_2884_, v_stop_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v_stop_2885_);
lean_dec(v_start_2884_);
lean_dec_ref(v_as_2883_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(lean_object* v_as_2893_, size_t v_i_2894_, size_t v_stop_2895_, lean_object* v_b_2896_){
_start:
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_usize_dec_eq(v_i_2894_, v_stop_2895_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; size_t v___x_2900_; size_t v___x_2901_; 
v___x_2898_ = lean_array_uget_borrowed(v_as_2893_, v_i_2894_);
v___x_2899_ = lean_nat_add(v_b_2896_, v___x_2898_);
lean_dec(v_b_2896_);
v___x_2900_ = ((size_t)1ULL);
v___x_2901_ = lean_usize_add(v_i_2894_, v___x_2900_);
v_i_2894_ = v___x_2901_;
v_b_2896_ = v___x_2899_;
goto _start;
}
else
{
return v_b_2896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2___boxed(lean_object* v_as_2903_, lean_object* v_i_2904_, lean_object* v_stop_2905_, lean_object* v_b_2906_){
_start:
{
size_t v_i_boxed_2907_; size_t v_stop_boxed_2908_; lean_object* v_res_2909_; 
v_i_boxed_2907_ = lean_unbox_usize(v_i_2904_);
lean_dec(v_i_2904_);
v_stop_boxed_2908_ = lean_unbox_usize(v_stop_2905_);
lean_dec(v_stop_2905_);
v_res_2909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v_as_2903_, v_i_boxed_2907_, v_stop_boxed_2908_, v_b_2906_);
lean_dec_ref(v_as_2903_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(lean_object* v_as_2910_, size_t v_i_2911_, size_t v_stop_2912_, lean_object* v_b_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v___x_2916_; 
v___x_2916_ = lean_usize_dec_eq(v_i_2911_, v_stop_2912_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; 
v___x_2917_ = lean_array_uget_borrowed(v_as_2910_, v_i_2911_);
lean_inc(v___x_2917_);
v___x_2918_ = l_Lean_Linter_EnvLinter_isAutoDecl___redArg(v___x_2917_, v___y_2914_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v_a_2921_; uint8_t v___x_2925_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
lean_dec_ref_known(v___x_2918_, 1);
v___x_2925_ = lean_unbox(v_a_2919_);
lean_dec(v_a_2919_);
if (v___x_2925_ == 0)
{
v_a_2921_ = v_b_2913_;
goto v___jp_2920_;
}
else
{
lean_object* v___x_2926_; 
lean_inc(v___x_2917_);
v___x_2926_ = lean_array_push(v_b_2913_, v___x_2917_);
v_a_2921_ = v___x_2926_;
goto v___jp_2920_;
}
v___jp_2920_:
{
size_t v___x_2922_; size_t v___x_2923_; 
v___x_2922_ = ((size_t)1ULL);
v___x_2923_ = lean_usize_add(v_i_2911_, v___x_2922_);
v_i_2911_ = v___x_2923_;
v_b_2913_ = v_a_2921_;
goto _start;
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec_ref(v_b_2913_);
v_a_2927_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2918_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2918_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
else
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2935_, 0, v_b_2913_);
return v___x_2935_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg___boxed(lean_object* v_as_2936_, lean_object* v_i_2937_, lean_object* v_stop_2938_, lean_object* v_b_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
size_t v_i_boxed_2942_; size_t v_stop_boxed_2943_; lean_object* v_res_2944_; 
v_i_boxed_2942_ = lean_unbox_usize(v_i_2937_);
lean_dec(v_i_2937_);
v_stop_boxed_2943_ = lean_unbox_usize(v_stop_2938_);
lean_dec(v_stop_2938_);
v_res_2944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_2936_, v_i_boxed_2942_, v_stop_boxed_2943_, v_b_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v_as_2936_);
return v_res_2944_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__0));
v___x_2947_ = l_Lean_stringToMessageData(v___x_2946_);
return v___x_2947_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__2));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5(void){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__4));
v___x_2953_ = l_Lean_stringToMessageData(v___x_2952_);
return v___x_2953_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7(void){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__6));
v___x_2956_ = l_Lean_stringToMessageData(v___x_2955_);
return v___x_2956_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9(void){
_start:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___x_2958_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__8));
v___x_2959_ = l_Lean_stringToMessageData(v___x_2958_);
return v___x_2959_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2961_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__10));
v___x_2962_ = l_Lean_stringToMessageData(v___x_2961_);
return v___x_2962_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2964_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__12));
v___x_2965_ = l_Lean_stringToMessageData(v___x_2964_);
return v___x_2965_;
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__15(void){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__14));
v___x_2968_ = l_Lean_stringToMessageData(v___x_2967_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults(lean_object* v_results_2970_, lean_object* v_decls_2971_, uint8_t v_groupByFilename_2972_, lean_object* v_whereDesc_2973_, uint8_t v_scope_2974_, uint8_t v_verbose_2975_, lean_object* v_numLinters_2976_, uint8_t v_useErrorFormat_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v_s_2982_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = lean_unsigned_to_nat(0u);
v___x_2988_ = lean_array_get_size(v_results_2970_);
v___x_2989_ = l_Array_filterMapM___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__0(v_useErrorFormat_2977_, v_groupByFilename_2972_, v_verbose_2975_, v_results_2970_, v___x_2987_, v___x_2988_, v_a_2978_, v_a_2979_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v_a_3042_; lean_object* v___y_3055_; lean_object* v___x_3065_; uint8_t v___x_3066_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = lean_array_to_list(v_a_2990_);
v___x_2992_ = lean_obj_once(&l_Lean_Linter_EnvLinter_printWarnings___closed__0, &l_Lean_Linter_EnvLinter_printWarnings___closed__0_once, _init_l_Lean_Linter_EnvLinter_printWarnings___closed__0);
v___x_2993_ = l_Lean_MessageData_joinSep(v___x_2991_, v___x_2992_);
v___x_2994_ = lean_array_get_size(v_decls_2971_);
v___x_3065_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___x_3066_ = lean_nat_dec_lt(v___x_2987_, v___x_2994_);
if (v___x_3066_ == 0)
{
v_a_3042_ = v___x_3065_;
goto v___jp_3041_;
}
else
{
uint8_t v___x_3067_; 
v___x_3067_ = lean_nat_dec_le(v___x_2994_, v___x_2994_);
if (v___x_3067_ == 0)
{
if (v___x_3066_ == 0)
{
v_a_3042_ = v___x_3065_;
goto v___jp_3041_;
}
else
{
size_t v___x_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v___x_3068_ = ((size_t)0ULL);
v___x_3069_ = lean_usize_of_nat(v___x_2994_);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_2971_, v___x_3068_, v___x_3069_, v___x_3065_, v_a_2979_);
v___y_3055_ = v___x_3070_;
goto v___jp_3054_;
}
}
else
{
size_t v___x_3071_; size_t v___x_3072_; lean_object* v___x_3073_; 
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = lean_usize_of_nat(v___x_2994_);
v___x_3073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_decls_2971_, v___x_3071_, v___x_3072_, v___x_3065_, v_a_2979_);
v___y_3055_ = v___x_3073_;
goto v___jp_3054_;
}
}
v___jp_2995_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
lean_inc_ref(v___y_2998_);
v___x_2999_ = l_Lean_stringToMessageData(v___y_2998_);
v___x_3000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3000_, 0, v___y_2996_);
lean_ctor_set(v___x_3000_, 1, v___x_2999_);
v___x_3001_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__3, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__3_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__3);
v___x_3002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3000_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = lean_nat_sub(v___x_2994_, v___y_2997_);
v___x_3004_ = l_Nat_reprFast(v___x_3003_);
v___x_3005_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3004_);
v___x_3006_ = l_Lean_MessageData_ofFormat(v___x_3005_);
v___x_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3002_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__5, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__5_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__5);
v___x_3009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3007_);
lean_ctor_set(v___x_3009_, 1, v___x_3008_);
v___x_3010_ = l_Nat_reprFast(v___y_2997_);
v___x_3011_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
v___x_3012_ = l_Lean_MessageData_ofFormat(v___x_3011_);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3009_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__7, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__7_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__7);
v___x_3015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = l_Lean_stringToMessageData(v_whereDesc_2973_);
v___x_3017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3015_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__9, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__9_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__9);
v___x_3019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3017_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
v___x_3020_ = l_Nat_reprFast(v_numLinters_2976_);
v___x_3021_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3021_, 0, v___x_3020_);
v___x_3022_ = l_Lean_MessageData_ofFormat(v___x_3021_);
v___x_3023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3019_);
lean_ctor_set(v___x_3023_, 1, v___x_3022_);
v___x_3024_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__11, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__11_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__11);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
lean_ctor_set(v___x_3026_, 1, v___x_2993_);
v_s_2982_ = v___x_3026_;
goto v___jp_2981_;
}
v___jp_3027_:
{
if (v_verbose_2975_ == 0)
{
lean_dec(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec(v_numLinters_2976_);
lean_dec_ref(v_whereDesc_2973_);
v_s_2982_ = v___x_2993_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3030_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__13, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__13_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__13);
lean_inc(v___y_3029_);
v___x_3031_ = l_Nat_reprFast(v___y_3029_);
v___x_3032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
v___x_3033_ = l_Lean_MessageData_ofFormat(v___x_3032_);
v___x_3034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3030_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
v___x_3035_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__15, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__15_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__15);
v___x_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_unsigned_to_nat(1u);
v___x_3038_ = lean_nat_dec_eq(v___y_3029_, v___x_3037_);
lean_dec(v___y_3029_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; 
v___x_3039_ = ((lean_object*)(l_Lean_Linter_EnvLinter_formatLinterResults___closed__16));
v___y_2996_ = v___x_3036_;
v___y_2997_ = v___y_3028_;
v___y_2998_ = v___x_3039_;
goto v___jp_2995_;
}
else
{
lean_object* v___x_3040_; 
v___x_3040_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__6___closed__0));
v___y_2996_ = v___x_3036_;
v___y_2997_ = v___y_3028_;
v___y_2998_ = v___x_3040_;
goto v___jp_2995_;
}
}
}
v___jp_3041_:
{
lean_object* v___x_3043_; size_t v_sz_3044_; size_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3043_ = lean_array_get_size(v_a_3042_);
lean_dec_ref(v_a_3042_);
v_sz_3044_ = lean_array_size(v_results_2970_);
v___x_3045_ = ((size_t)0ULL);
v___x_3046_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__1(v_sz_3044_, v___x_3045_, v_results_2970_);
v___x_3047_ = lean_array_get_size(v___x_3046_);
v___x_3048_ = lean_nat_dec_lt(v___x_2987_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_dec_ref(v___x_3046_);
v___y_3028_ = v___x_3043_;
v___y_3029_ = v___x_2987_;
goto v___jp_3027_;
}
else
{
uint8_t v___x_3049_; 
v___x_3049_ = lean_nat_dec_le(v___x_3047_, v___x_3047_);
if (v___x_3049_ == 0)
{
if (v___x_3048_ == 0)
{
lean_dec_ref(v___x_3046_);
v___y_3028_ = v___x_3043_;
v___y_3029_ = v___x_2987_;
goto v___jp_3027_;
}
else
{
size_t v___x_3050_; lean_object* v___x_3051_; 
v___x_3050_ = lean_usize_of_nat(v___x_3047_);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_3046_, v___x_3045_, v___x_3050_, v___x_2987_);
lean_dec_ref(v___x_3046_);
v___y_3028_ = v___x_3043_;
v___y_3029_ = v___x_3051_;
goto v___jp_3027_;
}
}
else
{
size_t v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_usize_of_nat(v___x_3047_);
v___x_3053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__2(v___x_3046_, v___x_3045_, v___x_3052_, v___x_2987_);
lean_dec_ref(v___x_3046_);
v___y_3028_ = v___x_3043_;
v___y_3029_ = v___x_3053_;
goto v___jp_3027_;
}
}
}
v___jp_3054_:
{
if (lean_obj_tag(v___y_3055_) == 0)
{
lean_object* v_a_3056_; 
v_a_3056_ = lean_ctor_get(v___y_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___y_3055_, 1);
v_a_3042_ = v_a_3056_;
goto v___jp_3041_;
}
else
{
lean_object* v_a_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3064_; 
lean_dec_ref(v___x_2993_);
lean_dec(v_numLinters_2976_);
lean_dec_ref(v_whereDesc_2973_);
lean_dec_ref(v_results_2970_);
v_a_3057_ = lean_ctor_get(v___y_3055_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___y_3055_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3059_ = v___y_3055_;
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_a_3057_);
lean_dec(v___y_3055_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3064_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3062_; 
if (v_isShared_3060_ == 0)
{
v___x_3062_ = v___x_3059_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_a_3057_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v_numLinters_2976_);
lean_dec_ref(v_whereDesc_2973_);
lean_dec_ref(v_results_2970_);
v_a_3074_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_2989_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_2989_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
v___jp_2981_:
{
if (v_scope_2974_ == 0)
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = lean_obj_once(&l_Lean_Linter_EnvLinter_formatLinterResults___closed__1, &l_Lean_Linter_EnvLinter_formatLinterResults___closed__1_once, _init_l_Lean_Linter_EnvLinter_formatLinterResults___closed__1);
v___x_2984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2984_, 0, v_s_2982_);
lean_ctor_set(v___x_2984_, 1, v___x_2983_);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
else
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_s_2982_);
return v___x_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_formatLinterResults___boxed(lean_object* v_results_3082_, lean_object* v_decls_3083_, lean_object* v_groupByFilename_3084_, lean_object* v_whereDesc_3085_, lean_object* v_scope_3086_, lean_object* v_verbose_3087_, lean_object* v_numLinters_3088_, lean_object* v_useErrorFormat_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_){
_start:
{
uint8_t v_groupByFilename_boxed_3093_; uint8_t v_scope_boxed_3094_; uint8_t v_verbose_boxed_3095_; uint8_t v_useErrorFormat_boxed_3096_; lean_object* v_res_3097_; 
v_groupByFilename_boxed_3093_ = lean_unbox(v_groupByFilename_3084_);
v_scope_boxed_3094_ = lean_unbox(v_scope_3086_);
v_verbose_boxed_3095_ = lean_unbox(v_verbose_3087_);
v_useErrorFormat_boxed_3096_ = lean_unbox(v_useErrorFormat_3089_);
v_res_3097_ = l_Lean_Linter_EnvLinter_formatLinterResults(v_results_3082_, v_decls_3083_, v_groupByFilename_boxed_3093_, v_whereDesc_3085_, v_scope_boxed_3094_, v_verbose_boxed_3095_, v_numLinters_3088_, v_useErrorFormat_boxed_3096_, v_a_3090_, v_a_3091_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
lean_dec_ref(v_decls_3083_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(lean_object* v_as_3098_, size_t v_i_3099_, size_t v_stop_3100_, lean_object* v_b_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v___x_3105_; 
v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___redArg(v_as_3098_, v_i_3099_, v_stop_3100_, v_b_3101_, v___y_3103_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3___boxed(lean_object* v_as_3106_, lean_object* v_i_3107_, lean_object* v_stop_3108_, lean_object* v_b_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
size_t v_i_boxed_3113_; size_t v_stop_boxed_3114_; lean_object* v_res_3115_; 
v_i_boxed_3113_ = lean_unbox_usize(v_i_3107_);
lean_dec(v_i_3107_);
v_stop_boxed_3114_ = lean_unbox_usize(v_stop_3108_);
lean_dec(v_stop_3108_);
v_res_3115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_formatLinterResults_spec__3(v_as_3106_, v_i_boxed_3113_, v_stop_boxed_3114_, v_b_3109_, v___y_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec_ref(v_as_3106_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(lean_object* v_r_3116_, lean_object* v_k_3117_, lean_object* v_x_3118_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = lean_array_push(v_r_3116_, v_k_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0___boxed(lean_object* v_r_3120_, lean_object* v_k_3121_, lean_object* v_x_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___lam__0(v_r_3120_, v_k_3121_, v_x_3122_);
lean_dec_ref(v_x_3122_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0(lean_object* v_f_3124_, lean_object* v_x1_3125_, lean_object* v_x2_3126_, lean_object* v_x3_3127_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = lean_apply_3(v_f_3124_, v_x1_3125_, v_x2_3126_, v_x3_3127_);
return v___x_3128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_3129_, lean_object* v_keys_3130_, lean_object* v_vals_3131_, lean_object* v_i_3132_, lean_object* v_acc_3133_){
_start:
{
lean_object* v___x_3134_; uint8_t v___x_3135_; 
v___x_3134_ = lean_array_get_size(v_keys_3130_);
v___x_3135_ = lean_nat_dec_lt(v_i_3132_, v___x_3134_);
if (v___x_3135_ == 0)
{
lean_dec(v_i_3132_);
lean_dec(v_f_3129_);
return v_acc_3133_;
}
else
{
lean_object* v_k_3136_; lean_object* v_v_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v_k_3136_ = lean_array_fget_borrowed(v_keys_3130_, v_i_3132_);
v_v_3137_ = lean_array_fget_borrowed(v_vals_3131_, v_i_3132_);
lean_inc(v_f_3129_);
lean_inc(v_v_3137_);
lean_inc(v_k_3136_);
v___x_3138_ = lean_apply_3(v_f_3129_, v_acc_3133_, v_k_3136_, v_v_3137_);
v___x_3139_ = lean_unsigned_to_nat(1u);
v___x_3140_ = lean_nat_add(v_i_3132_, v___x_3139_);
lean_dec(v_i_3132_);
v_i_3132_ = v___x_3140_;
v_acc_3133_ = v___x_3138_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_3142_, lean_object* v_keys_3143_, lean_object* v_vals_3144_, lean_object* v_i_3145_, lean_object* v_acc_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3142_, v_keys_3143_, v_vals_3144_, v_i_3145_, v_acc_3146_);
lean_dec_ref(v_vals_3144_);
lean_dec_ref(v_keys_3143_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(lean_object* v_f_3148_, lean_object* v_x_3149_, lean_object* v_x_3150_){
_start:
{
if (lean_obj_tag(v_x_3149_) == 0)
{
lean_object* v_es_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v_es_3151_ = lean_ctor_get(v_x_3149_, 0);
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = lean_array_get_size(v_es_3151_);
v___x_3154_ = lean_nat_dec_lt(v___x_3152_, v___x_3153_);
if (v___x_3154_ == 0)
{
lean_dec(v_f_3148_);
return v_x_3150_;
}
else
{
uint8_t v___x_3155_; 
v___x_3155_ = lean_nat_dec_le(v___x_3153_, v___x_3153_);
if (v___x_3155_ == 0)
{
if (v___x_3154_ == 0)
{
lean_dec(v_f_3148_);
return v_x_3150_;
}
else
{
size_t v___x_3156_; size_t v___x_3157_; lean_object* v___x_3158_; 
v___x_3156_ = ((size_t)0ULL);
v___x_3157_ = lean_usize_of_nat(v___x_3153_);
v___x_3158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3148_, v_es_3151_, v___x_3156_, v___x_3157_, v_x_3150_);
return v___x_3158_;
}
}
else
{
size_t v___x_3159_; size_t v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = ((size_t)0ULL);
v___x_3160_ = lean_usize_of_nat(v___x_3153_);
v___x_3161_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3148_, v_es_3151_, v___x_3159_, v___x_3160_, v_x_3150_);
return v___x_3161_;
}
}
}
else
{
lean_object* v_ks_3162_; lean_object* v_vs_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; 
v_ks_3162_ = lean_ctor_get(v_x_3149_, 0);
v_vs_3163_ = lean_ctor_get(v_x_3149_, 1);
v___x_3164_ = lean_unsigned_to_nat(0u);
v___x_3165_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3148_, v_ks_3162_, v_vs_3163_, v___x_3164_, v_x_3150_);
return v___x_3165_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_3166_, lean_object* v_as_3167_, size_t v_i_3168_, size_t v_stop_3169_, lean_object* v_b_3170_){
_start:
{
lean_object* v___y_3172_; uint8_t v___x_3176_; 
v___x_3176_ = lean_usize_dec_eq(v_i_3168_, v_stop_3169_);
if (v___x_3176_ == 0)
{
lean_object* v___x_3177_; 
v___x_3177_ = lean_array_uget_borrowed(v_as_3167_, v_i_3168_);
switch(lean_obj_tag(v___x_3177_))
{
case 0:
{
lean_object* v_key_3178_; lean_object* v_val_3179_; lean_object* v___x_3180_; 
v_key_3178_ = lean_ctor_get(v___x_3177_, 0);
v_val_3179_ = lean_ctor_get(v___x_3177_, 1);
lean_inc(v_f_3166_);
lean_inc(v_val_3179_);
lean_inc(v_key_3178_);
v___x_3180_ = lean_apply_3(v_f_3166_, v_b_3170_, v_key_3178_, v_val_3179_);
v___y_3172_ = v___x_3180_;
goto v___jp_3171_;
}
case 1:
{
lean_object* v_node_3181_; lean_object* v___x_3182_; 
v_node_3181_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_f_3166_);
v___x_3182_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3166_, v_node_3181_, v_b_3170_);
v___y_3172_ = v___x_3182_;
goto v___jp_3171_;
}
default: 
{
v___y_3172_ = v_b_3170_;
goto v___jp_3171_;
}
}
}
else
{
lean_dec(v_f_3166_);
return v_b_3170_;
}
v___jp_3171_:
{
size_t v___x_3173_; size_t v___x_3174_; 
v___x_3173_ = ((size_t)1ULL);
v___x_3174_ = lean_usize_add(v_i_3168_, v___x_3173_);
v_i_3168_ = v___x_3174_;
v_b_3170_ = v___y_3172_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_3183_, lean_object* v_as_3184_, lean_object* v_i_3185_, lean_object* v_stop_3186_, lean_object* v_b_3187_){
_start:
{
size_t v_i_boxed_3188_; size_t v_stop_boxed_3189_; lean_object* v_res_3190_; 
v_i_boxed_3188_ = lean_unbox_usize(v_i_3185_);
lean_dec(v_i_3185_);
v_stop_boxed_3189_ = lean_unbox_usize(v_stop_3186_);
lean_dec(v_stop_3186_);
v_res_3190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3183_, v_as_3184_, v_i_boxed_3188_, v_stop_boxed_3189_, v_b_3187_);
lean_dec_ref(v_as_3184_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_3191_, lean_object* v_x_3192_, lean_object* v_x_3193_){
_start:
{
lean_object* v_res_3194_; 
v_res_3194_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3191_, v_x_3192_, v_x_3193_);
lean_dec_ref(v_x_3192_);
return v_res_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(lean_object* v_map_3195_, lean_object* v_f_3196_, lean_object* v_init_3197_){
_start:
{
lean_object* v___f_3198_; lean_object* v___x_3199_; 
v___f_3198_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_3198_, 0, v_f_3196_);
v___x_3199_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v___f_3198_, v_map_3195_, v_init_3197_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg___boxed(lean_object* v_map_3200_, lean_object* v_f_3201_, lean_object* v_init_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_3200_, v_f_3201_, v_init_3202_);
lean_dec_ref(v_map_3200_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(lean_object* v_a_3205_){
_start:
{
lean_object* v___x_3207_; lean_object* v_env_3208_; lean_object* v___x_3209_; lean_object* v_map_u2082_3210_; lean_object* v___f_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3207_ = lean_st_ref_get(v_a_3205_);
v_env_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc_ref(v_env_3208_);
lean_dec(v___x_3207_);
v___x_3209_ = l_Lean_Environment_constants(v_env_3208_);
v_map_u2082_3210_ = lean_ctor_get(v___x_3209_, 1);
lean_inc_ref(v_map_u2082_3210_);
lean_dec_ref(v___x_3209_);
v___f_3211_ = ((lean_object*)(l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___closed__0));
v___x_3212_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___at___00Lean_Linter_EnvLinter_lintCore_spec__3___redArg___closed__1));
v___x_3213_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_u2082_3210_, v___f_3211_, v___x_3212_);
lean_dec_ref(v_map_u2082_3210_);
v___x_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3213_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg___boxed(lean_object* v_a_3215_, lean_object* v_a_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3215_);
lean_dec(v_a_3215_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule(lean_object* v_a_3218_, lean_object* v_a_3219_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3219_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInCurrModule___boxed(lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_){
_start:
{
lean_object* v_res_3225_; 
v_res_3225_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule(v_a_3222_, v_a_3223_);
lean_dec(v_a_3223_);
lean_dec_ref(v_a_3222_);
return v_res_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(lean_object* v_00_u03c3_3226_, lean_object* v_00_u03b2_3227_, lean_object* v_map_3228_, lean_object* v_f_3229_, lean_object* v_init_3230_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___redArg(v_map_3228_, v_f_3229_, v_init_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0___boxed(lean_object* v_00_u03c3_3232_, lean_object* v_00_u03b2_3233_, lean_object* v_map_3234_, lean_object* v_f_3235_, lean_object* v_init_3236_){
_start:
{
lean_object* v_res_3237_; 
v_res_3237_ = l_Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0(v_00_u03c3_3232_, v_00_u03b2_3233_, v_map_3234_, v_f_3235_, v_init_3236_);
lean_dec_ref(v_map_3234_);
return v_res_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(lean_object* v_map_3238_, lean_object* v_f_3239_, lean_object* v_init_3240_){
_start:
{
lean_object* v___x_3241_; 
v___x_3241_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3239_, v_map_3238_, v_init_3240_);
return v___x_3241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg___boxed(lean_object* v_map_3242_, lean_object* v_f_3243_, lean_object* v_init_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___redArg(v_map_3242_, v_f_3243_, v_init_3244_);
lean_dec_ref(v_map_3242_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(lean_object* v_00_u03c3_3246_, lean_object* v_00_u03b2_3247_, lean_object* v_map_3248_, lean_object* v_f_3249_, lean_object* v_init_3250_){
_start:
{
lean_object* v___x_3251_; 
v___x_3251_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3249_, v_map_3248_, v_init_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0___boxed(lean_object* v_00_u03c3_3252_, lean_object* v_00_u03b2_3253_, lean_object* v_map_3254_, lean_object* v_f_3255_, lean_object* v_init_3256_){
_start:
{
lean_object* v_res_3257_; 
v_res_3257_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0(v_00_u03c3_3252_, v_00_u03b2_3253_, v_map_3254_, v_f_3255_, v_init_3256_);
lean_dec_ref(v_map_3254_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_3258_, lean_object* v_00_u03b1_3259_, lean_object* v_00_u03b2_3260_, lean_object* v_f_3261_, lean_object* v_x_3262_, lean_object* v_x_3263_){
_start:
{
lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___redArg(v_f_3261_, v_x_3262_, v_x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_3265_, lean_object* v_00_u03b1_3266_, lean_object* v_00_u03b2_3267_, lean_object* v_f_3268_, lean_object* v_x_3269_, lean_object* v_x_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1(v_00_u03c3_3265_, v_00_u03b1_3266_, v_00_u03b2_3267_, v_f_3268_, v_x_3269_, v_x_3270_);
lean_dec_ref(v_x_3269_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_3272_, lean_object* v_00_u03b2_3273_, lean_object* v_00_u03c3_3274_, lean_object* v_f_3275_, lean_object* v_as_3276_, size_t v_i_3277_, size_t v_stop_3278_, lean_object* v_b_3279_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___redArg(v_f_3275_, v_as_3276_, v_i_3277_, v_stop_3278_, v_b_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_3281_, lean_object* v_00_u03b2_3282_, lean_object* v_00_u03c3_3283_, lean_object* v_f_3284_, lean_object* v_as_3285_, lean_object* v_i_3286_, lean_object* v_stop_3287_, lean_object* v_b_3288_){
_start:
{
size_t v_i_boxed_3289_; size_t v_stop_boxed_3290_; lean_object* v_res_3291_; 
v_i_boxed_3289_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_stop_boxed_3290_ = lean_unbox_usize(v_stop_3287_);
lean_dec(v_stop_3287_);
v_res_3291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_3281_, v_00_u03b2_3282_, v_00_u03c3_3283_, v_f_3284_, v_as_3285_, v_i_boxed_3289_, v_stop_boxed_3290_, v_b_3288_);
lean_dec_ref(v_as_3285_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_3292_, lean_object* v_00_u03b1_3293_, lean_object* v_00_u03b2_3294_, lean_object* v_f_3295_, lean_object* v_keys_3296_, lean_object* v_vals_3297_, lean_object* v_heq_3298_, lean_object* v_i_3299_, lean_object* v_acc_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___redArg(v_f_3295_, v_keys_3296_, v_vals_3297_, v_i_3299_, v_acc_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_3302_, lean_object* v_00_u03b1_3303_, lean_object* v_00_u03b2_3304_, lean_object* v_f_3305_, lean_object* v_keys_3306_, lean_object* v_vals_3307_, lean_object* v_heq_3308_, lean_object* v_i_3309_, lean_object* v_acc_3310_){
_start:
{
lean_object* v_res_3311_; 
v_res_3311_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_Linter_EnvLinter_getDeclsInCurrModule_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_3302_, v_00_u03b1_3303_, v_00_u03b2_3304_, v_f_3305_, v_keys_3306_, v_vals_3307_, v_heq_3308_, v_i_3309_, v_acc_3310_);
lean_dec_ref(v_vals_3307_);
lean_dec_ref(v_keys_3306_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(lean_object* v_x_3312_, lean_object* v_x_3313_){
_start:
{
if (lean_obj_tag(v_x_3313_) == 0)
{
return v_x_3312_;
}
else
{
lean_object* v_key_3314_; lean_object* v_tail_3315_; lean_object* v___x_3316_; 
v_key_3314_ = lean_ctor_get(v_x_3313_, 0);
lean_inc(v_key_3314_);
v_tail_3315_ = lean_ctor_get(v_x_3313_, 2);
lean_inc(v_tail_3315_);
lean_dec_ref_known(v_x_3313_, 3);
v___x_3316_ = lean_array_push(v_x_3312_, v_key_3314_);
v_x_3312_ = v___x_3316_;
v_x_3313_ = v_tail_3315_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(lean_object* v_as_3318_, size_t v_i_3319_, size_t v_stop_3320_, lean_object* v_b_3321_){
_start:
{
uint8_t v___x_3322_; 
v___x_3322_ = lean_usize_dec_eq(v_i_3319_, v_stop_3320_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; size_t v___x_3325_; size_t v___x_3326_; 
v___x_3323_ = lean_array_uget_borrowed(v_as_3318_, v_i_3319_);
lean_inc(v___x_3323_);
v___x_3324_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getAllDecls_spec__0(v_b_3321_, v___x_3323_);
v___x_3325_ = ((size_t)1ULL);
v___x_3326_ = lean_usize_add(v_i_3319_, v___x_3325_);
v_i_3319_ = v___x_3326_;
v_b_3321_ = v___x_3324_;
goto _start;
}
else
{
return v_b_3321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1___boxed(lean_object* v_as_3328_, lean_object* v_i_3329_, lean_object* v_stop_3330_, lean_object* v_b_3331_){
_start:
{
size_t v_i_boxed_3332_; size_t v_stop_boxed_3333_; lean_object* v_res_3334_; 
v_i_boxed_3332_ = lean_unbox_usize(v_i_3329_);
lean_dec(v_i_3329_);
v_stop_boxed_3333_ = lean_unbox_usize(v_stop_3330_);
lean_dec(v_stop_3330_);
v_res_3334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_as_3328_, v_i_boxed_3332_, v_stop_boxed_3333_, v_b_3331_);
lean_dec_ref(v_as_3328_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg(lean_object* v_a_3335_){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v_a_3339_; lean_object* v_env_3340_; lean_object* v___x_3341_; lean_object* v_map_u2081_3342_; lean_object* v_buckets_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
v___x_3337_ = lean_st_ref_get(v_a_3335_);
v___x_3338_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3335_);
v_a_3339_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_a_3339_);
v_env_3340_ = lean_ctor_get(v___x_3337_, 0);
lean_inc_ref(v_env_3340_);
lean_dec(v___x_3337_);
v___x_3341_ = l_Lean_Environment_constants(v_env_3340_);
v_map_u2081_3342_ = lean_ctor_get(v___x_3341_, 0);
lean_inc_ref(v_map_u2081_3342_);
lean_dec_ref(v___x_3341_);
v_buckets_3343_ = lean_ctor_get(v_map_u2081_3342_, 1);
lean_inc_ref(v_buckets_3343_);
lean_dec_ref(v_map_u2081_3342_);
v___x_3344_ = lean_unsigned_to_nat(0u);
v___x_3345_ = lean_array_get_size(v_buckets_3343_);
v___x_3346_ = lean_nat_dec_lt(v___x_3344_, v___x_3345_);
if (v___x_3346_ == 0)
{
lean_dec_ref(v_buckets_3343_);
lean_dec(v_a_3339_);
return v___x_3338_;
}
else
{
uint8_t v___x_3347_; 
v___x_3347_ = lean_nat_dec_le(v___x_3345_, v___x_3345_);
if (v___x_3347_ == 0)
{
if (v___x_3346_ == 0)
{
lean_dec_ref(v_buckets_3343_);
lean_dec(v_a_3339_);
return v___x_3338_;
}
else
{
lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3357_; 
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v___x_3338_, 0);
lean_dec(v_unused_3358_);
v___x_3349_ = v___x_3338_;
v_isShared_3350_ = v_isSharedCheck_3357_;
goto v_resetjp_3348_;
}
else
{
lean_dec(v___x_3338_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3357_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
size_t v___x_3351_; size_t v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3351_ = ((size_t)0ULL);
v___x_3352_ = lean_usize_of_nat(v___x_3345_);
v___x_3353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_3343_, v___x_3351_, v___x_3352_, v_a_3339_);
lean_dec_ref(v_buckets_3343_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3353_);
v___x_3355_ = v___x_3349_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3368_; 
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3338_);
if (v_isSharedCheck_3368_ == 0)
{
lean_object* v_unused_3369_; 
v_unused_3369_ = lean_ctor_get(v___x_3338_, 0);
lean_dec(v_unused_3369_);
v___x_3360_ = v___x_3338_;
v_isShared_3361_ = v_isSharedCheck_3368_;
goto v_resetjp_3359_;
}
else
{
lean_dec(v___x_3338_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3368_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
size_t v___x_3362_; size_t v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3362_ = ((size_t)0ULL);
v___x_3363_ = lean_usize_of_nat(v___x_3345_);
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getAllDecls_spec__1(v_buckets_3343_, v___x_3362_, v___x_3363_, v_a_3339_);
lean_dec_ref(v_buckets_3343_);
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 0, v___x_3364_);
v___x_3366_ = v___x_3360_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3367_; 
v_reuseFailAlloc_3367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3367_, 0, v___x_3364_);
v___x_3366_ = v_reuseFailAlloc_3367_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
return v___x_3366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___redArg___boxed(lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_3370_);
lean_dec(v_a_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls(lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Lean_Linter_EnvLinter_getAllDecls___redArg(v_a_3374_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getAllDecls___boxed(lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_Lean_Linter_EnvLinter_getAllDecls(v_a_3377_, v_a_3378_);
lean_dec(v_a_3378_);
lean_dec_ref(v_a_3377_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(lean_object* v_msg_3381_){
_start:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = lean_panic_fn_borrowed(v___x_3382_, v_msg_3381_);
return v___x_3383_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; 
v___x_3387_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__2));
v___x_3388_ = lean_unsigned_to_nat(14u);
v___x_3389_ = lean_unsigned_to_nat(22u);
v___x_3390_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__1));
v___x_3391_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__0));
v___x_3392_ = l_mkPanicMessageWithDecl(v___x_3391_, v___x_3390_, v___x_3389_, v___x_3388_, v___x_3387_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(lean_object* v___x_3393_, lean_object* v___x_3394_, lean_object* v_x_3395_, lean_object* v_x_3396_){
_start:
{
if (lean_obj_tag(v_x_3396_) == 0)
{
lean_dec_ref(v___x_3394_);
return v_x_3395_;
}
else
{
lean_object* v_key_3397_; lean_object* v_tail_3398_; uint8_t v___x_3399_; lean_object* v___y_3401_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_key_3397_ = lean_ctor_get(v_x_3396_, 0);
lean_inc(v_key_3397_);
v_tail_3398_ = lean_ctor_get(v_x_3396_, 2);
lean_inc(v_tail_3398_);
lean_dec_ref_known(v_x_3396_, 3);
v___x_3399_ = 0;
lean_inc_ref(v___x_3394_);
v___x_3408_ = l_Lean_Environment_const2ModIdx(v___x_3394_);
v___x_3409_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Linter_EnvLinter_groupedByFilename_spec__5___redArg(v___x_3408_, v_key_3397_);
lean_dec_ref(v___x_3408_);
if (lean_obj_tag(v___x_3409_) == 0)
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___closed__3);
v___x_3411_ = l_panic___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__1(v___x_3410_);
v___y_3401_ = v___x_3411_;
goto v___jp_3400_;
}
else
{
lean_object* v_val_3412_; 
v_val_3412_ = lean_ctor_get(v___x_3409_, 0);
lean_inc(v_val_3412_);
lean_dec_ref_known(v___x_3409_, 1);
v___y_3401_ = v_val_3412_;
goto v___jp_3400_;
}
v___jp_3400_:
{
lean_object* v___x_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3402_ = lean_box(v___x_3399_);
v___x_3403_ = lean_array_get(v___x_3402_, v___x_3393_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec(v___x_3402_);
v___x_3404_ = lean_unbox(v___x_3403_);
lean_dec(v___x_3403_);
if (v___x_3404_ == 0)
{
lean_dec(v_key_3397_);
v_x_3396_ = v_tail_3398_;
goto _start;
}
else
{
lean_object* v___x_3406_; 
v___x_3406_ = lean_array_push(v_x_3395_, v_key_3397_);
v_x_3395_ = v___x_3406_;
v_x_3396_ = v_tail_3398_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2___boxed(lean_object* v___x_3413_, lean_object* v___x_3414_, lean_object* v_x_3415_, lean_object* v_x_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_3413_, v___x_3414_, v_x_3415_, v_x_3416_);
lean_dec_ref(v___x_3413_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(lean_object* v___x_3418_, lean_object* v___x_3419_, lean_object* v_as_3420_, size_t v_i_3421_, size_t v_stop_3422_, lean_object* v_b_3423_){
_start:
{
uint8_t v___x_3424_; 
v___x_3424_ = lean_usize_dec_eq(v_i_3421_, v_stop_3422_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; lean_object* v___x_3426_; size_t v___x_3427_; size_t v___x_3428_; 
v___x_3425_ = lean_array_uget_borrowed(v_as_3420_, v_i_3421_);
lean_inc(v___x_3425_);
lean_inc_ref(v___x_3419_);
v___x_3426_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__2(v___x_3418_, v___x_3419_, v_b_3423_, v___x_3425_);
v___x_3427_ = ((size_t)1ULL);
v___x_3428_ = lean_usize_add(v_i_3421_, v___x_3427_);
v_i_3421_ = v___x_3428_;
v_b_3423_ = v___x_3426_;
goto _start;
}
else
{
lean_dec_ref(v___x_3419_);
return v_b_3423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3___boxed(lean_object* v___x_3430_, lean_object* v___x_3431_, lean_object* v_as_3432_, lean_object* v_i_3433_, lean_object* v_stop_3434_, lean_object* v_b_3435_){
_start:
{
size_t v_i_boxed_3436_; size_t v_stop_boxed_3437_; lean_object* v_res_3438_; 
v_i_boxed_3436_ = lean_unbox_usize(v_i_3433_);
lean_dec(v_i_3433_);
v_stop_boxed_3437_ = lean_unbox_usize(v_stop_3434_);
lean_dec(v_stop_3434_);
v_res_3438_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3430_, v___x_3431_, v_as_3432_, v_i_boxed_3436_, v_stop_boxed_3437_, v_b_3435_);
lean_dec_ref(v_as_3432_);
lean_dec_ref(v___x_3430_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(lean_object* v_pkg_3439_, size_t v_sz_3440_, size_t v_i_3441_, lean_object* v_bs_3442_){
_start:
{
uint8_t v___x_3443_; 
v___x_3443_ = lean_usize_dec_lt(v_i_3441_, v_sz_3440_);
if (v___x_3443_ == 0)
{
return v_bs_3442_;
}
else
{
lean_object* v_v_3444_; lean_object* v___x_3445_; lean_object* v_bs_x27_3446_; uint8_t v___x_3447_; size_t v___x_3448_; size_t v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v_v_3444_ = lean_array_uget(v_bs_3442_, v_i_3441_);
v___x_3445_ = lean_unsigned_to_nat(0u);
v_bs_x27_3446_ = lean_array_uset(v_bs_3442_, v_i_3441_, v___x_3445_);
v___x_3447_ = l_Lean_Name_isPrefixOf(v_pkg_3439_, v_v_3444_);
lean_dec(v_v_3444_);
v___x_3448_ = ((size_t)1ULL);
v___x_3449_ = lean_usize_add(v_i_3441_, v___x_3448_);
v___x_3450_ = lean_box(v___x_3447_);
v___x_3451_ = lean_array_uset(v_bs_x27_3446_, v_i_3441_, v___x_3450_);
v_i_3441_ = v___x_3449_;
v_bs_3442_ = v___x_3451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0___boxed(lean_object* v_pkg_3453_, lean_object* v_sz_3454_, lean_object* v_i_3455_, lean_object* v_bs_3456_){
_start:
{
size_t v_sz_boxed_3457_; size_t v_i_boxed_3458_; lean_object* v_res_3459_; 
v_sz_boxed_3457_ = lean_unbox_usize(v_sz_3454_);
lean_dec(v_sz_3454_);
v_i_boxed_3458_ = lean_unbox_usize(v_i_3455_);
lean_dec(v_i_3455_);
v_res_3459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_3453_, v_sz_boxed_3457_, v_i_boxed_3458_, v_bs_3456_);
lean_dec(v_pkg_3453_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(lean_object* v_pkg_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v_a_3465_; lean_object* v_env_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v_map_u2081_3469_; lean_object* v_buckets_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3463_ = lean_st_ref_get(v_a_3461_);
v___x_3464_ = l_Lean_Linter_EnvLinter_getDeclsInCurrModule___redArg(v_a_3461_);
v_a_3465_ = lean_ctor_get(v___x_3464_, 0);
lean_inc(v_a_3465_);
v_env_3466_ = lean_ctor_get(v___x_3463_, 0);
lean_inc_ref_n(v_env_3466_, 2);
lean_dec(v___x_3463_);
v___x_3467_ = l_Lean_Environment_header(v_env_3466_);
v___x_3468_ = l_Lean_Environment_constants(v_env_3466_);
v_map_u2081_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc_ref(v_map_u2081_3469_);
lean_dec_ref(v___x_3468_);
v_buckets_3470_ = lean_ctor_get(v_map_u2081_3469_, 1);
lean_inc_ref(v_buckets_3470_);
lean_dec_ref(v_map_u2081_3469_);
v___x_3471_ = lean_unsigned_to_nat(0u);
v___x_3472_ = lean_array_get_size(v_buckets_3470_);
v___x_3473_ = lean_nat_dec_lt(v___x_3471_, v___x_3472_);
if (v___x_3473_ == 0)
{
lean_dec_ref(v_buckets_3470_);
lean_dec_ref(v___x_3467_);
lean_dec_ref(v_env_3466_);
lean_dec(v_a_3465_);
return v___x_3464_;
}
else
{
lean_object* v___x_3474_; size_t v_sz_3475_; size_t v___x_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; 
v___x_3474_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3467_);
v_sz_3475_ = lean_array_size(v___x_3474_);
v___x_3476_ = ((size_t)0ULL);
v___x_3477_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__0(v_pkg_3460_, v_sz_3475_, v___x_3476_, v___x_3474_);
v___x_3478_ = lean_nat_dec_le(v___x_3472_, v___x_3472_);
if (v___x_3478_ == 0)
{
if (v___x_3473_ == 0)
{
lean_dec_ref(v___x_3477_);
lean_dec_ref(v_buckets_3470_);
lean_dec_ref(v_env_3466_);
lean_dec(v_a_3465_);
return v___x_3464_;
}
else
{
lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3487_; 
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3487_ == 0)
{
lean_object* v_unused_3488_; 
v_unused_3488_ = lean_ctor_get(v___x_3464_, 0);
lean_dec(v_unused_3488_);
v___x_3480_ = v___x_3464_;
v_isShared_3481_ = v_isSharedCheck_3487_;
goto v_resetjp_3479_;
}
else
{
lean_dec(v___x_3464_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3487_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
size_t v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3485_; 
v___x_3482_ = lean_usize_of_nat(v___x_3472_);
v___x_3483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3477_, v_env_3466_, v_buckets_3470_, v___x_3476_, v___x_3482_, v_a_3465_);
lean_dec_ref(v_buckets_3470_);
lean_dec_ref(v___x_3477_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3483_);
v___x_3485_ = v___x_3480_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v___x_3483_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3497_; 
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3497_ == 0)
{
lean_object* v_unused_3498_; 
v_unused_3498_ = lean_ctor_get(v___x_3464_, 0);
lean_dec(v_unused_3498_);
v___x_3490_ = v___x_3464_;
v_isShared_3491_ = v_isSharedCheck_3497_;
goto v_resetjp_3489_;
}
else
{
lean_dec(v___x_3464_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3497_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
size_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3495_; 
v___x_3492_ = lean_usize_of_nat(v___x_3472_);
v___x_3493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Linter_EnvLinter_getDeclsInPackage_spec__3(v___x_3477_, v_env_3466_, v_buckets_3470_, v___x_3476_, v___x_3492_, v_a_3465_);
lean_dec_ref(v_buckets_3470_);
lean_dec_ref(v___x_3477_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 0, v___x_3493_);
v___x_3495_ = v___x_3490_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg___boxed(lean_object* v_pkg_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_){
_start:
{
lean_object* v_res_3502_; 
v_res_3502_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_3499_, v_a_3500_);
lean_dec(v_a_3500_);
lean_dec(v_pkg_3499_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage(lean_object* v_pkg_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_){
_start:
{
lean_object* v___x_3507_; 
v___x_3507_ = l_Lean_Linter_EnvLinter_getDeclsInPackage___redArg(v_pkg_3503_, v_a_3505_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_getDeclsInPackage___boxed(lean_object* v_pkg_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_Linter_EnvLinter_getDeclsInPackage(v_pkg_3508_, v_a_3509_, v_a_3510_);
lean_dec(v_a_3510_);
lean_dec_ref(v_a_3509_);
lean_dec(v_pkg_3508_);
return v_res_3512_;
}
}
lean_object* runtime_initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Path(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_EnvLinter_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Linter_EnvLinter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default = _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity_default();
l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity = _init_l_Lean_Linter_EnvLinter_instInhabitedLintVerbosity();
l_Lean_Linter_EnvLinter_instInhabitedLintScope_default = _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope_default();
l_Lean_Linter_EnvLinter_instInhabitedLintScope = _init_l_Lean_Linter_EnvLinter_instInhabitedLintScope();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_EnvLinter_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_EnvLinter_Basic(uint8_t builtin);
lean_object* initialize_Lean_DeclarationRange(uint8_t builtin);
lean_object* initialize_Lean_Util_Path(uint8_t builtin);
lean_object* initialize_Lean_CoreM(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_EnvLinter_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_EnvLinter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DeclarationRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Path(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_EnvLinter_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_EnvLinter_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_EnvLinter_Frontend(builtin);
}
#ifdef __cplusplus
}
#endif
