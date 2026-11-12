// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Lint
// Imports: public import Lean.Elab.Command import Init.Grind.Lint import Lean.Elab.Tactic.Grind.Config import Lean.Meta.Tactic.TryThis
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_grindExt;
lean_object* l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_PrettyPrinter_ppCategory(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabConfigItems___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Linter_checkDeprecatedAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_NameSet_insert, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__3_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__5_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__7_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__9_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(243, 88, 6, 248, 93, 59, 25, 68)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lint"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__11_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__12_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(183, 114, 43, 248, 93, 254, 15, 10)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__13_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(202, 60, 208, 68, 200, 143, 88, 44)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__14_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(203, 228, 54, 219, 35, 84, 66, 241)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__15_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(157, 8, 11, 132, 215, 230, 226, 190)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__16_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(132, 1, 217, 23, 127, 111, 118, 114)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__17_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 50, 192, 159, 220, 212, 146, 219)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "skipExt"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__19_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(251, 38, 210, 115, 172, 166, 0, 188)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "skipSuffixExt"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(69, 232, 160, 86, 131, 141, 224, 111)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "muteExt"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(31, 201, 217, 5, 230, 14, 173, 234)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "` is not marked with the `@[grind]` attribute for theorem instantiation"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__4;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` is already in the `#grind_lint` skip suffix set"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` is already in the `#grind_lint` skip set"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLintSkip"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 168, 241, 99, 13, 160, 45, 13)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "elabGrindLintSkip"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(34, 150, 93, 202, 39, 76, 72, 121)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` is already in the `#grind_lint` mute set"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "grindLintMute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 30, 63, 16, 186, 128, 138, 7)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "elabGrindLintMute"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 217, 3, 71, 4, 76, 33, 206)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*18 + 40, .m_other = 18, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0 = (const lean_object*)&l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0_value;
static const lean_array_object l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___boxed(lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "thm"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 106, 229, 125, 19, 158, 75, 156)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " ↦ "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___boxed, .m_arity = 8, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "instantiating `"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` triggers "};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = " additional `grind` theorem instantiations"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` triggers more than "};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ematch"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(188, 203, 62, 74, 58, 114, 10, 110)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(234, 73, 177, 83, 191, 84, 13, 55)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(113, 53, 23, 82, 113, 68, 182, 130)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "in"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "set_option"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "trace.grind.ematch.instance"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__11_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Try this to display the actual theorem instances:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "grindLintInspect"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 56, 130, 46, 162, 240, 182, 8)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "elabGrindLintInspect"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 183, 118, 110, 60, 132, 15, 220)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 175, 53, 50, 212, 152, 178, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " failed with "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "#grind_lint inspect "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Try this:"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grindLintCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__10_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 113, 74, 13, 3, 158, 65, 234)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "elabGrindLintCheck"};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__18_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 242, 245, 17, 70, 107, 60, 218)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___lam__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_(lean_object* v_es_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_array_mk(v_es_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_3_, size_t v_i_4_, size_t v_stop_5_, lean_object* v_b_6_){
_start:
{
uint8_t v___x_7_; 
v___x_7_ = lean_usize_dec_eq(v_i_4_, v_stop_5_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; size_t v___x_10_; size_t v___x_11_; 
v___x_8_ = lean_array_uget_borrowed(v_as_3_, v_i_4_);
lean_inc(v___x_8_);
v___x_9_ = l_Lean_NameSet_insert(v_b_6_, v___x_8_);
v___x_10_ = ((size_t)1ULL);
v___x_11_ = lean_usize_add(v_i_4_, v___x_10_);
v_i_4_ = v___x_11_;
v_b_6_ = v___x_9_;
goto _start;
}
else
{
return v_b_6_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_13_, lean_object* v_i_14_, lean_object* v_stop_15_, lean_object* v_b_16_){
_start:
{
size_t v_i_boxed_17_; size_t v_stop_boxed_18_; lean_object* v_res_19_; 
v_i_boxed_17_ = lean_unbox_usize(v_i_14_);
lean_dec(v_i_14_);
v_stop_boxed_18_ = lean_unbox_usize(v_stop_15_);
lean_dec(v_stop_15_);
v_res_19_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0(v_as_13_, v_i_boxed_17_, v_stop_boxed_18_, v_b_16_);
lean_dec_ref(v_as_13_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_20_, size_t v_i_21_, size_t v_stop_22_, lean_object* v_b_23_){
_start:
{
lean_object* v___y_25_; uint8_t v___x_29_; 
v___x_29_ = lean_usize_dec_eq(v_i_21_, v_stop_22_);
if (v___x_29_ == 0)
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
v___x_30_ = lean_array_uget_borrowed(v_as_20_, v_i_21_);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_array_get_size(v___x_30_);
v___x_33_ = lean_nat_dec_lt(v___x_31_, v___x_32_);
if (v___x_33_ == 0)
{
v___y_25_ = v_b_23_;
goto v___jp_24_;
}
else
{
size_t v___x_34_; size_t v___x_35_; lean_object* v___x_36_; 
v___x_34_ = ((size_t)0ULL);
v___x_35_ = lean_usize_of_nat(v___x_32_);
v___x_36_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0(v___x_30_, v___x_34_, v___x_35_, v_b_23_);
v___y_25_ = v___x_36_;
goto v___jp_24_;
}
}
else
{
return v_b_23_;
}
v___jp_24_:
{
size_t v___x_26_; size_t v___x_27_; 
v___x_26_ = ((size_t)1ULL);
v___x_27_ = lean_usize_add(v_i_21_, v___x_26_);
v_i_21_ = v___x_27_;
v_b_23_ = v___y_25_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_37_, lean_object* v_i_38_, lean_object* v_stop_39_, lean_object* v_b_40_){
_start:
{
size_t v_i_boxed_41_; size_t v_stop_boxed_42_; lean_object* v_res_43_; 
v_i_boxed_41_ = lean_unbox_usize(v_i_38_);
lean_dec(v_i_38_);
v_stop_boxed_42_ = lean_unbox_usize(v_stop_39_);
lean_dec(v_stop_39_);
v_res_43_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(v_as_37_, v_i_boxed_41_, v_stop_boxed_42_, v_b_40_);
lean_dec_ref(v_as_37_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0(lean_object* v_initState_44_, lean_object* v_as_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = lean_array_get_size(v_as_45_);
v___x_48_ = lean_nat_dec_lt(v___x_46_, v___x_47_);
if (v___x_48_ == 0)
{
return v_initState_44_;
}
else
{
size_t v___x_49_; size_t v___x_50_; lean_object* v___x_51_; 
v___x_49_ = ((size_t)0ULL);
v___x_50_ = lean_usize_of_nat(v___x_47_);
v___x_51_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(v_as_45_, v___x_49_, v___x_50_, v_initState_44_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_52_, lean_object* v_as_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0(v_initState_52_, v_as_53_);
lean_dec_ref(v_as_53_);
return v_res_54_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = l_Lean_NameSet_empty;
v___x_101_ = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0___boxed), 2, 1);
lean_closure_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_102_ = 0;
v___x_103_ = lean_box(2);
v___x_104_ = lean_box(0);
v___f_105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_106_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
v___f_107_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_109_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___f_107_);
lean_ctor_set(v___x_109_, 2, v___x_106_);
lean_ctor_set(v___x_109_, 3, v___f_105_);
lean_ctor_set(v___x_109_, 4, v___x_104_);
lean_ctor_set(v___x_109_, 5, v___x_103_);
lean_ctor_set(v___x_109_, 6, v___x_104_);
lean_ctor_set_uint8(v___x_109_, sizeof(void*)*7, v___x_102_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
v___x_112_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2____boxed(lean_object* v_a_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_();
return v_res_114_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___f_122_; lean_object* v___x_123_; lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_119_ = 0;
v___x_120_ = lean_box(2);
v___x_121_ = lean_box(0);
v___f_122_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_123_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
v___f_124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_125_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_));
v___x_126_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v___f_124_);
lean_ctor_set(v___x_126_, 2, v___x_123_);
lean_ctor_set(v___x_126_, 3, v___f_122_);
lean_ctor_set(v___x_126_, 4, v___x_121_);
lean_ctor_set(v___x_126_, 5, v___x_120_);
lean_ctor_set(v___x_126_, 6, v___x_121_);
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*7, v___x_119_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_);
v___x_129_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2____boxed(lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_();
return v_res_131_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___f_139_; lean_object* v___x_140_; lean_object* v___f_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_136_ = 0;
v___x_137_ = lean_box(2);
v___x_138_ = lean_box(0);
v___f_139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_140_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
v___f_141_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_142_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_));
v___x_143_ = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___f_141_);
lean_ctor_set(v___x_143_, 2, v___x_140_);
lean_ctor_set(v___x_143_, 3, v___f_139_);
lean_ctor_set(v___x_143_, 4, v___x_138_);
lean_ctor_set(v___x_143_, 5, v___x_137_);
lean_ctor_set(v___x_143_, 6, v___x_138_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*7, v___x_136_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_);
v___x_146_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2____boxed(lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_();
return v_res_148_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_149_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0);
v___x_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
lean_ctor_set(v___x_154_, 2, v___x_153_);
lean_ctor_set(v___x_154_, 3, v___x_153_);
lean_ctor_set(v___x_154_, 4, v___x_152_);
lean_ctor_set(v___x_154_, 5, v___x_152_);
lean_ctor_set(v___x_154_, 6, v___x_152_);
lean_ctor_set(v___x_154_, 7, v___x_152_);
lean_ctor_set(v___x_154_, 8, v___x_152_);
lean_ctor_set(v___x_154_, 9, v___x_152_);
lean_ctor_set(v___x_154_, 10, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_unsigned_to_nat(32u);
v___x_156_ = lean_mk_empty_array_with_capacity(v___x_155_);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_158_ = ((size_t)5ULL);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_unsigned_to_nat(32u);
v___x_161_ = lean_mk_empty_array_with_capacity(v___x_160_);
v___x_162_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3);
v___x_163_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_159_);
lean_ctor_set(v___x_163_, 3, v___x_159_);
lean_ctor_set_usize(v___x_163_, 4, v___x_158_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_164_ = lean_box(1);
v___x_165_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4);
v___x_166_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1);
v___x_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
lean_ctor_set(v___x_167_, 2, v___x_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(lean_object* v_msgData_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; lean_object* v_toCold_173_; lean_object* v_env_174_; lean_object* v_options_175_; uint8_t v___x_176_; lean_object* v_env_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_172_ = lean_st_ref_get(v___y_170_);
v_toCold_173_ = lean_ctor_get(v___y_169_, 0);
v_env_174_ = lean_ctor_get(v___x_172_, 0);
lean_inc_ref(v_env_174_);
lean_dec(v___x_172_);
v_options_175_ = lean_ctor_get(v_toCold_173_, 2);
v___x_176_ = 0;
v_env_177_ = l_Lean_Environment_setRecordingDeps(v_env_174_, v___x_176_);
v___x_178_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_175_);
v___x_180_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_180_, 0, v_env_177_);
lean_ctor_set(v___x_180_, 1, v___x_178_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
lean_ctor_set(v___x_180_, 3, v_options_175_);
v___x_181_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v_msgData_168_);
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_msgData_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(v_msgData_183_, v___y_184_, v___y_185_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(lean_object* v_msg_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_ref_192_; lean_object* v___x_193_; lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_202_; 
v_ref_192_ = lean_ctor_get(v___y_189_, 2);
v___x_193_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(v_msg_188_, v___y_189_, v___y_190_);
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_202_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_202_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_202_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
lean_inc(v_ref_192_);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v_ref_192_);
lean_ctor_set(v___x_198_, 1, v_a_194_);
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 1);
lean_ctor_set(v___x_196_, 0, v___x_198_);
v___x_200_ = v___x_196_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg___boxed(lean_object* v_msg_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v_msg_203_, v___y_204_, v___y_205_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_207_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__0));
v___x_210_ = l_Lean_stringToMessageData(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__2));
v___x_213_ = l_Lean_stringToMessageData(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(lean_object* v_declName_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = l_Lean_Meta_Grind_grindExt;
lean_inc(v_declName_214_);
v___x_219_ = l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(v___x_218_, v_declName_214_, v_a_216_);
if (lean_obj_tag(v___x_219_) == 0)
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_235_; 
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_235_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_235_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_235_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
uint8_t v___x_224_; 
v___x_224_ = lean_unbox(v_a_220_);
lean_dec(v_a_220_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; 
lean_del_object(v___x_222_);
v___x_225_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
v___x_226_ = l_Lean_MessageData_ofName(v_declName_214_);
v___x_227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3);
v___x_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v___x_229_, v_a_215_, v_a_216_);
return v___x_230_;
}
else
{
lean_object* v___x_231_; lean_object* v___x_233_; 
lean_dec(v_declName_214_);
v___x_231_ = lean_box(0);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_231_);
v___x_233_ = v___x_222_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_declName_214_);
v_a_236_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_219_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_219_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___boxed(lean_object* v_declName_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_declName_244_, v_a_245_, v_a_246_);
lean_dec(v_a_246_);
lean_dec_ref(v_a_245_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0(lean_object* v_00_u03b1_249_, lean_object* v_msg_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v_msg_250_, v___y_251_, v___y_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___boxed(lean_object* v_00_u03b1_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0(v_00_u03b1_255_, v_msg_256_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_260_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_box(0);
v___x_262_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg(){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0);
v___x_266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___boxed(lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4(lean_object* v_00_u03b1_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___boxed(lean_object* v_00_u03b1_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4(v_00_u03b1_274_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_278_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___closed__0);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg();
return v_res_284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___lam__0(lean_object* v_addEntryFn_285_, lean_object* v___x_286_, lean_object* v_s_287_){
_start:
{
lean_object* v_importedEntries_288_; lean_object* v_state_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_297_; 
v_importedEntries_288_ = lean_ctor_get(v_s_287_, 0);
v_state_289_ = lean_ctor_get(v_s_287_, 1);
v_isSharedCheck_297_ = !lean_is_exclusive(v_s_287_);
if (v_isSharedCheck_297_ == 0)
{
v___x_291_ = v_s_287_;
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_state_289_);
lean_inc(v_importedEntries_288_);
lean_dec(v_s_287_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v_state_293_; lean_object* v___x_295_; 
v_state_293_ = lean_apply_2(v_addEntryFn_285_, v_state_289_, v___x_286_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v_state_293_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_importedEntries_288_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_state_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(lean_object* v_opts_298_, lean_object* v_opt_299_){
_start:
{
lean_object* v_name_300_; lean_object* v_defValue_301_; lean_object* v_map_302_; lean_object* v___x_303_; 
v_name_300_ = lean_ctor_get(v_opt_299_, 0);
v_defValue_301_ = lean_ctor_get(v_opt_299_, 1);
v_map_302_ = lean_ctor_get(v_opts_298_, 0);
v___x_303_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_302_, v_name_300_);
if (lean_obj_tag(v___x_303_) == 0)
{
uint8_t v___x_304_; 
v___x_304_ = lean_unbox(v_defValue_301_);
return v___x_304_;
}
else
{
lean_object* v_val_305_; 
v_val_305_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v___x_303_, 1);
if (lean_obj_tag(v_val_305_) == 1)
{
uint8_t v_v_306_; 
v_v_306_ = lean_ctor_get_uint8(v_val_305_, 0);
lean_dec_ref_known(v_val_305_, 0);
return v_v_306_;
}
else
{
uint8_t v___x_307_; 
lean_dec(v_val_305_);
v___x_307_ = lean_unbox(v_defValue_301_);
return v___x_307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5___boxed(lean_object* v_opts_308_, lean_object* v_opt_309_){
_start:
{
uint8_t v_res_310_; lean_object* v_r_311_; 
v_res_310_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(v_opts_308_, v_opt_309_);
lean_dec_ref(v_opt_309_);
lean_dec_ref(v_opts_308_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_box(1);
v___x_313_ = l_Lean_MessageData_ofFormat(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__2));
v___x_318_ = l_Lean_MessageData_ofFormat(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6(lean_object* v_x_319_, lean_object* v_x_320_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
return v_x_319_;
}
else
{
lean_object* v_head_321_; lean_object* v_tail_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_344_; 
v_head_321_ = lean_ctor_get(v_x_320_, 0);
v_tail_322_ = lean_ctor_get(v_x_320_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_x_320_);
if (v_isSharedCheck_344_ == 0)
{
v___x_324_ = v_x_320_;
v_isShared_325_ = v_isSharedCheck_344_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_tail_322_);
lean_inc(v_head_321_);
lean_dec(v_x_320_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_344_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v_before_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_342_; 
v_before_326_ = lean_ctor_get(v_head_321_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v_head_321_);
if (v_isSharedCheck_342_ == 0)
{
lean_object* v_unused_343_; 
v_unused_343_ = lean_ctor_get(v_head_321_, 1);
lean_dec(v_unused_343_);
v___x_328_ = v_head_321_;
v_isShared_329_ = v_isSharedCheck_342_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_before_326_);
lean_dec(v_head_321_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_342_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
v___x_330_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0);
if (v_isShared_329_ == 0)
{
lean_ctor_set_tag(v___x_328_, 7);
lean_ctor_set(v___x_328_, 1, v___x_330_);
lean_ctor_set(v___x_328_, 0, v_x_319_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_x_319_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_330_);
v___x_332_ = v_reuseFailAlloc_341_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_333_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__3);
if (v_isShared_325_ == 0)
{
lean_ctor_set_tag(v___x_324_, 7);
lean_ctor_set(v___x_324_, 1, v___x_333_);
lean_ctor_set(v___x_324_, 0, v___x_332_);
v___x_335_ = v___x_324_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_340_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = l_Lean_MessageData_ofSyntax(v_before_326_);
v___x_337_ = l_Lean_indentD(v___x_336_);
v___x_338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_335_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v_x_319_ = v___x_338_;
v_x_320_ = v_tail_322_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__1));
v___x_349_ = l_Lean_MessageData_ofFormat(v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg(lean_object* v_msgData_350_, lean_object* v_macroStack_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_354_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_352_);
v___x_355_ = l_Lean_Elab_pp_macroStack;
v___x_356_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(v___x_354_, v___x_355_);
lean_dec_ref(v___x_354_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
lean_dec(v_macroStack_351_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v_msgData_350_);
return v___x_357_;
}
else
{
if (lean_obj_tag(v_macroStack_351_) == 0)
{
lean_object* v___x_358_; 
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v_msgData_350_);
return v___x_358_;
}
else
{
lean_object* v_head_359_; lean_object* v_after_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_375_; 
v_head_359_ = lean_ctor_get(v_macroStack_351_, 0);
lean_inc(v_head_359_);
v_after_360_ = lean_ctor_get(v_head_359_, 1);
v_isSharedCheck_375_ = !lean_is_exclusive(v_head_359_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v_head_359_, 0);
lean_dec(v_unused_376_);
v___x_362_ = v_head_359_;
v_isShared_363_ = v_isSharedCheck_375_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_after_360_);
lean_dec(v_head_359_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_375_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_364_; lean_object* v___x_366_; 
v___x_364_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0);
if (v_isShared_363_ == 0)
{
lean_ctor_set_tag(v___x_362_, 7);
lean_ctor_set(v___x_362_, 1, v___x_364_);
lean_ctor_set(v___x_362_, 0, v_msgData_350_);
v___x_366_ = v___x_362_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_msgData_350_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_364_);
v___x_366_ = v_reuseFailAlloc_374_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_msgData_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_367_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__2);
v___x_368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_366_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = l_Lean_MessageData_ofSyntax(v_after_360_);
v___x_370_ = l_Lean_indentD(v___x_369_);
v_msgData_371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_371_, 0, v___x_368_);
lean_ctor_set(v_msgData_371_, 1, v___x_370_);
v___x_372_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6(v_msgData_371_, v_macroStack_351_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_377_, lean_object* v_macroStack_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg(v_msgData_377_, v_macroStack_378_, v___y_379_);
lean_dec_ref(v___y_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(lean_object* v_msgData_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_){
_start:
{
lean_object* v___x_388_; lean_object* v_env_389_; uint8_t v___x_390_; lean_object* v_env_391_; lean_object* v___x_392_; lean_object* v_toCold_393_; lean_object* v_mctx_394_; lean_object* v_lctx_395_; lean_object* v_options_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_388_ = lean_st_ref_get(v___y_386_);
v_env_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc_ref(v_env_389_);
lean_dec(v___x_388_);
v___x_390_ = 0;
v_env_391_ = l_Lean_Environment_setRecordingDeps(v_env_389_, v___x_390_);
v___x_392_ = lean_st_ref_get(v___y_384_);
v_toCold_393_ = lean_ctor_get(v___y_385_, 0);
v_mctx_394_ = lean_ctor_get(v___x_392_, 0);
lean_inc_ref(v_mctx_394_);
lean_dec(v___x_392_);
v_lctx_395_ = lean_ctor_get(v___y_383_, 2);
v_options_396_ = lean_ctor_get(v_toCold_393_, 2);
lean_inc_ref(v_options_396_);
lean_inc_ref(v_lctx_395_);
v___x_397_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_397_, 0, v_env_391_);
lean_ctor_set(v___x_397_, 1, v_mctx_394_);
lean_ctor_set(v___x_397_, 2, v_lctx_395_);
lean_ctor_set(v___x_397_, 3, v_options_396_);
v___x_398_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_msgData_382_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2___boxed(lean_object* v_msgData_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(v_msgData_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v___y_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(lean_object* v_msg_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_ref_415_; lean_object* v_macroStack_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_a_419_; lean_object* v___x_420_; lean_object* v_a_421_; lean_object* v___x_423_; uint8_t v_isShared_424_; uint8_t v_isSharedCheck_429_; 
v_ref_415_ = lean_ctor_get(v___y_412_, 2);
v_macroStack_416_ = lean_ctor_get(v___y_408_, 1);
v___x_417_ = l_Lean_Elab_getBetterRef(v_ref_415_, v_macroStack_416_);
v___x_418_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(v_msg_407_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref(v___x_418_);
lean_inc(v_macroStack_416_);
v___x_420_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg(v_a_419_, v_macroStack_416_, v___y_412_);
v_a_421_ = lean_ctor_get(v___x_420_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_429_ == 0)
{
v___x_423_ = v___x_420_;
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
else
{
lean_inc(v_a_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_box(0);
v_isShared_424_ = v_isSharedCheck_429_;
goto v_resetjp_422_;
}
v_resetjp_422_:
{
lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_417_);
lean_ctor_set(v___x_425_, 1, v_a_421_);
if (v_isShared_424_ == 0)
{
lean_ctor_set_tag(v___x_423_, 1);
lean_ctor_set(v___x_423_, 0, v___x_425_);
v___x_427_ = v___x_423_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg___boxed(lean_object* v_msg_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(v_msg_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
return v_res_438_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2(void){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg();
return v___x_443_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3(void){
_start:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__4(void){
_start:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0);
v___x_448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
lean_ctor_set(v___x_448_, 2, v___x_446_);
return v___x_448_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_449_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__4);
v___x_450_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3);
v___x_451_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0);
v___x_452_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2);
v___x_453_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_450_);
lean_ctor_set(v___x_453_, 3, v___x_451_);
lean_ctor_set(v___x_453_, 4, v___x_451_);
lean_ctor_set(v___x_453_, 5, v___x_451_);
lean_ctor_set(v___x_453_, 6, v___x_451_);
lean_ctor_set(v___x_453_, 7, v___x_449_);
return v___x_453_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__7(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__6));
v___x_456_ = l_Lean_stringToMessageData(v___x_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(uint8_t v___y_457_, lean_object* v_as_458_, size_t v_sz_459_, size_t v_i_460_, lean_object* v_b_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_lt(v_i_460_, v_sz_459_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_b_461_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v_nextMacroScope_475_; lean_object* v_ngen_476_; lean_object* v_auxDeclNGen_477_; lean_object* v_traceState_478_; lean_object* v_recordedDeps_479_; lean_object* v_messages_480_; lean_object* v_infoState_481_; lean_object* v_snapshotTasks_482_; lean_object* v___y_483_; lean_object* v___x_505_; lean_object* v_a_506_; lean_object* v___x_507_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___x_531_; lean_object* v_env_532_; lean_object* v___x_533_; lean_object* v_toEnvExtension_534_; lean_object* v_asyncMode_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_471_ = lean_box(0);
v___x_505_ = lean_box(1);
v_a_506_ = lean_array_uget_borrowed(v_as_458_, v_i_460_);
v___x_507_ = l_Lean_TSyntax_getId(v_a_506_);
v___x_531_ = lean_st_ref_get(v___y_467_);
v_env_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc_ref(v_env_532_);
lean_dec(v___x_531_);
v___x_533_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_534_ = lean_ctor_get(v___x_533_, 0);
v_asyncMode_535_ = lean_ctor_get(v_toEnvExtension_534_, 2);
v___x_536_ = lean_box(0);
v___x_537_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_505_, v___x_533_, v_env_532_, v_asyncMode_535_, v___x_536_);
v___x_538_ = l_Lean_NameSet_contains(v___x_537_, v___x_507_);
lean_dec(v___x_537_);
if (v___x_538_ == 0)
{
v___y_509_ = v___y_465_;
v___y_510_ = v___y_467_;
goto v___jp_508_;
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_539_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v___x_507_);
v___x_540_ = l_Lean_MessageData_ofName(v___x_507_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_539_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__7);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(v___x_543_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_dec_ref_known(v___x_544_, 1);
v___y_509_ = v___y_465_;
v___y_510_ = v___y_467_;
goto v___jp_508_;
}
else
{
lean_dec(v___x_507_);
return v___x_544_;
}
}
v___jp_472_:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v_mctx_488_; lean_object* v_zetaDeltaFVarIds_489_; lean_object* v_postponed_490_; lean_object* v_diag_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_503_; 
v___x_484_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1);
v___x_485_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_485_, 0, v___y_483_);
lean_ctor_set(v___x_485_, 1, v_nextMacroScope_475_);
lean_ctor_set(v___x_485_, 2, v_ngen_476_);
lean_ctor_set(v___x_485_, 3, v_auxDeclNGen_477_);
lean_ctor_set(v___x_485_, 4, v_traceState_478_);
lean_ctor_set(v___x_485_, 5, v___x_484_);
lean_ctor_set(v___x_485_, 6, v_recordedDeps_479_);
lean_ctor_set(v___x_485_, 7, v_messages_480_);
lean_ctor_set(v___x_485_, 8, v_infoState_481_);
lean_ctor_set(v___x_485_, 9, v_snapshotTasks_482_);
v___x_486_ = lean_st_ref_put(v___y_473_, v___x_485_);
v___x_487_ = lean_st_ref_take(v___y_474_);
v_mctx_488_ = lean_ctor_get(v___x_487_, 0);
v_zetaDeltaFVarIds_489_ = lean_ctor_get(v___x_487_, 2);
v_postponed_490_ = lean_ctor_get(v___x_487_, 3);
v_diag_491_ = lean_ctor_get(v___x_487_, 4);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v___x_487_, 1);
lean_dec(v_unused_504_);
v___x_493_ = v___x_487_;
v_isShared_494_ = v_isSharedCheck_503_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_diag_491_);
lean_inc(v_postponed_490_);
lean_inc(v_zetaDeltaFVarIds_489_);
lean_inc(v_mctx_488_);
lean_dec(v___x_487_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_503_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_mctx_488_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_495_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_zetaDeltaFVarIds_489_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_postponed_490_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_diag_491_);
v___x_497_ = v_reuseFailAlloc_502_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; size_t v___x_499_; size_t v___x_500_; 
v___x_498_ = lean_st_ref_put(v___y_474_, v___x_497_);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_460_, v___x_499_);
v_i_460_ = v___x_500_;
v_b_461_ = v___x_471_;
goto _start;
}
}
}
v___jp_508_:
{
lean_object* v___x_511_; lean_object* v_env_512_; lean_object* v_nextMacroScope_513_; lean_object* v_ngen_514_; lean_object* v_auxDeclNGen_515_; lean_object* v_traceState_516_; lean_object* v_recordedDeps_517_; lean_object* v_messages_518_; lean_object* v_infoState_519_; lean_object* v_snapshotTasks_520_; lean_object* v___x_521_; lean_object* v_toEnvExtension_522_; lean_object* v_addEntryFn_523_; lean_object* v_asyncMode_524_; uint8_t v_logWrites_525_; lean_object* v___f_526_; lean_object* v___x_527_; 
v___x_511_ = lean_st_ref_take(v___y_510_);
v_env_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc_ref(v_env_512_);
v_nextMacroScope_513_ = lean_ctor_get(v___x_511_, 1);
lean_inc(v_nextMacroScope_513_);
v_ngen_514_ = lean_ctor_get(v___x_511_, 2);
lean_inc_ref(v_ngen_514_);
v_auxDeclNGen_515_ = lean_ctor_get(v___x_511_, 3);
lean_inc_ref(v_auxDeclNGen_515_);
v_traceState_516_ = lean_ctor_get(v___x_511_, 4);
lean_inc_ref(v_traceState_516_);
v_recordedDeps_517_ = lean_ctor_get(v___x_511_, 6);
lean_inc_ref(v_recordedDeps_517_);
v_messages_518_ = lean_ctor_get(v___x_511_, 7);
lean_inc_ref(v_messages_518_);
v_infoState_519_ = lean_ctor_get(v___x_511_, 8);
lean_inc_ref(v_infoState_519_);
v_snapshotTasks_520_ = lean_ctor_get(v___x_511_, 9);
lean_inc_ref(v_snapshotTasks_520_);
lean_dec(v___x_511_);
v___x_521_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_522_ = lean_ctor_get(v___x_521_, 0);
v_addEntryFn_523_ = lean_ctor_get(v___x_521_, 3);
v_asyncMode_524_ = lean_ctor_get(v_toEnvExtension_522_, 2);
v_logWrites_525_ = lean_ctor_get_uint8(v_toEnvExtension_522_, sizeof(void*)*6);
lean_inc(v_addEntryFn_523_);
v___f_526_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_526_, 0, v_addEntryFn_523_);
lean_closure_set(v___f_526_, 1, v___x_507_);
v___x_527_ = lean_box(0);
if (v_logWrites_525_ == 0)
{
lean_object* v___x_528_; 
lean_inc_ref(v_toEnvExtension_522_);
v___x_528_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_522_, v_env_512_, v___f_526_, v_asyncMode_524_, v___x_527_, v___y_457_);
v___y_473_ = v___y_510_;
v___y_474_ = v___y_509_;
v_nextMacroScope_475_ = v_nextMacroScope_513_;
v_ngen_476_ = v_ngen_514_;
v_auxDeclNGen_477_ = v_auxDeclNGen_515_;
v_traceState_478_ = v_traceState_516_;
v_recordedDeps_479_ = v_recordedDeps_517_;
v_messages_480_ = v_messages_518_;
v_infoState_481_ = v_infoState_519_;
v_snapshotTasks_482_ = v_snapshotTasks_520_;
v___y_483_ = v___x_528_;
goto v___jp_472_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_inc_ref_n(v_toEnvExtension_522_, 2);
v___x_529_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_522_, v_env_512_);
lean_dec_ref(v_env_512_);
v___x_530_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_522_, v___x_529_, v___f_526_, v_asyncMode_524_, v___x_527_, v___y_457_);
v___y_473_ = v___y_510_;
v___y_474_ = v___y_509_;
v_nextMacroScope_475_ = v_nextMacroScope_513_;
v_ngen_476_ = v_ngen_514_;
v_auxDeclNGen_477_ = v_auxDeclNGen_515_;
v_traceState_478_ = v_traceState_516_;
v_recordedDeps_479_ = v_recordedDeps_517_;
v_messages_480_ = v_messages_518_;
v_infoState_481_ = v_infoState_519_;
v_snapshotTasks_482_ = v_snapshotTasks_520_;
v___y_483_ = v___x_530_;
goto v___jp_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___boxed(lean_object* v___y_545_, lean_object* v_as_546_, lean_object* v_sz_547_, lean_object* v_i_548_, lean_object* v_b_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
uint8_t v___y_8768__boxed_557_; size_t v_sz_boxed_558_; size_t v_i_boxed_559_; lean_object* v_res_560_; 
v___y_8768__boxed_557_ = lean_unbox(v___y_545_);
v_sz_boxed_558_ = lean_unbox_usize(v_sz_547_);
lean_dec(v_sz_547_);
v_i_boxed_559_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(v___y_8768__boxed_557_, v_as_546_, v_sz_boxed_558_, v_i_boxed_559_, v_b_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec_ref(v_as_546_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___lam__0(lean_object* v_addEntryFn_561_, lean_object* v_a_562_, lean_object* v_s_563_){
_start:
{
lean_object* v_importedEntries_564_; lean_object* v_state_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_573_; 
v_importedEntries_564_ = lean_ctor_get(v_s_563_, 0);
v_state_565_ = lean_ctor_get(v_s_563_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_s_563_);
if (v_isSharedCheck_573_ == 0)
{
v___x_567_ = v_s_563_;
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_state_565_);
lean_inc(v_importedEntries_564_);
lean_dec(v_s_563_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_573_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_state_569_; lean_object* v___x_571_; 
v_state_569_ = lean_apply_2(v_addEntryFn_561_, v_state_565_, v_a_562_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v_state_569_);
v___x_571_ = v___x_567_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_importedEntries_564_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_state_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0));
v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(uint8_t v___x_577_, lean_object* v_as_578_, size_t v_sz_579_, size_t v_i_580_, lean_object* v_b_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v___x_589_; 
v___x_589_ = lean_usize_dec_lt(v_i_580_, v_sz_579_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_590_, 0, v_b_581_);
return v___x_590_;
}
else
{
lean_object* v___x_591_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v_nextMacroScope_595_; lean_object* v_ngen_596_; lean_object* v_auxDeclNGen_597_; lean_object* v_traceState_598_; lean_object* v_recordedDeps_599_; lean_object* v_messages_600_; lean_object* v_infoState_601_; lean_object* v_snapshotTasks_602_; lean_object* v___y_603_; lean_object* v___x_625_; lean_object* v_a_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_591_ = lean_box(0);
v___x_625_ = lean_box(1);
v_a_626_ = lean_array_uget_borrowed(v_as_578_, v_i_580_);
v___x_627_ = lean_box(0);
lean_inc(v_a_626_);
v___x_628_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_626_, v___x_627_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___x_653_; lean_object* v___x_654_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc_n(v_a_629_, 2);
lean_dec_ref_known(v___x_628_, 1);
v___x_653_ = lean_box(1);
v___x_654_ = l_Lean_Linter_checkDeprecatedAt(v_a_626_, v_a_629_, v___x_653_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v___x_655_; 
lean_dec_ref_known(v___x_654_, 1);
lean_inc(v_a_629_);
v___x_655_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_a_629_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_656_; lean_object* v_env_657_; lean_object* v___x_658_; lean_object* v_toEnvExtension_659_; lean_object* v_asyncMode_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
lean_dec_ref_known(v___x_655_, 1);
v___x_656_ = lean_st_ref_get(v___y_587_);
v_env_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc_ref(v_env_657_);
lean_dec(v___x_656_);
v___x_658_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_659_ = lean_ctor_get(v___x_658_, 0);
v_asyncMode_660_ = lean_ctor_get(v_toEnvExtension_659_, 2);
v___x_661_ = lean_box(0);
v___x_662_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_625_, v___x_658_, v_env_657_, v_asyncMode_660_, v___x_661_);
v___x_663_ = l_Lean_NameSet_contains(v___x_662_, v_a_629_);
lean_dec(v___x_662_);
if (v___x_663_ == 0)
{
v___y_631_ = v___y_585_;
v___y_632_ = v___y_587_;
goto v___jp_630_;
}
else
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_664_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v_a_629_);
v___x_665_ = l_Lean_MessageData_ofName(v_a_629_);
v___x_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_664_);
lean_ctor_set(v___x_666_, 1, v___x_665_);
v___x_667_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1);
v___x_668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_666_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___x_669_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(v___x_668_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_669_) == 0)
{
lean_dec_ref_known(v___x_669_, 1);
v___y_631_ = v___y_585_;
v___y_632_ = v___y_587_;
goto v___jp_630_;
}
else
{
lean_dec(v_a_629_);
return v___x_669_;
}
}
}
else
{
lean_dec(v_a_629_);
return v___x_655_;
}
}
else
{
lean_dec(v_a_629_);
return v___x_654_;
}
v___jp_630_:
{
lean_object* v___x_633_; lean_object* v_env_634_; lean_object* v_nextMacroScope_635_; lean_object* v_ngen_636_; lean_object* v_auxDeclNGen_637_; lean_object* v_traceState_638_; lean_object* v_recordedDeps_639_; lean_object* v_messages_640_; lean_object* v_infoState_641_; lean_object* v_snapshotTasks_642_; lean_object* v___x_643_; lean_object* v_toEnvExtension_644_; lean_object* v_addEntryFn_645_; lean_object* v_asyncMode_646_; uint8_t v_logWrites_647_; lean_object* v___f_648_; lean_object* v___x_649_; 
v___x_633_ = lean_st_ref_take(v___y_632_);
v_env_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_env_634_);
v_nextMacroScope_635_ = lean_ctor_get(v___x_633_, 1);
lean_inc(v_nextMacroScope_635_);
v_ngen_636_ = lean_ctor_get(v___x_633_, 2);
lean_inc_ref(v_ngen_636_);
v_auxDeclNGen_637_ = lean_ctor_get(v___x_633_, 3);
lean_inc_ref(v_auxDeclNGen_637_);
v_traceState_638_ = lean_ctor_get(v___x_633_, 4);
lean_inc_ref(v_traceState_638_);
v_recordedDeps_639_ = lean_ctor_get(v___x_633_, 6);
lean_inc_ref(v_recordedDeps_639_);
v_messages_640_ = lean_ctor_get(v___x_633_, 7);
lean_inc_ref(v_messages_640_);
v_infoState_641_ = lean_ctor_get(v___x_633_, 8);
lean_inc_ref(v_infoState_641_);
v_snapshotTasks_642_ = lean_ctor_get(v___x_633_, 9);
lean_inc_ref(v_snapshotTasks_642_);
lean_dec(v___x_633_);
v___x_643_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_644_ = lean_ctor_get(v___x_643_, 0);
v_addEntryFn_645_ = lean_ctor_get(v___x_643_, 3);
v_asyncMode_646_ = lean_ctor_get(v_toEnvExtension_644_, 2);
v_logWrites_647_ = lean_ctor_get_uint8(v_toEnvExtension_644_, sizeof(void*)*6);
lean_inc(v_addEntryFn_645_);
v___f_648_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_648_, 0, v_addEntryFn_645_);
lean_closure_set(v___f_648_, 1, v_a_629_);
v___x_649_ = lean_box(0);
if (v_logWrites_647_ == 0)
{
lean_object* v___x_650_; 
lean_inc_ref(v_toEnvExtension_644_);
v___x_650_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_644_, v_env_634_, v___f_648_, v_asyncMode_646_, v___x_649_, v___x_577_);
v___y_593_ = v___y_631_;
v___y_594_ = v___y_632_;
v_nextMacroScope_595_ = v_nextMacroScope_635_;
v_ngen_596_ = v_ngen_636_;
v_auxDeclNGen_597_ = v_auxDeclNGen_637_;
v_traceState_598_ = v_traceState_638_;
v_recordedDeps_599_ = v_recordedDeps_639_;
v_messages_600_ = v_messages_640_;
v_infoState_601_ = v_infoState_641_;
v_snapshotTasks_602_ = v_snapshotTasks_642_;
v___y_603_ = v___x_650_;
goto v___jp_592_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_inc_ref_n(v_toEnvExtension_644_, 2);
v___x_651_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_644_, v_env_634_);
lean_dec_ref(v_env_634_);
v___x_652_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_644_, v___x_651_, v___f_648_, v_asyncMode_646_, v___x_649_, v___x_577_);
v___y_593_ = v___y_631_;
v___y_594_ = v___y_632_;
v_nextMacroScope_595_ = v_nextMacroScope_635_;
v_ngen_596_ = v_ngen_636_;
v_auxDeclNGen_597_ = v_auxDeclNGen_637_;
v_traceState_598_ = v_traceState_638_;
v_recordedDeps_599_ = v_recordedDeps_639_;
v_messages_600_ = v_messages_640_;
v_infoState_601_ = v_infoState_641_;
v_snapshotTasks_602_ = v_snapshotTasks_642_;
v___y_603_ = v___x_652_;
goto v___jp_592_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
v_a_670_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_628_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_628_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
v___jp_592_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_mctx_608_; lean_object* v_zetaDeltaFVarIds_609_; lean_object* v_postponed_610_; lean_object* v_diag_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_623_; 
v___x_604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1);
v___x_605_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_605_, 0, v___y_603_);
lean_ctor_set(v___x_605_, 1, v_nextMacroScope_595_);
lean_ctor_set(v___x_605_, 2, v_ngen_596_);
lean_ctor_set(v___x_605_, 3, v_auxDeclNGen_597_);
lean_ctor_set(v___x_605_, 4, v_traceState_598_);
lean_ctor_set(v___x_605_, 5, v___x_604_);
lean_ctor_set(v___x_605_, 6, v_recordedDeps_599_);
lean_ctor_set(v___x_605_, 7, v_messages_600_);
lean_ctor_set(v___x_605_, 8, v_infoState_601_);
lean_ctor_set(v___x_605_, 9, v_snapshotTasks_602_);
v___x_606_ = lean_st_ref_put(v___y_594_, v___x_605_);
v___x_607_ = lean_st_ref_take(v___y_593_);
v_mctx_608_ = lean_ctor_get(v___x_607_, 0);
v_zetaDeltaFVarIds_609_ = lean_ctor_get(v___x_607_, 2);
v_postponed_610_ = lean_ctor_get(v___x_607_, 3);
v_diag_611_ = lean_ctor_get(v___x_607_, 4);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v___x_607_, 1);
lean_dec(v_unused_624_);
v___x_613_ = v___x_607_;
v_isShared_614_ = v_isSharedCheck_623_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_diag_611_);
lean_inc(v_postponed_610_);
lean_inc(v_zetaDeltaFVarIds_609_);
lean_inc(v_mctx_608_);
lean_dec(v___x_607_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_623_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_615_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_615_);
v___x_617_ = v___x_613_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_mctx_608_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_zetaDeltaFVarIds_609_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v_postponed_610_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v_diag_611_);
v___x_617_ = v_reuseFailAlloc_622_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; size_t v___x_619_; size_t v___x_620_; 
v___x_618_ = lean_st_ref_put(v___y_593_, v___x_617_);
v___x_619_ = ((size_t)1ULL);
v___x_620_ = lean_usize_add(v_i_580_, v___x_619_);
v_i_580_ = v___x_620_;
v_b_581_ = v___x_591_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___boxed(lean_object* v___x_678_, lean_object* v_as_679_, lean_object* v_sz_680_, lean_object* v_i_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
uint8_t v___x_8954__boxed_690_; size_t v_sz_boxed_691_; size_t v_i_boxed_692_; lean_object* v_res_693_; 
v___x_8954__boxed_690_ = lean_unbox(v___x_678_);
v_sz_boxed_691_ = lean_unbox_usize(v_sz_680_);
lean_dec(v_sz_680_);
v_i_boxed_692_ = lean_unbox_usize(v_i_681_);
lean_dec(v_i_681_);
v_res_693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(v___x_8954__boxed_690_, v_as_679_, v_sz_boxed_691_, v_i_boxed_692_, v_b_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec_ref(v_as_679_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(uint8_t v___y_694_, lean_object* v_ids_695_, uint8_t v___x_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
if (v___y_694_ == 0)
{
lean_object* v___x_704_; size_t v_sz_705_; size_t v___x_706_; lean_object* v___x_707_; 
v___x_704_ = lean_box(0);
v_sz_705_ = lean_array_size(v_ids_695_);
v___x_706_ = ((size_t)0ULL);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(v___x_696_, v_ids_695_, v_sz_705_, v___x_706_, v___x_704_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_714_ == 0)
{
lean_object* v_unused_715_; 
v_unused_715_ = lean_ctor_get(v___x_707_, 0);
lean_dec(v_unused_715_);
v___x_709_ = v___x_707_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_dec(v___x_707_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_704_);
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_704_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
else
{
return v___x_707_;
}
}
else
{
lean_object* v___x_716_; size_t v_sz_717_; size_t v___x_718_; lean_object* v___x_719_; 
v___x_716_ = lean_box(0);
v_sz_717_ = lean_array_size(v_ids_695_);
v___x_718_ = ((size_t)0ULL);
v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(v___y_694_, v_ids_695_, v_sz_717_, v___x_718_, v___x_716_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v___x_719_, 0);
lean_dec(v_unused_727_);
v___x_721_ = v___x_719_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_dec(v___x_719_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v___x_716_);
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_716_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed(lean_object* v___y_728_, lean_object* v_ids_729_, lean_object* v___x_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
uint8_t v___y_9107__boxed_738_; uint8_t v___x_9108__boxed_739_; lean_object* v_res_740_; 
v___y_9107__boxed_738_ = lean_unbox(v___y_728_);
v___x_9108__boxed_739_ = lean_unbox(v___x_730_);
v_res_740_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(v___y_9107__boxed_738_, v_ids_729_, v___x_9108__boxed_739_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
lean_dec(v___y_736_);
lean_dec_ref(v___y_735_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v_ids_729_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(lean_object* v_stx_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; uint8_t v___x_751_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; uint8_t v___y_756_; lean_object* v_sfx_x3f_762_; lean_object* v___y_763_; lean_object* v___y_764_; 
v___x_750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1));
lean_inc(v_stx_746_);
v___x_751_ = l_Lean_Syntax_isOfKind(v_stx_746_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_769_; 
lean_dec(v_stx_746_);
v___x_769_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
return v___x_769_;
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_770_ = lean_unsigned_to_nat(2u);
v___x_771_ = l_Lean_Syntax_getArg(v_stx_746_, v___x_770_);
v___x_772_ = l_Lean_Syntax_isNone(v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; uint8_t v___x_774_; 
v___x_773_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_771_);
v___x_774_ = l_Lean_Syntax_matchesNull(v___x_771_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v___x_771_);
lean_dec(v_stx_746_);
v___x_775_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
return v___x_775_;
}
else
{
lean_object* v___x_776_; lean_object* v_sfx_x3f_777_; lean_object* v___x_778_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v_sfx_x3f_777_ = l_Lean_Syntax_getArg(v___x_771_, v___x_776_);
lean_dec(v___x_771_);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v_sfx_x3f_777_);
v_sfx_x3f_762_ = v___x_778_;
v___y_763_ = v_a_747_;
v___y_764_ = v_a_748_;
goto v___jp_761_;
}
}
else
{
lean_object* v___x_779_; 
lean_dec(v___x_771_);
v___x_779_ = lean_box(0);
v_sfx_x3f_762_ = v___x_779_;
v___y_763_ = v_a_747_;
v___y_764_ = v_a_748_;
goto v___jp_761_;
}
}
v___jp_752_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___y_759_; lean_object* v___x_760_; 
v___x_757_ = lean_box(v___y_756_);
v___x_758_ = lean_box(v___x_751_);
v___y_759_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed), 10, 3);
lean_closure_set(v___y_759_, 0, v___x_757_);
lean_closure_set(v___y_759_, 1, v___y_755_);
lean_closure_set(v___y_759_, 2, v___x_758_);
v___x_760_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_759_, v___y_753_, v___y_754_);
return v___x_760_;
}
v___jp_761_:
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v_ids_767_; 
v___x_765_ = lean_unsigned_to_nat(3u);
v___x_766_ = l_Lean_Syntax_getArg(v_stx_746_, v___x_765_);
lean_dec(v_stx_746_);
v_ids_767_ = l_Lean_Syntax_getArgs(v___x_766_);
lean_dec(v___x_766_);
if (lean_obj_tag(v_sfx_x3f_762_) == 0)
{
uint8_t v___x_768_; 
v___x_768_ = 0;
v___y_753_ = v___y_763_;
v___y_754_ = v___y_764_;
v___y_755_ = v_ids_767_;
v___y_756_ = v___x_768_;
goto v___jp_752_;
}
else
{
lean_dec_ref_known(v_sfx_x3f_762_, 1);
v___y_753_ = v___y_763_;
v___y_754_ = v___y_764_;
v___y_755_ = v_ids_767_;
v___y_756_ = v___x_751_;
goto v___jp_752_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed(lean_object* v_stx_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(v_stx_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(lean_object* v_00_u03b2_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg___boxed(lean_object* v___dummy_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg();
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0(lean_object* v_00_u03b2_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(lean_object* v_00_u03b1_793_, lean_object* v_msg_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; 
v___x_802_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(v_msg_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___boxed(lean_object* v_00_u03b1_803_, lean_object* v_msg_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(v_00_u03b1_803_, v_msg_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3(lean_object* v_msgData_813_, lean_object* v_macroStack_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg(v_msgData_813_, v_macroStack_814_, v___y_819_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___boxed(lean_object* v_msgData_823_, lean_object* v_macroStack_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3(v_msgData_823_, v_macroStack_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1(){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_838_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_839_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1));
v___x_840_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1));
v___x_841_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed), 4, 0);
v___x_842_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_838_, v___x_839_, v___x_840_, v___x_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___boxed(lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1();
return v_res_844_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0));
v___x_847_ = l_Lean_stringToMessageData(v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(uint8_t v___x_848_, lean_object* v_as_849_, size_t v_sz_850_, size_t v_i_851_, lean_object* v_b_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_860_ == 0)
{
lean_object* v___x_861_; 
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v_b_852_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; lean_object* v___y_864_; lean_object* v_nextMacroScope_865_; lean_object* v_ngen_866_; lean_object* v_auxDeclNGen_867_; lean_object* v_traceState_868_; lean_object* v_recordedDeps_869_; lean_object* v_messages_870_; lean_object* v_infoState_871_; lean_object* v_snapshotTasks_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___x_896_; lean_object* v_a_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_862_ = lean_box(0);
v___x_896_ = lean_box(1);
v_a_897_ = lean_array_uget_borrowed(v_as_849_, v_i_851_);
v___x_898_ = lean_box(0);
lean_inc(v_a_897_);
v___x_899_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_897_, v___x_898_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc_n(v_a_900_, 2);
lean_dec_ref_known(v___x_899_, 1);
v___x_924_ = lean_box(1);
v___x_925_ = l_Lean_Linter_checkDeprecatedAt(v_a_897_, v_a_900_, v___x_924_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v___x_926_; 
lean_dec_ref_known(v___x_925_, 1);
lean_inc(v_a_900_);
v___x_926_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_a_900_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v___x_927_; lean_object* v_env_928_; lean_object* v___x_929_; lean_object* v_toEnvExtension_930_; lean_object* v_asyncMode_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
lean_dec_ref_known(v___x_926_, 1);
v___x_927_ = lean_st_ref_get(v___y_858_);
v_env_928_ = lean_ctor_get(v___x_927_, 0);
lean_inc_ref(v_env_928_);
lean_dec(v___x_927_);
v___x_929_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_930_ = lean_ctor_get(v___x_929_, 0);
v_asyncMode_931_ = lean_ctor_get(v_toEnvExtension_930_, 2);
v___x_932_ = lean_box(0);
v___x_933_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_896_, v___x_929_, v_env_928_, v_asyncMode_931_, v___x_932_);
v___x_934_ = l_Lean_NameSet_contains(v___x_933_, v_a_900_);
lean_dec(v___x_933_);
if (v___x_934_ == 0)
{
v___y_902_ = v___y_856_;
v___y_903_ = v___y_858_;
goto v___jp_901_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_935_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v_a_900_);
v___x_936_ = l_Lean_MessageData_ofName(v_a_900_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(v___x_939_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_dec_ref_known(v___x_940_, 1);
v___y_902_ = v___y_856_;
v___y_903_ = v___y_858_;
goto v___jp_901_;
}
else
{
lean_dec(v_a_900_);
return v___x_940_;
}
}
}
else
{
lean_dec(v_a_900_);
return v___x_926_;
}
}
else
{
lean_dec(v_a_900_);
return v___x_925_;
}
v___jp_901_:
{
lean_object* v___x_904_; lean_object* v_env_905_; lean_object* v_nextMacroScope_906_; lean_object* v_ngen_907_; lean_object* v_auxDeclNGen_908_; lean_object* v_traceState_909_; lean_object* v_recordedDeps_910_; lean_object* v_messages_911_; lean_object* v_infoState_912_; lean_object* v_snapshotTasks_913_; lean_object* v___x_914_; lean_object* v_toEnvExtension_915_; lean_object* v_addEntryFn_916_; lean_object* v_asyncMode_917_; uint8_t v_logWrites_918_; lean_object* v___f_919_; lean_object* v___x_920_; 
v___x_904_ = lean_st_ref_take(v___y_903_);
v_env_905_ = lean_ctor_get(v___x_904_, 0);
lean_inc_ref(v_env_905_);
v_nextMacroScope_906_ = lean_ctor_get(v___x_904_, 1);
lean_inc(v_nextMacroScope_906_);
v_ngen_907_ = lean_ctor_get(v___x_904_, 2);
lean_inc_ref(v_ngen_907_);
v_auxDeclNGen_908_ = lean_ctor_get(v___x_904_, 3);
lean_inc_ref(v_auxDeclNGen_908_);
v_traceState_909_ = lean_ctor_get(v___x_904_, 4);
lean_inc_ref(v_traceState_909_);
v_recordedDeps_910_ = lean_ctor_get(v___x_904_, 6);
lean_inc_ref(v_recordedDeps_910_);
v_messages_911_ = lean_ctor_get(v___x_904_, 7);
lean_inc_ref(v_messages_911_);
v_infoState_912_ = lean_ctor_get(v___x_904_, 8);
lean_inc_ref(v_infoState_912_);
v_snapshotTasks_913_ = lean_ctor_get(v___x_904_, 9);
lean_inc_ref(v_snapshotTasks_913_);
lean_dec(v___x_904_);
v___x_914_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_915_ = lean_ctor_get(v___x_914_, 0);
v_addEntryFn_916_ = lean_ctor_get(v___x_914_, 3);
v_asyncMode_917_ = lean_ctor_get(v_toEnvExtension_915_, 2);
v_logWrites_918_ = lean_ctor_get_uint8(v_toEnvExtension_915_, sizeof(void*)*6);
lean_inc(v_addEntryFn_916_);
v___f_919_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_919_, 0, v_addEntryFn_916_);
lean_closure_set(v___f_919_, 1, v_a_900_);
v___x_920_ = lean_box(0);
if (v_logWrites_918_ == 0)
{
lean_object* v___x_921_; 
lean_inc_ref(v_toEnvExtension_915_);
v___x_921_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_915_, v_env_905_, v___f_919_, v_asyncMode_917_, v___x_920_, v___x_848_);
v___y_864_ = v___y_902_;
v_nextMacroScope_865_ = v_nextMacroScope_906_;
v_ngen_866_ = v_ngen_907_;
v_auxDeclNGen_867_ = v_auxDeclNGen_908_;
v_traceState_868_ = v_traceState_909_;
v_recordedDeps_869_ = v_recordedDeps_910_;
v_messages_870_ = v_messages_911_;
v_infoState_871_ = v_infoState_912_;
v_snapshotTasks_872_ = v_snapshotTasks_913_;
v___y_873_ = v___y_903_;
v___y_874_ = v___x_921_;
goto v___jp_863_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; 
lean_inc_ref_n(v_toEnvExtension_915_, 2);
v___x_922_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_915_, v_env_905_);
lean_dec_ref(v_env_905_);
v___x_923_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_915_, v___x_922_, v___f_919_, v_asyncMode_917_, v___x_920_, v___x_848_);
v___y_864_ = v___y_902_;
v_nextMacroScope_865_ = v_nextMacroScope_906_;
v_ngen_866_ = v_ngen_907_;
v_auxDeclNGen_867_ = v_auxDeclNGen_908_;
v_traceState_868_ = v_traceState_909_;
v_recordedDeps_869_ = v_recordedDeps_910_;
v_messages_870_ = v_messages_911_;
v_infoState_871_ = v_infoState_912_;
v_snapshotTasks_872_ = v_snapshotTasks_913_;
v___y_873_ = v___y_903_;
v___y_874_ = v___x_923_;
goto v___jp_863_;
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
v_a_941_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_899_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_899_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
v___jp_863_:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v_mctx_879_; lean_object* v_zetaDeltaFVarIds_880_; lean_object* v_postponed_881_; lean_object* v_diag_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_894_; 
v___x_875_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1);
v___x_876_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_876_, 0, v___y_874_);
lean_ctor_set(v___x_876_, 1, v_nextMacroScope_865_);
lean_ctor_set(v___x_876_, 2, v_ngen_866_);
lean_ctor_set(v___x_876_, 3, v_auxDeclNGen_867_);
lean_ctor_set(v___x_876_, 4, v_traceState_868_);
lean_ctor_set(v___x_876_, 5, v___x_875_);
lean_ctor_set(v___x_876_, 6, v_recordedDeps_869_);
lean_ctor_set(v___x_876_, 7, v_messages_870_);
lean_ctor_set(v___x_876_, 8, v_infoState_871_);
lean_ctor_set(v___x_876_, 9, v_snapshotTasks_872_);
v___x_877_ = lean_st_ref_put(v___y_873_, v___x_876_);
v___x_878_ = lean_st_ref_take(v___y_864_);
v_mctx_879_ = lean_ctor_get(v___x_878_, 0);
v_zetaDeltaFVarIds_880_ = lean_ctor_get(v___x_878_, 2);
v_postponed_881_ = lean_ctor_get(v___x_878_, 3);
v_diag_882_ = lean_ctor_get(v___x_878_, 4);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v___x_878_, 1);
lean_dec(v_unused_895_);
v___x_884_ = v___x_878_;
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_diag_882_);
lean_inc(v_postponed_881_);
lean_inc(v_zetaDeltaFVarIds_880_);
lean_inc(v_mctx_879_);
lean_dec(v___x_878_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_894_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_886_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5);
if (v_isShared_885_ == 0)
{
lean_ctor_set(v___x_884_, 1, v___x_886_);
v___x_888_ = v___x_884_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_mctx_879_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_893_, 2, v_zetaDeltaFVarIds_880_);
lean_ctor_set(v_reuseFailAlloc_893_, 3, v_postponed_881_);
lean_ctor_set(v_reuseFailAlloc_893_, 4, v_diag_882_);
v___x_888_ = v_reuseFailAlloc_893_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; size_t v___x_890_; size_t v___x_891_; 
v___x_889_ = lean_st_ref_put(v___y_864_, v___x_888_);
v___x_890_ = ((size_t)1ULL);
v___x_891_ = lean_usize_add(v_i_851_, v___x_890_);
v_i_851_ = v___x_891_;
v_b_852_ = v___x_862_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___boxed(lean_object* v___x_949_, lean_object* v_as_950_, lean_object* v_sz_951_, lean_object* v_i_952_, lean_object* v_b_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
uint8_t v___x_3931__boxed_961_; size_t v_sz_boxed_962_; size_t v_i_boxed_963_; lean_object* v_res_964_; 
v___x_3931__boxed_961_ = lean_unbox(v___x_949_);
v_sz_boxed_962_ = lean_unbox_usize(v_sz_951_);
lean_dec(v_sz_951_);
v_i_boxed_963_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_res_964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(v___x_3931__boxed_961_, v_as_950_, v_sz_boxed_962_, v_i_boxed_963_, v_b_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec_ref(v_as_950_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(uint8_t v___x_965_, lean_object* v_ids_966_, size_t v_sz_967_, size_t v___x_968_, lean_object* v___x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(v___x_965_, v_ids_966_, v_sz_967_, v___x_968_, v___x_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_984_ == 0)
{
lean_object* v_unused_985_; 
v_unused_985_ = lean_ctor_get(v___x_977_, 0);
lean_dec(v_unused_985_);
v___x_979_ = v___x_977_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_dec(v___x_977_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
lean_ctor_set(v___x_979_, 0, v___x_969_);
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_969_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
else
{
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed(lean_object* v___x_986_, lean_object* v_ids_987_, lean_object* v_sz_988_, lean_object* v___x_989_, lean_object* v___x_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
uint8_t v___x_4084__boxed_998_; size_t v_sz_boxed_999_; size_t v___x_4085__boxed_1000_; lean_object* v_res_1001_; 
v___x_4084__boxed_998_ = lean_unbox(v___x_986_);
v_sz_boxed_999_ = lean_unbox_usize(v_sz_988_);
lean_dec(v_sz_988_);
v___x_4085__boxed_1000_ = lean_unbox_usize(v___x_989_);
lean_dec(v___x_989_);
v_res_1001_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(v___x_4084__boxed_998_, v_ids_987_, v_sz_boxed_999_, v___x_4085__boxed_1000_, v___x_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec_ref(v_ids_987_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(lean_object* v_stx_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1));
lean_inc(v_stx_1009_);
v___x_1014_ = l_Lean_Syntax_isOfKind(v_stx_1009_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
lean_dec(v_stx_1009_);
v___x_1015_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
return v___x_1015_;
}
else
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v_ids_1018_; lean_object* v___x_1019_; size_t v_sz_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; lean_object* v___x_1025_; 
v___x_1016_ = lean_unsigned_to_nat(2u);
v___x_1017_ = l_Lean_Syntax_getArg(v_stx_1009_, v___x_1016_);
lean_dec(v_stx_1009_);
v_ids_1018_ = l_Lean_Syntax_getArgs(v___x_1017_);
lean_dec(v___x_1017_);
v___x_1019_ = lean_box(0);
v_sz_1020_ = lean_array_size(v_ids_1018_);
v___x_1021_ = lean_box(v___x_1014_);
v___x_1022_ = lean_box_usize(v_sz_1020_);
v___x_1023_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1));
v___f_1024_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1024_, 0, v___x_1021_);
lean_closure_set(v___f_1024_, 1, v_ids_1018_);
lean_closure_set(v___f_1024_, 2, v___x_1022_);
lean_closure_set(v___f_1024_, 3, v___x_1023_);
lean_closure_set(v___f_1024_, 4, v___x_1019_);
v___x_1025_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1024_, v_a_1010_, v_a_1011_);
return v___x_1025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed(lean_object* v_stx_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(v_stx_1026_, v_a_1027_, v_a_1028_);
lean_dec(v_a_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1(){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1036_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1037_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1));
v___x_1038_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1));
v___x_1039_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed), 4, 0);
v___x_1040_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1036_, v___x_1037_, v___x_1038_, v___x_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___boxed(lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1();
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(lean_object* v_items_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig));
v___x_1067_ = l_Lean_Elab_Tactic_Grind_elabConfigItems___redArg(v___x_1066_, v_items_1061_, v_a_1062_, v_a_1063_, v_a_1064_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg___boxed(lean_object* v_items_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_items_1068_, v_a_1069_, v_a_1070_, v_a_1071_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec_ref(v_a_1069_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(lean_object* v_items_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_items_1074_, v_a_1075_, v_a_1079_, v_a_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___boxed(lean_object* v_items_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(v_items_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(lean_object* v_init_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
if (lean_obj_tag(v_x_1093_) == 0)
{
lean_object* v_k_1099_; lean_object* v_l_1100_; lean_object* v_r_1101_; lean_object* v___x_1102_; 
v_k_1099_ = lean_ctor_get(v_x_1093_, 1);
lean_inc(v_k_1099_);
v_l_1100_ = lean_ctor_get(v_x_1093_, 3);
lean_inc(v_l_1100_);
v_r_1101_ = lean_ctor_get(v_x_1093_, 4);
lean_inc(v_r_1101_);
lean_dec_ref_known(v_x_1093_, 5);
v___x_1102_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_init_1092_, v_l_1100_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v_a_1104_; lean_object* v___x_1105_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 1);
v_a_1104_ = lean_ctor_get(v_a_1103_, 0);
lean_inc_n(v_a_1104_, 2);
lean_dec(v_a_1103_);
v___x_1105_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_a_1104_, v_k_1099_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; 
lean_dec(v_a_1104_);
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_init_1092_ = v_a_1106_;
v_x_1093_ = v_r_1101_;
goto _start;
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1121_; 
v_a_1108_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1110_ = v___x_1105_;
v_isShared_1111_ = v_isSharedCheck_1121_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1105_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1121_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
uint8_t v___x_1112_; 
v___x_1112_ = l_Lean_Exception_isInterrupt(v_a_1108_);
if (v___x_1112_ == 0)
{
uint8_t v___x_1113_; 
lean_inc(v_a_1108_);
v___x_1113_ = l_Lean_Exception_isRuntime(v_a_1108_);
if (v___x_1113_ == 0)
{
lean_del_object(v___x_1110_);
lean_dec(v_a_1108_);
v_init_1092_ = v_a_1104_;
v_x_1093_ = v_r_1101_;
goto _start;
}
else
{
lean_object* v___x_1116_; 
lean_dec(v_a_1104_);
lean_dec(v_r_1101_);
if (v_isShared_1111_ == 0)
{
v___x_1116_ = v___x_1110_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1108_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
else
{
lean_object* v___x_1119_; 
lean_dec(v_a_1104_);
lean_dec(v_r_1101_);
if (v_isShared_1111_ == 0)
{
v___x_1119_ = v___x_1110_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1108_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
else
{
lean_dec(v_r_1101_);
lean_dec(v_k_1099_);
return v___x_1102_;
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1122_, 0, v_init_1092_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0___boxed(lean_object* v_init_1124_, lean_object* v_x_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_init_1124_, v_x_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec_ref(v___y_1128_);
lean_dec(v___y_1127_);
lean_dec_ref(v___y_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(lean_object* v_config_1132_, lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1139_ = lean_box(1);
v___x_1140_ = l_Lean_Meta_Grind_mkDefaultParams(v_config_1132_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1209_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1209_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1209_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_config_1145_; lean_object* v_identity_1146_; lean_object* v_extensions_1147_; lean_object* v_extra_1148_; lean_object* v_extraInj_1149_; lean_object* v_extraFacts_1150_; lean_object* v_symPrios_1151_; lean_object* v_norm_1152_; lean_object* v_normProcs_1153_; lean_object* v_anchorRefs_x3f_1154_; uint8_t v_interactive_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1208_; 
v_config_1145_ = lean_ctor_get(v_a_1141_, 0);
v_identity_1146_ = lean_ctor_get(v_a_1141_, 1);
v_extensions_1147_ = lean_ctor_get(v_a_1141_, 2);
v_extra_1148_ = lean_ctor_get(v_a_1141_, 3);
v_extraInj_1149_ = lean_ctor_get(v_a_1141_, 4);
v_extraFacts_1150_ = lean_ctor_get(v_a_1141_, 5);
v_symPrios_1151_ = lean_ctor_get(v_a_1141_, 6);
v_norm_1152_ = lean_ctor_get(v_a_1141_, 7);
v_normProcs_1153_ = lean_ctor_get(v_a_1141_, 8);
v_anchorRefs_x3f_1154_ = lean_ctor_get(v_a_1141_, 9);
v_interactive_1155_ = lean_ctor_get_uint8(v_a_1141_, sizeof(void*)*10);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_a_1141_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1157_ = v_a_1141_;
v_isShared_1158_ = v_isSharedCheck_1208_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_anchorRefs_x3f_1154_);
lean_inc(v_normProcs_1153_);
lean_inc(v_norm_1152_);
lean_inc(v_symPrios_1151_);
lean_inc(v_extraFacts_1150_);
lean_inc(v_extraInj_1149_);
lean_inc(v_extra_1148_);
lean_inc(v_extensions_1147_);
lean_inc(v_identity_1146_);
lean_inc(v_config_1145_);
lean_dec(v_a_1141_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1208_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___y_1160_; lean_object* v___x_1167_; lean_object* v_a_1169_; lean_object* v___x_1188_; lean_object* v_ematch_1189_; lean_object* v___x_1190_; lean_object* v_env_1191_; lean_object* v___x_1192_; lean_object* v_toEnvExtension_1193_; lean_object* v_asyncMode_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_array_get_borrowed(v___x_1138_, v_extensions_1147_, v___x_1167_);
v_ematch_1189_ = lean_ctor_get(v___x_1188_, 3);
v___x_1190_ = lean_st_ref_get(v_a_1136_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc_ref(v_env_1191_);
lean_dec(v___x_1190_);
v___x_1192_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_1193_ = lean_ctor_get(v___x_1192_, 0);
v_asyncMode_1194_ = lean_ctor_get(v_toEnvExtension_1193_, 2);
v___x_1195_ = lean_box(0);
v___x_1196_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1139_, v___x_1192_, v_env_1191_, v_asyncMode_1194_, v___x_1195_);
lean_inc_ref(v_ematch_1189_);
v___x_1197_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_ematch_1189_, v___x_1196_, v_a_1133_, v_a_1134_, v_a_1135_, v_a_1136_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v_a_1199_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref_known(v___x_1197_, 1);
v_a_1199_ = lean_ctor_get(v_a_1198_, 0);
lean_inc(v_a_1199_);
lean_dec(v_a_1198_);
v_a_1169_ = v_a_1199_;
goto v___jp_1168_;
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_del_object(v___x_1157_);
lean_dec(v_anchorRefs_x3f_1154_);
lean_dec_ref(v_normProcs_1153_);
lean_dec_ref(v_norm_1152_);
lean_dec_ref(v_symPrios_1151_);
lean_dec_ref(v_extraFacts_1150_);
lean_dec_ref(v_extraInj_1149_);
lean_dec_ref(v_extra_1148_);
lean_dec_ref(v_extensions_1147_);
lean_dec(v_identity_1146_);
lean_dec_ref(v_config_1145_);
lean_del_object(v___x_1143_);
v_a_1200_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1197_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1197_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
v___jp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 2, v___y_1160_);
v___x_1162_ = v___x_1157_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_config_1145_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_identity_1146_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v___y_1160_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_extra_1148_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_extraInj_1149_);
lean_ctor_set(v_reuseFailAlloc_1166_, 5, v_extraFacts_1150_);
lean_ctor_set(v_reuseFailAlloc_1166_, 6, v_symPrios_1151_);
lean_ctor_set(v_reuseFailAlloc_1166_, 7, v_norm_1152_);
lean_ctor_set(v_reuseFailAlloc_1166_, 8, v_normProcs_1153_);
lean_ctor_set(v_reuseFailAlloc_1166_, 9, v_anchorRefs_x3f_1154_);
lean_ctor_set_uint8(v_reuseFailAlloc_1166_, sizeof(void*)*10, v_interactive_1155_);
v___x_1162_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1162_);
v___x_1164_ = v___x_1143_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1162_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
v___jp_1168_:
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_array_get_size(v_extensions_1147_);
v___x_1171_ = lean_nat_dec_lt(v___x_1167_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_dec_ref(v_a_1169_);
v___y_1160_ = v_extensions_1147_;
goto v___jp_1159_;
}
else
{
lean_object* v_v_1172_; lean_object* v_casesTypes_1173_; lean_object* v_extThms_1174_; lean_object* v_funCC_1175_; lean_object* v_inj_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1186_; 
v_v_1172_ = lean_array_fget(v_extensions_1147_, v___x_1167_);
v_casesTypes_1173_ = lean_ctor_get(v_v_1172_, 0);
v_extThms_1174_ = lean_ctor_get(v_v_1172_, 1);
v_funCC_1175_ = lean_ctor_get(v_v_1172_, 2);
v_inj_1176_ = lean_ctor_get(v_v_1172_, 4);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_v_1172_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; 
v_unused_1187_ = lean_ctor_get(v_v_1172_, 3);
lean_dec(v_unused_1187_);
v___x_1178_ = v_v_1172_;
v_isShared_1179_ = v_isSharedCheck_1186_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_inj_1176_);
lean_inc(v_funCC_1175_);
lean_inc(v_extThms_1174_);
lean_inc(v_casesTypes_1173_);
lean_dec(v_v_1172_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1186_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v_xs_x27_1181_; lean_object* v___x_1183_; 
v___x_1180_ = lean_box(0);
v_xs_x27_1181_ = lean_array_fset(v_extensions_1147_, v___x_1167_, v___x_1180_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 3, v_a_1169_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_casesTypes_1173_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_extThms_1174_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_funCC_1175_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_a_1169_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v_inj_1176_);
v___x_1183_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
lean_object* v___x_1184_; 
v___x_1184_ = lean_array_fset(v_xs_x27_1181_, v___x_1167_, v___x_1183_);
v___y_1160_ = v___x_1184_;
goto v___jp_1159_;
}
}
}
}
}
}
}
else
{
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams___boxed(lean_object* v_config_1210_, lean_object* v_a_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_config_1210_, v_a_1211_, v_a_1212_, v_a_1213_, v_a_1214_);
lean_dec(v_a_1214_);
lean_dec_ref(v_a_1213_);
lean_dec(v_a_1212_);
lean_dec_ref(v_a_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(lean_object* v_x_1217_, lean_object* v_____s_1218_){
_start:
{
lean_object* v_snd_1219_; lean_object* v_r_1220_; lean_object* v___x_1221_; 
v_snd_1219_ = lean_ctor_get(v_x_1217_, 1);
v_r_1220_ = lean_nat_add(v_____s_1218_, v_snd_1219_);
v___x_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1221_, 0, v_r_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0___boxed(lean_object* v_x_1222_, lean_object* v_____s_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(v_x_1222_, v_____s_1223_);
lean_dec(v_____s_1223_);
lean_dec_ref(v_x_1222_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0(lean_object* v_f_1225_, lean_object* v_s_1226_, lean_object* v_a_1227_, lean_object* v_b_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_a_1227_);
lean_ctor_set(v___x_1229_, 1, v_b_1228_);
v___x_1230_ = lean_apply_2(v_f_1225_, v___x_1229_, v_s_1226_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
v_a_1231_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1230_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1230_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
v_a_1239_ = lean_ctor_get(v___x_1230_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1230_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1230_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1247_, lean_object* v_keys_1248_, lean_object* v_vals_1249_, lean_object* v_i_1250_, lean_object* v_acc_1251_){
_start:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
v___x_1252_ = lean_array_get_size(v_keys_1248_);
v___x_1253_ = lean_nat_dec_lt(v_i_1250_, v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; 
lean_dec(v_i_1250_);
lean_dec_ref(v_f_1247_);
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v_acc_1251_);
return v___x_1254_;
}
else
{
lean_object* v_k_1255_; lean_object* v_v_1256_; lean_object* v___x_1257_; 
v_k_1255_ = lean_array_fget_borrowed(v_keys_1248_, v_i_1250_);
v_v_1256_ = lean_array_fget_borrowed(v_vals_1249_, v_i_1250_);
lean_inc_ref(v_f_1247_);
lean_inc(v_v_1256_);
lean_inc(v_k_1255_);
v___x_1257_ = lean_apply_3(v_f_1247_, v_acc_1251_, v_k_1255_, v_v_1256_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_dec(v_i_1250_);
lean_dec_ref(v_f_1247_);
return v___x_1257_;
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___x_1257_, 1);
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = lean_nat_add(v_i_1250_, v___x_1259_);
lean_dec(v_i_1250_);
v_i_1250_ = v___x_1260_;
v_acc_1251_ = v_a_1258_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1262_, lean_object* v_keys_1263_, lean_object* v_vals_1264_, lean_object* v_i_1265_, lean_object* v_acc_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1262_, v_keys_1263_, v_vals_1264_, v_i_1265_, v_acc_1266_);
lean_dec_ref(v_vals_1264_);
lean_dec_ref(v_keys_1263_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1268_, lean_object* v_as_1269_, size_t v_i_1270_, size_t v_stop_1271_, lean_object* v_b_1272_){
_start:
{
lean_object* v_a_1274_; lean_object* v___y_1279_; uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_eq(v_i_1270_, v_stop_1271_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_array_uget_borrowed(v_as_1269_, v_i_1270_);
switch(lean_obj_tag(v___x_1282_))
{
case 0:
{
lean_object* v_key_1283_; lean_object* v_val_1284_; lean_object* v___x_1285_; 
v_key_1283_ = lean_ctor_get(v___x_1282_, 0);
v_val_1284_ = lean_ctor_get(v___x_1282_, 1);
lean_inc_ref(v_f_1268_);
lean_inc(v_val_1284_);
lean_inc(v_key_1283_);
v___x_1285_ = lean_apply_3(v_f_1268_, v_b_1272_, v_key_1283_, v_val_1284_);
v___y_1279_ = v___x_1285_;
goto v___jp_1278_;
}
case 1:
{
lean_object* v_node_1286_; lean_object* v___x_1287_; 
v_node_1286_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_node_1286_);
lean_inc_ref(v_f_1268_);
v___x_1287_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1268_, v_node_1286_, v_b_1272_);
v___y_1279_ = v___x_1287_;
goto v___jp_1278_;
}
default: 
{
v_a_1274_ = v_b_1272_;
goto v___jp_1273_;
}
}
}
else
{
lean_object* v___x_1288_; 
lean_dec_ref(v_f_1268_);
v___x_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1288_, 0, v_b_1272_);
return v___x_1288_;
}
v___jp_1273_:
{
size_t v___x_1275_; size_t v___x_1276_; 
v___x_1275_ = ((size_t)1ULL);
v___x_1276_ = lean_usize_add(v_i_1270_, v___x_1275_);
v_i_1270_ = v___x_1276_;
v_b_1272_ = v_a_1274_;
goto _start;
}
v___jp_1278_:
{
if (lean_obj_tag(v___y_1279_) == 0)
{
lean_dec_ref(v_f_1268_);
return v___y_1279_;
}
else
{
lean_object* v_a_1280_; 
v_a_1280_ = lean_ctor_get(v___y_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___y_1279_, 1);
v_a_1274_ = v_a_1280_;
goto v___jp_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
if (lean_obj_tag(v_x_1290_) == 0)
{
lean_object* v_es_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1305_; 
v_es_1292_ = lean_ctor_get(v_x_1290_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_x_1290_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1294_ = v_x_1290_;
v_isShared_1295_ = v_isSharedCheck_1305_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_es_1292_);
lean_dec(v_x_1290_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1305_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1296_ = lean_unsigned_to_nat(0u);
v___x_1297_ = lean_array_get_size(v_es_1292_);
v___x_1298_ = lean_nat_dec_lt(v___x_1296_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1300_; 
lean_dec_ref(v_es_1292_);
lean_dec_ref(v_f_1289_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set_tag(v___x_1294_, 1);
lean_ctor_set(v___x_1294_, 0, v_x_1291_);
v___x_1300_ = v___x_1294_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_x_1291_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
else
{
size_t v___x_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
lean_del_object(v___x_1294_);
v___x_1302_ = ((size_t)0ULL);
v___x_1303_ = lean_usize_of_nat(v___x_1297_);
v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1289_, v_es_1292_, v___x_1302_, v___x_1303_, v_x_1291_);
lean_dec_ref(v_es_1292_);
return v___x_1304_;
}
}
}
else
{
lean_object* v_ks_1306_; lean_object* v_vs_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; 
v_ks_1306_ = lean_ctor_get(v_x_1290_, 0);
lean_inc_ref(v_ks_1306_);
v_vs_1307_ = lean_ctor_get(v_x_1290_, 1);
lean_inc_ref(v_vs_1307_);
lean_dec_ref_known(v_x_1290_, 2);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1289_, v_ks_1306_, v_vs_1307_, v___x_1308_, v_x_1291_);
lean_dec_ref(v_vs_1307_);
lean_dec_ref(v_ks_1306_);
return v___x_1309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1310_, lean_object* v_as_1311_, lean_object* v_i_1312_, lean_object* v_stop_1313_, lean_object* v_b_1314_){
_start:
{
size_t v_i_boxed_1315_; size_t v_stop_boxed_1316_; lean_object* v_res_1317_; 
v_i_boxed_1315_ = lean_unbox_usize(v_i_1312_);
lean_dec(v_i_1312_);
v_stop_boxed_1316_ = lean_unbox_usize(v_stop_1313_);
lean_dec(v_stop_1313_);
v_res_1317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1310_, v_as_1311_, v_i_boxed_1315_, v_stop_boxed_1316_, v_b_1314_);
lean_dec_ref(v_as_1311_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(lean_object* v_map_1318_, lean_object* v_init_1319_, lean_object* v_f_1320_){
_start:
{
lean_object* v___f_1321_; lean_object* v___x_1322_; lean_object* v_a_1323_; 
v___f_1321_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1321_, 0, v_f_1320_);
lean_inc_ref(v_map_1318_);
v___x_1322_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v___f_1321_, v_map_1318_, v_init_1319_);
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref(v___x_1322_);
return v_a_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___boxed(lean_object* v_map_1324_, lean_object* v_init_1325_, lean_object* v_f_1326_){
_start:
{
lean_object* v_res_1327_; 
v_res_1327_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_map_1324_, v_init_1325_, v_f_1326_);
lean_dec_ref(v_map_1324_);
return v_res_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(lean_object* v_cs_1329_){
_start:
{
lean_object* v___f_1330_; lean_object* v_r_1331_; lean_object* v___x_1332_; 
v___f_1330_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0));
v_r_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_cs_1329_, v_r_1331_, v___f_1330_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___boxed(lean_object* v_cs_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(v_cs_1333_);
lean_dec_ref(v_cs_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(lean_object* v_00_u03c3_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_map_1337_, lean_object* v_init_1338_, lean_object* v_f_1339_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_map_1337_, v_init_1338_, v_f_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___boxed(lean_object* v_00_u03c3_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_map_1343_, lean_object* v_init_1344_, lean_object* v_f_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(v_00_u03c3_1341_, v_00_u03b2_1342_, v_map_1343_, v_init_1344_, v_f_1345_);
lean_dec_ref(v_map_1343_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0___redArg(lean_object* v_map_1347_, lean_object* v_f_1348_, lean_object* v_init_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1348_, v_map_1347_, v_init_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0(lean_object* v_00_u03c3_1351_, lean_object* v_00_u03c3_1352_, lean_object* v_00_u03b2_1353_, lean_object* v_map_1354_, lean_object* v_f_1355_, lean_object* v_init_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1355_, v_map_1354_, v_init_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1358_, lean_object* v_00_u03c3_1359_, lean_object* v_00_u03b1_1360_, lean_object* v_00_u03b2_1361_, lean_object* v_f_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
lean_object* v___x_1365_; 
v___x_1365_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1362_, v_x_1363_, v_x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1366_, lean_object* v_00_u03b2_1367_, lean_object* v_00_u03c3_1368_, lean_object* v_00_u03c3_1369_, lean_object* v_f_1370_, lean_object* v_as_1371_, size_t v_i_1372_, size_t v_stop_1373_, lean_object* v_b_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1370_, v_as_1371_, v_i_1372_, v_stop_1373_, v_b_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1376_, lean_object* v_00_u03b2_1377_, lean_object* v_00_u03c3_1378_, lean_object* v_00_u03c3_1379_, lean_object* v_f_1380_, lean_object* v_as_1381_, lean_object* v_i_1382_, lean_object* v_stop_1383_, lean_object* v_b_1384_){
_start:
{
size_t v_i_boxed_1385_; size_t v_stop_boxed_1386_; lean_object* v_res_1387_; 
v_i_boxed_1385_ = lean_unbox_usize(v_i_1382_);
lean_dec(v_i_1382_);
v_stop_boxed_1386_ = lean_unbox_usize(v_stop_1383_);
lean_dec(v_stop_1383_);
v_res_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1376_, v_00_u03b2_1377_, v_00_u03c3_1378_, v_00_u03c3_1379_, v_f_1380_, v_as_1381_, v_i_boxed_1385_, v_stop_boxed_1386_, v_b_1384_);
lean_dec_ref(v_as_1381_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_1388_, lean_object* v_00_u03c3_1389_, lean_object* v_00_u03b1_1390_, lean_object* v_00_u03b2_1391_, lean_object* v_f_1392_, lean_object* v_keys_1393_, lean_object* v_vals_1394_, lean_object* v_heq_1395_, lean_object* v_i_1396_, lean_object* v_acc_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1392_, v_keys_1393_, v_vals_1394_, v_i_1396_, v_acc_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1399_, lean_object* v_00_u03c3_1400_, lean_object* v_00_u03b1_1401_, lean_object* v_00_u03b2_1402_, lean_object* v_f_1403_, lean_object* v_keys_1404_, lean_object* v_vals_1405_, lean_object* v_heq_1406_, lean_object* v_i_1407_, lean_object* v_acc_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_1399_, v_00_u03c3_1400_, v_00_u03b1_1401_, v_00_u03b2_1402_, v_f_1403_, v_keys_1404_, v_vals_1405_, v_heq_1406_, v_i_1407_, v_acc_1408_);
lean_dec_ref(v_vals_1405_);
lean_dec_ref(v_keys_1404_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(lean_object* v_as_1410_, size_t v_i_1411_, size_t v_stop_1412_, lean_object* v_b_1413_){
_start:
{
lean_object* v___y_1415_; uint8_t v___x_1419_; 
v___x_1419_ = lean_usize_dec_eq(v_i_1411_, v_stop_1412_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; lean_object* v_fst_1421_; 
v___x_1420_ = lean_array_uget(v_as_1410_, v_i_1411_);
v_fst_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_fst_1421_);
if (lean_obj_tag(v_fst_1421_) == 0)
{
lean_object* v_snd_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1431_; 
v_snd_1422_ = lean_ctor_get(v___x_1420_, 1);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1420_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; 
v_unused_1432_ = lean_ctor_get(v___x_1420_, 0);
lean_dec(v_unused_1432_);
v___x_1424_ = v___x_1420_;
v_isShared_1425_ = v_isSharedCheck_1431_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_snd_1422_);
lean_dec(v___x_1420_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1431_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v_declName_1426_; lean_object* v___x_1428_; 
v_declName_1426_ = lean_ctor_get(v_fst_1421_, 0);
lean_inc(v_declName_1426_);
lean_dec_ref_known(v_fst_1421_, 1);
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 0, v_declName_1426_);
v___x_1428_ = v___x_1424_;
goto v_reusejp_1427_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_declName_1426_);
lean_ctor_set(v_reuseFailAlloc_1430_, 1, v_snd_1422_);
v___x_1428_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1427_;
}
v_reusejp_1427_:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_array_push(v_b_1413_, v___x_1428_);
v___y_1415_ = v___x_1429_;
goto v___jp_1414_;
}
}
}
else
{
lean_dec(v_fst_1421_);
lean_dec(v___x_1420_);
v___y_1415_ = v_b_1413_;
goto v___jp_1414_;
}
}
else
{
return v_b_1413_;
}
v___jp_1414_:
{
size_t v___x_1416_; size_t v___x_1417_; 
v___x_1416_ = ((size_t)1ULL);
v___x_1417_ = lean_usize_add(v_i_1411_, v___x_1416_);
v_i_1411_ = v___x_1417_;
v_b_1413_ = v___y_1415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6___boxed(lean_object* v_as_1433_, lean_object* v_i_1434_, lean_object* v_stop_1435_, lean_object* v_b_1436_){
_start:
{
size_t v_i_boxed_1437_; size_t v_stop_boxed_1438_; lean_object* v_res_1439_; 
v_i_boxed_1437_ = lean_unbox_usize(v_i_1434_);
lean_dec(v_i_1434_);
v_stop_boxed_1438_ = lean_unbox_usize(v_stop_1435_);
lean_dec(v_stop_1435_);
v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1433_, v_i_boxed_1437_, v_stop_boxed_1438_, v_b_1436_);
lean_dec_ref(v_as_1433_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(lean_object* v_as_1442_, lean_object* v_start_1443_, lean_object* v_stop_1444_){
_start:
{
lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1445_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0));
v___x_1446_ = lean_nat_dec_lt(v_start_1443_, v_stop_1444_);
if (v___x_1446_ == 0)
{
return v___x_1445_;
}
else
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_array_get_size(v_as_1442_);
v___x_1448_ = lean_nat_dec_le(v_stop_1444_, v___x_1447_);
if (v___x_1448_ == 0)
{
uint8_t v___x_1449_; 
v___x_1449_ = lean_nat_dec_lt(v_start_1443_, v___x_1447_);
if (v___x_1449_ == 0)
{
return v___x_1445_;
}
else
{
size_t v___x_1450_; size_t v___x_1451_; lean_object* v___x_1452_; 
v___x_1450_ = lean_usize_of_nat(v_start_1443_);
v___x_1451_ = lean_usize_of_nat(v___x_1447_);
v___x_1452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1442_, v___x_1450_, v___x_1451_, v___x_1445_);
return v___x_1452_;
}
}
else
{
size_t v___x_1453_; size_t v___x_1454_; lean_object* v___x_1455_; 
v___x_1453_ = lean_usize_of_nat(v_start_1443_);
v___x_1454_ = lean_usize_of_nat(v_stop_1444_);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1442_, v___x_1453_, v___x_1454_, v___x_1445_);
return v___x_1455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___boxed(lean_object* v_as_1456_, lean_object* v_start_1457_, lean_object* v_stop_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(v_as_1456_, v_start_1457_, v_stop_1458_);
lean_dec(v_stop_1458_);
lean_dec(v_start_1457_);
lean_dec_ref(v_as_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(lean_object* v_x_1460_, lean_object* v_x_1461_){
_start:
{
lean_object* v_fst_1462_; lean_object* v_snd_1463_; lean_object* v_fst_1464_; lean_object* v_snd_1465_; uint8_t v___x_1466_; 
v_fst_1462_ = lean_ctor_get(v_x_1460_, 0);
v_snd_1463_ = lean_ctor_get(v_x_1460_, 1);
v_fst_1464_ = lean_ctor_get(v_x_1461_, 0);
v_snd_1465_ = lean_ctor_get(v_x_1461_, 1);
v___x_1466_ = lean_nat_dec_eq(v_snd_1463_, v_snd_1465_);
if (v___x_1466_ == 0)
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_nat_dec_lt(v_snd_1465_, v_snd_1463_);
return v___x_1467_;
}
else
{
uint8_t v___x_1468_; 
v___x_1468_ = l_Lean_Name_lt(v_fst_1462_, v_fst_1464_);
return v___x_1468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0___boxed(lean_object* v_x_1469_, lean_object* v_x_1470_){
_start:
{
uint8_t v_res_1471_; lean_object* v_r_1472_; 
v_res_1471_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v_x_1469_, v_x_1470_);
lean_dec_ref(v_x_1470_);
lean_dec_ref(v_x_1469_);
v_r_1472_ = lean_box(v_res_1471_);
return v_r_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(lean_object* v_hi_1473_, lean_object* v_pivot_1474_, lean_object* v_as_1475_, lean_object* v_i_1476_, lean_object* v_k_1477_){
_start:
{
uint8_t v___y_1479_; uint8_t v___x_1488_; 
v___x_1488_ = lean_nat_dec_lt(v_k_1477_, v_hi_1473_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
lean_dec(v_k_1477_);
v___x_1489_ = lean_array_fswap(v_as_1475_, v_i_1476_, v_hi_1473_);
v___x_1490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1490_, 0, v_i_1476_);
lean_ctor_set(v___x_1490_, 1, v___x_1489_);
return v___x_1490_;
}
else
{
lean_object* v___x_1491_; lean_object* v_fst_1492_; lean_object* v_snd_1493_; lean_object* v_fst_1494_; lean_object* v_snd_1495_; uint8_t v___x_1496_; 
v___x_1491_ = lean_array_fget_borrowed(v_as_1475_, v_k_1477_);
v_fst_1492_ = lean_ctor_get(v___x_1491_, 0);
v_snd_1493_ = lean_ctor_get(v___x_1491_, 1);
v_fst_1494_ = lean_ctor_get(v_pivot_1474_, 0);
v_snd_1495_ = lean_ctor_get(v_pivot_1474_, 1);
v___x_1496_ = lean_nat_dec_eq(v_snd_1493_, v_snd_1495_);
if (v___x_1496_ == 0)
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_nat_dec_lt(v_snd_1495_, v_snd_1493_);
v___y_1479_ = v___x_1497_;
goto v___jp_1478_;
}
else
{
uint8_t v___x_1498_; 
v___x_1498_ = l_Lean_Name_lt(v_fst_1492_, v_fst_1494_);
v___y_1479_ = v___x_1498_;
goto v___jp_1478_;
}
}
v___jp_1478_:
{
if (v___y_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = lean_unsigned_to_nat(1u);
v___x_1481_ = lean_nat_add(v_k_1477_, v___x_1480_);
lean_dec(v_k_1477_);
v_k_1477_ = v___x_1481_;
goto _start;
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1483_ = lean_array_fswap(v_as_1475_, v_i_1476_, v_k_1477_);
v___x_1484_ = lean_unsigned_to_nat(1u);
v___x_1485_ = lean_nat_add(v_i_1476_, v___x_1484_);
lean_dec(v_i_1476_);
v___x_1486_ = lean_nat_add(v_k_1477_, v___x_1484_);
lean_dec(v_k_1477_);
v_as_1475_ = v___x_1483_;
v_i_1476_ = v___x_1485_;
v_k_1477_ = v___x_1486_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg___boxed(lean_object* v_hi_1499_, lean_object* v_pivot_1500_, lean_object* v_as_1501_, lean_object* v_i_1502_, lean_object* v_k_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_1499_, v_pivot_1500_, v_as_1501_, v_i_1502_, v_k_1503_);
lean_dec_ref(v_pivot_1500_);
lean_dec(v_hi_1499_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(lean_object* v_n_1505_, lean_object* v_as_1506_, lean_object* v_lo_1507_, lean_object* v_hi_1508_){
_start:
{
lean_object* v___y_1510_; uint8_t v___x_1520_; 
v___x_1520_ = lean_nat_dec_lt(v_lo_1507_, v_hi_1508_);
if (v___x_1520_ == 0)
{
lean_dec(v_lo_1507_);
return v_as_1506_;
}
else
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v_mid_1523_; lean_object* v___y_1525_; lean_object* v___y_1531_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1521_ = lean_nat_add(v_lo_1507_, v_hi_1508_);
v___x_1522_ = lean_unsigned_to_nat(1u);
v_mid_1523_ = lean_nat_shiftr(v___x_1521_, v___x_1522_);
lean_dec(v___x_1521_);
v___x_1536_ = lean_array_fget_borrowed(v_as_1506_, v_mid_1523_);
v___x_1537_ = lean_array_fget_borrowed(v_as_1506_, v_lo_1507_);
v___x_1538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
v___y_1531_ = v_as_1506_;
goto v___jp_1530_;
}
else
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_array_fswap(v_as_1506_, v_lo_1507_, v_mid_1523_);
v___y_1531_ = v___x_1539_;
goto v___jp_1530_;
}
v___jp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1526_ = lean_array_fget_borrowed(v___y_1525_, v_mid_1523_);
v___x_1527_ = lean_array_fget_borrowed(v___y_1525_, v_hi_1508_);
v___x_1528_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_dec(v_mid_1523_);
v___y_1510_ = v___y_1525_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1529_; 
v___x_1529_ = lean_array_fswap(v___y_1525_, v_mid_1523_, v_hi_1508_);
lean_dec(v_mid_1523_);
v___y_1510_ = v___x_1529_;
goto v___jp_1509_;
}
}
v___jp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1532_ = lean_array_fget_borrowed(v___y_1531_, v_hi_1508_);
v___x_1533_ = lean_array_fget_borrowed(v___y_1531_, v_lo_1507_);
v___x_1534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
v___y_1525_ = v___y_1531_;
goto v___jp_1524_;
}
else
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_array_fswap(v___y_1531_, v_lo_1507_, v_hi_1508_);
v___y_1525_ = v___x_1535_;
goto v___jp_1524_;
}
}
}
v___jp_1509_:
{
lean_object* v_pivot_1511_; lean_object* v___x_1512_; lean_object* v_fst_1513_; lean_object* v_snd_1514_; uint8_t v___x_1515_; 
v_pivot_1511_ = lean_array_fget(v___y_1510_, v_hi_1508_);
lean_inc_n(v_lo_1507_, 2);
v___x_1512_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_1508_, v_pivot_1511_, v___y_1510_, v_lo_1507_, v_lo_1507_);
lean_dec(v_pivot_1511_);
v_fst_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_fst_1513_);
v_snd_1514_ = lean_ctor_get(v___x_1512_, 1);
lean_inc(v_snd_1514_);
lean_dec_ref(v___x_1512_);
v___x_1515_ = lean_nat_dec_le(v_hi_1508_, v_fst_1513_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_1505_, v_snd_1514_, v_lo_1507_, v_fst_1513_);
v___x_1517_ = lean_unsigned_to_nat(1u);
v___x_1518_ = lean_nat_add(v_fst_1513_, v___x_1517_);
lean_dec(v_fst_1513_);
v_as_1506_ = v___x_1516_;
v_lo_1507_ = v___x_1518_;
goto _start;
}
else
{
lean_dec(v_fst_1513_);
lean_dec(v_lo_1507_);
return v_snd_1514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___boxed(lean_object* v_n_1540_, lean_object* v_as_1541_, lean_object* v_lo_1542_, lean_object* v_hi_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_1540_, v_as_1541_, v_lo_1542_, v_hi_1543_);
lean_dec(v_hi_1543_);
lean_dec(v_n_1540_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___lam__0(lean_object* v_ps_1545_, lean_object* v_k_1546_, lean_object* v_v_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1548_, 0, v_k_1546_);
lean_ctor_set(v___x_1548_, 1, v_v_1547_);
v___x_1549_ = lean_array_push(v_ps_1545_, v___x_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0(lean_object* v_f_1550_, lean_object* v_x1_1551_, lean_object* v_x2_1552_, lean_object* v_x3_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_apply_3(v_f_1550_, v_x1_1551_, v_x2_1552_, v_x3_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(lean_object* v_f_1555_, lean_object* v_keys_1556_, lean_object* v_vals_1557_, lean_object* v_i_1558_, lean_object* v_acc_1559_){
_start:
{
lean_object* v___x_1560_; uint8_t v___x_1561_; 
v___x_1560_ = lean_array_get_size(v_keys_1556_);
v___x_1561_ = lean_nat_dec_lt(v_i_1558_, v___x_1560_);
if (v___x_1561_ == 0)
{
lean_dec(v_i_1558_);
lean_dec(v_f_1555_);
return v_acc_1559_;
}
else
{
lean_object* v_k_1562_; lean_object* v_v_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v_k_1562_ = lean_array_fget_borrowed(v_keys_1556_, v_i_1558_);
v_v_1563_ = lean_array_fget_borrowed(v_vals_1557_, v_i_1558_);
lean_inc(v_f_1555_);
lean_inc(v_v_1563_);
lean_inc(v_k_1562_);
v___x_1564_ = lean_apply_3(v_f_1555_, v_acc_1559_, v_k_1562_, v_v_1563_);
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = lean_nat_add(v_i_1558_, v___x_1565_);
lean_dec(v_i_1558_);
v_i_1558_ = v___x_1566_;
v_acc_1559_ = v___x_1564_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_f_1568_, lean_object* v_keys_1569_, lean_object* v_vals_1570_, lean_object* v_i_1571_, lean_object* v_acc_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_1568_, v_keys_1569_, v_vals_1570_, v_i_1571_, v_acc_1572_);
lean_dec_ref(v_vals_1570_);
lean_dec_ref(v_keys_1569_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(lean_object* v_f_1574_, lean_object* v_as_1575_, size_t v_i_1576_, size_t v_stop_1577_, lean_object* v_b_1578_){
_start:
{
lean_object* v___y_1580_; uint8_t v___x_1584_; 
v___x_1584_ = lean_usize_dec_eq(v_i_1576_, v_stop_1577_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = lean_array_uget_borrowed(v_as_1575_, v_i_1576_);
switch(lean_obj_tag(v___x_1585_))
{
case 0:
{
lean_object* v_key_1586_; lean_object* v_val_1587_; lean_object* v___x_1588_; 
v_key_1586_ = lean_ctor_get(v___x_1585_, 0);
v_val_1587_ = lean_ctor_get(v___x_1585_, 1);
lean_inc(v_f_1574_);
lean_inc(v_val_1587_);
lean_inc(v_key_1586_);
v___x_1588_ = lean_apply_3(v_f_1574_, v_b_1578_, v_key_1586_, v_val_1587_);
v___y_1580_ = v___x_1588_;
goto v___jp_1579_;
}
case 1:
{
lean_object* v_node_1589_; lean_object* v___x_1590_; 
v_node_1589_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_f_1574_);
v___x_1590_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_1574_, v_node_1589_, v_b_1578_);
v___y_1580_ = v___x_1590_;
goto v___jp_1579_;
}
default: 
{
v___y_1580_ = v_b_1578_;
goto v___jp_1579_;
}
}
}
else
{
lean_dec(v_f_1574_);
return v_b_1578_;
}
v___jp_1579_:
{
size_t v___x_1581_; size_t v___x_1582_; 
v___x_1581_ = ((size_t)1ULL);
v___x_1582_ = lean_usize_add(v_i_1576_, v___x_1581_);
v_i_1576_ = v___x_1582_;
v_b_1578_ = v___y_1580_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_f_1591_, lean_object* v_x_1592_, lean_object* v_x_1593_){
_start:
{
if (lean_obj_tag(v_x_1592_) == 0)
{
lean_object* v_es_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_es_1594_ = lean_ctor_get(v_x_1592_, 0);
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = lean_array_get_size(v_es_1594_);
v___x_1597_ = lean_nat_dec_lt(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec(v_f_1591_);
return v_x_1593_;
}
else
{
size_t v___x_1598_; size_t v___x_1599_; lean_object* v___x_1600_; 
v___x_1598_ = ((size_t)0ULL);
v___x_1599_ = lean_usize_of_nat(v___x_1596_);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_1591_, v_es_1594_, v___x_1598_, v___x_1599_, v_x_1593_);
return v___x_1600_;
}
}
else
{
lean_object* v_ks_1601_; lean_object* v_vs_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v_ks_1601_ = lean_ctor_get(v_x_1592_, 0);
v_vs_1602_ = lean_ctor_get(v_x_1592_, 1);
v___x_1603_ = lean_unsigned_to_nat(0u);
v___x_1604_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_1591_, v_ks_1601_, v_vs_1602_, v___x_1603_, v_x_1593_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_f_1605_, lean_object* v_x_1606_, lean_object* v_x_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_1605_, v_x_1606_, v_x_1607_);
lean_dec_ref(v_x_1606_);
return v_res_1608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg___boxed(lean_object* v_f_1609_, lean_object* v_as_1610_, lean_object* v_i_1611_, lean_object* v_stop_1612_, lean_object* v_b_1613_){
_start:
{
size_t v_i_boxed_1614_; size_t v_stop_boxed_1615_; lean_object* v_res_1616_; 
v_i_boxed_1614_ = lean_unbox_usize(v_i_1611_);
lean_dec(v_i_1611_);
v_stop_boxed_1615_ = lean_unbox_usize(v_stop_1612_);
lean_dec(v_stop_1612_);
v_res_1616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_1609_, v_as_1610_, v_i_boxed_1614_, v_stop_boxed_1615_, v_b_1613_);
lean_dec_ref(v_as_1610_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(lean_object* v_map_1617_, lean_object* v_f_1618_, lean_object* v_init_1619_){
_start:
{
lean_object* v___f_1620_; lean_object* v___x_1621_; 
v___f_1620_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1620_, 0, v_f_1618_);
v___x_1621_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v___f_1620_, v_map_1617_, v_init_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___boxed(lean_object* v_map_1622_, lean_object* v_f_1623_, lean_object* v_init_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_map_1622_, v_f_1623_, v_init_1624_);
lean_dec_ref(v_map_1622_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(lean_object* v_m_1629_){
_start:
{
lean_object* v___f_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___f_1630_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0));
v___x_1631_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1));
v___x_1632_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_m_1629_, v___f_1630_, v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___boxed(lean_object* v_m_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_m_1633_);
lean_dec_ref(v_m_1633_);
return v_res_1634_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0));
v___x_1637_ = l_Lean_stringToMessageData(v___x_1636_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2));
v___x_1640_ = l_Lean_stringToMessageData(v___x_1639_);
return v___x_1640_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4));
v___x_1643_ = l_Lean_stringToMessageData(v___x_1642_);
return v___x_1643_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6));
v___x_1646_ = l_Lean_stringToMessageData(v___x_1645_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8));
v___x_1649_ = l_Lean_stringToMessageData(v___x_1648_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10));
v___x_1652_ = l_Lean_stringToMessageData(v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12));
v___x_1655_ = l_Lean_stringToMessageData(v___x_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(lean_object* v_msg_1656_, lean_object* v_declHint_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v_env_1662_; uint8_t v___x_1663_; 
v___x_1660_ = lean_box(0);
v___x_1661_ = lean_st_ref_get(v___y_1658_);
v_env_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc_ref(v_env_1662_);
lean_dec(v___x_1661_);
v___x_1663_ = l_Lean_Name_isAnonymous(v_declHint_1657_);
if (v___x_1663_ == 0)
{
uint8_t v_isExporting_1664_; 
v_isExporting_1664_ = lean_ctor_get_uint8(v_env_1662_, sizeof(void*)*13);
if (v_isExporting_1664_ == 0)
{
lean_object* v___x_1665_; 
lean_dec_ref(v_env_1662_);
lean_dec(v_declHint_1657_);
v___x_1665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1665_, 0, v_msg_1656_);
return v___x_1665_;
}
else
{
lean_object* v___x_1666_; uint8_t v___x_1667_; 
lean_inc_ref(v_env_1662_);
v___x_1666_ = l_Lean_Environment_setExporting(v_env_1662_, v___x_1663_);
lean_inc(v_declHint_1657_);
lean_inc_ref(v___x_1666_);
v___x_1667_ = l_Lean_Environment_contains(v___x_1666_, v_declHint_1657_, v_isExporting_1664_);
if (v___x_1667_ == 0)
{
lean_object* v___x_1668_; 
lean_dec_ref(v___x_1666_);
lean_dec_ref(v_env_1662_);
lean_dec(v_declHint_1657_);
v___x_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1668_, 0, v_msg_1656_);
return v___x_1668_;
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v_c_1674_; lean_object* v___x_1675_; 
v___x_1669_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2);
v___x_1670_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5);
v___x_1671_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1666_);
v___x_1672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1666_);
lean_ctor_set(v___x_1672_, 1, v___x_1669_);
lean_ctor_set(v___x_1672_, 2, v___x_1670_);
lean_ctor_set(v___x_1672_, 3, v___x_1671_);
lean_inc(v_declHint_1657_);
v___x_1673_ = l_Lean_MessageData_ofConstName(v_declHint_1657_, v___x_1663_);
v_c_1674_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1674_, 0, v___x_1672_);
lean_ctor_set(v_c_1674_, 1, v___x_1673_);
v___x_1675_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1666_, v_declHint_1657_);
lean_dec_ref(v___x_1666_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
lean_dec_ref(v_env_1662_);
lean_dec(v_declHint_1657_);
v___x_1676_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_1677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_c_1674_);
v___x_1678_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_1679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1679_, 0, v___x_1677_);
lean_ctor_set(v___x_1679_, 1, v___x_1678_);
v___x_1680_ = l_Lean_MessageData_note(v___x_1679_);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v_msg_1656_);
lean_ctor_set(v___x_1681_, 1, v___x_1680_);
v___x_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1681_);
return v___x_1682_;
}
else
{
lean_object* v_val_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1717_; 
v_val_1683_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1685_ = v___x_1675_;
v_isShared_1686_ = v_isSharedCheck_1717_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_val_1683_);
lean_dec(v___x_1675_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1717_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v_moduleNames_1688_; lean_object* v_mod_1689_; uint8_t v___x_1690_; 
v___x_1687_ = l_Lean_Environment_header(v_env_1662_);
lean_dec_ref(v_env_1662_);
v_moduleNames_1688_ = lean_ctor_get(v___x_1687_, 4);
lean_inc_ref(v_moduleNames_1688_);
lean_dec_ref(v___x_1687_);
v_mod_1689_ = lean_array_get(v___x_1660_, v_moduleNames_1688_, v_val_1683_);
lean_dec(v_val_1683_);
lean_dec_ref(v_moduleNames_1688_);
v___x_1690_ = l_Lean_isPrivateName(v_declHint_1657_);
lean_dec(v_declHint_1657_);
if (v___x_1690_ == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1691_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5);
v___x_1692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v_c_1674_);
v___x_1693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1692_);
lean_ctor_set(v___x_1694_, 1, v___x_1693_);
v___x_1695_ = l_Lean_MessageData_ofName(v_mod_1689_);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = l_Lean_MessageData_note(v___x_1698_);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v_msg_1656_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1700_);
v___x_1702_ = v___x_1685_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1704_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_1705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1705_, 0, v___x_1704_);
lean_ctor_set(v___x_1705_, 1, v_c_1674_);
v___x_1706_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11);
v___x_1707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
v___x_1708_ = l_Lean_MessageData_ofName(v_mod_1689_);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1707_);
lean_ctor_set(v___x_1709_, 1, v___x_1708_);
v___x_1710_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = l_Lean_MessageData_note(v___x_1711_);
v___x_1713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_msg_1656_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set_tag(v___x_1685_, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1713_);
v___x_1715_ = v___x_1685_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1718_; 
lean_dec_ref(v_env_1662_);
lean_dec(v_declHint_1657_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v_msg_1656_);
return v___x_1718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___boxed(lean_object* v_msg_1719_, lean_object* v_declHint_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_1719_, v_declHint_1720_, v___y_1721_);
lean_dec(v___y_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(lean_object* v_msg_1724_, lean_object* v_declHint_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v___x_1731_; lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1741_; 
v___x_1731_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_1724_, v_declHint_1725_, v___y_1729_);
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1734_ = v___x_1731_;
v_isShared_1735_ = v_isSharedCheck_1741_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1741_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1736_ = l_Lean_unknownIdentifierMessageTag;
v___x_1737_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
lean_ctor_set(v___x_1737_, 1, v_a_1732_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1737_);
v___x_1739_ = v___x_1734_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16___boxed(lean_object* v_msg_1742_, lean_object* v_declHint_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(v_msg_1742_, v_declHint_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(lean_object* v_msg_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_ref_1756_; lean_object* v___x_1757_; lean_object* v_a_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
v_ref_1756_ = lean_ctor_get(v___y_1753_, 2);
v___x_1757_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(v_msg_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1760_ = v___x_1757_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_a_1758_);
lean_dec(v___x_1757_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
lean_inc(v_ref_1756_);
v___x_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1762_, 0, v_ref_1756_);
lean_ctor_set(v___x_1762_, 1, v_a_1758_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_msg_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec_ref(v___y_1768_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(lean_object* v_ref_1774_, lean_object* v_msg_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v_toCold_1781_; lean_object* v_currRecDepth_1782_; lean_object* v_ref_1783_; uint16_t v_optionFlags_1784_; uint8_t v_suppressElabErrors_1785_; uint8_t v_checkDeprecated_1786_; uint8_t v_isRecordingDeps_1787_; lean_object* v_ref_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v_toCold_1781_ = lean_ctor_get(v___y_1778_, 0);
v_currRecDepth_1782_ = lean_ctor_get(v___y_1778_, 1);
v_ref_1783_ = lean_ctor_get(v___y_1778_, 2);
v_optionFlags_1784_ = lean_ctor_get_uint16(v___y_1778_, sizeof(void*)*3);
v_suppressElabErrors_1785_ = lean_ctor_get_uint8(v___y_1778_, sizeof(void*)*3 + 2);
v_checkDeprecated_1786_ = lean_ctor_get_uint8(v___y_1778_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1787_ = lean_ctor_get_uint8(v___y_1778_, sizeof(void*)*3 + 4);
v_ref_1788_ = l_Lean_replaceRef(v_ref_1774_, v_ref_1783_);
lean_inc(v_currRecDepth_1782_);
lean_inc_ref(v_toCold_1781_);
v___x_1789_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1789_, 0, v_toCold_1781_);
lean_ctor_set(v___x_1789_, 1, v_currRecDepth_1782_);
lean_ctor_set(v___x_1789_, 2, v_ref_1788_);
lean_ctor_set_uint16(v___x_1789_, sizeof(void*)*3, v_optionFlags_1784_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*3 + 2, v_suppressElabErrors_1785_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*3 + 3, v_checkDeprecated_1786_);
lean_ctor_set_uint8(v___x_1789_, sizeof(void*)*3 + 4, v_isRecordingDeps_1787_);
v___x_1790_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_1775_, v___y_1776_, v___y_1777_, v___x_1789_, v___y_1779_);
lean_dec_ref_known(v___x_1789_, 3);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg___boxed(lean_object* v_ref_1791_, lean_object* v_msg_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_1791_, v_msg_1792_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
lean_dec(v___y_1796_);
lean_dec_ref(v___y_1795_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v_ref_1791_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(lean_object* v_ref_1799_, lean_object* v_msg_1800_, lean_object* v_declHint_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_){
_start:
{
lean_object* v___x_1807_; lean_object* v_a_1808_; lean_object* v___x_1809_; 
v___x_1807_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(v_msg_1800_, v_declHint_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
lean_inc(v_a_1808_);
lean_dec_ref(v___x_1807_);
v___x_1809_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_1799_, v_a_1808_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg___boxed(lean_object* v_ref_1810_, lean_object* v_msg_1811_, lean_object* v_declHint_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_1810_, v_msg_1811_, v_declHint_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v_ref_1810_);
return v_res_1818_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0));
v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(lean_object* v_ref_1822_, lean_object* v_constName_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; 
v___x_1829_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1);
v___x_1830_ = 0;
lean_inc(v_constName_1823_);
v___x_1831_ = l_Lean_MessageData_ofConstName(v_constName_1823_, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1829_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v___x_1833_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
v___x_1834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1832_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
v___x_1835_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_1822_, v___x_1834_, v_constName_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_ref_1836_, lean_object* v_constName_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_1836_, v_constName_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1839_);
lean_dec_ref(v___y_1838_);
lean_dec(v_ref_1836_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(lean_object* v_constName_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_ref_1850_; lean_object* v___x_1851_; 
v_ref_1850_ = lean_ctor_get(v___y_1847_, 2);
v___x_1851_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_1850_, v_constName_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_constName_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(lean_object* v_constName_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v___x_1865_; lean_object* v_env_1866_; uint8_t v___x_1867_; lean_object* v___x_1868_; 
v___x_1865_ = lean_st_ref_get(v___y_1863_);
v_env_1866_ = lean_ctor_get(v___x_1865_, 0);
lean_inc_ref(v_env_1866_);
lean_dec(v___x_1865_);
v___x_1867_ = 0;
lean_inc(v_constName_1859_);
v___x_1868_ = l_Lean_Environment_findConstVal_x3f(v_env_1866_, v_constName_1859_, v___x_1867_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
return v___x_1869_;
}
else
{
lean_object* v_val_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1877_; 
lean_dec(v_constName_1859_);
v_val_1870_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1877_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1872_ = v___x_1868_;
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_val_1870_);
lean_dec(v___x_1868_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1877_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1875_; 
if (v_isShared_1873_ == 0)
{
lean_ctor_set_tag(v___x_1872_, 0);
v___x_1875_ = v___x_1872_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_val_1870_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2___boxed(lean_object* v_constName_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(v_constName_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(lean_object* v_a_1885_, lean_object* v_a_1886_){
_start:
{
if (lean_obj_tag(v_a_1885_) == 0)
{
lean_object* v___x_1887_; 
v___x_1887_ = l_List_reverse___redArg(v_a_1886_);
return v___x_1887_;
}
else
{
lean_object* v_head_1888_; lean_object* v_tail_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1898_; 
v_head_1888_ = lean_ctor_get(v_a_1885_, 0);
v_tail_1889_ = lean_ctor_get(v_a_1885_, 1);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_a_1885_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1891_ = v_a_1885_;
v_isShared_1892_ = v_isSharedCheck_1898_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_tail_1889_);
lean_inc(v_head_1888_);
lean_dec(v_a_1885_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1898_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = l_Lean_mkLevelParam(v_head_1888_);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 1, v_a_1886_);
lean_ctor_set(v___x_1891_, 0, v___x_1893_);
v___x_1895_ = v___x_1891_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v___x_1893_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_a_1886_);
v___x_1895_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
v_a_1885_ = v_tail_1889_;
v_a_1886_ = v___x_1895_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(lean_object* v_constName_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_){
_start:
{
lean_object* v___x_1905_; 
lean_inc(v_constName_1899_);
v___x_1905_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(v_constName_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1917_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1908_ = v___x_1905_;
v_isShared_1909_ = v_isSharedCheck_1917_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1905_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1917_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v_levelParams_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
v_levelParams_1910_ = lean_ctor_get(v_a_1906_, 1);
lean_inc(v_levelParams_1910_);
lean_dec(v_a_1906_);
v___x_1911_ = lean_box(0);
v___x_1912_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(v_levelParams_1910_, v___x_1911_);
v___x_1913_ = l_Lean_mkConst(v_constName_1899_, v___x_1912_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 0, v___x_1913_);
v___x_1915_ = v___x_1908_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
else
{
lean_object* v_a_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
lean_dec(v_constName_1899_);
v_a_1918_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1925_ == 0)
{
v___x_1920_ = v___x_1905_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_a_1918_);
lean_dec(v___x_1905_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_a_1918_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1___boxed(lean_object* v_constName_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(v_constName_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
return v_res_1932_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1936_; double v___x_1937_; 
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_float_of_nat(v___x_1936_);
return v___x_1937_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4));
v___x_1941_ = l_Lean_stringToMessageData(v___x_1940_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(size_t v_sz_1944_, size_t v_i_1945_, lean_object* v_bs_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_){
_start:
{
uint8_t v___x_1952_; 
v___x_1952_ = lean_usize_dec_lt(v_i_1945_, v_sz_1944_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v_bs_1946_);
return v___x_1953_;
}
else
{
lean_object* v_v_1954_; lean_object* v_fst_1955_; lean_object* v_snd_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1992_; 
v_v_1954_ = lean_array_uget(v_bs_1946_, v_i_1945_);
v_fst_1955_ = lean_ctor_get(v_v_1954_, 0);
v_snd_1956_ = lean_ctor_get(v_v_1954_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_v_1954_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1958_ = v_v_1954_;
v_isShared_1959_ = v_isSharedCheck_1992_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_snd_1956_);
lean_inc(v_fst_1955_);
lean_dec(v_v_1954_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1992_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v_bs_x27_1961_; lean_object* v___x_1962_; 
v___x_1960_ = lean_unsigned_to_nat(0u);
v_bs_x27_1961_ = lean_array_uset(v_bs_1946_, v_i_1945_, v___x_1960_);
v___x_1962_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(v_fst_1955_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; double v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1972_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1));
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2);
v___x_1967_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
v___x_1968_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1968_, 0, v___x_1964_);
lean_ctor_set(v___x_1968_, 1, v___x_1965_);
lean_ctor_set(v___x_1968_, 2, v___x_1967_);
lean_ctor_set_float(v___x_1968_, sizeof(void*)*3, v___x_1966_);
lean_ctor_set_float(v___x_1968_, sizeof(void*)*3 + 8, v___x_1966_);
lean_ctor_set_uint8(v___x_1968_, sizeof(void*)*3 + 16, v___x_1952_);
v___x_1969_ = l_Lean_MessageData_ofConst(v_a_1963_);
v___x_1970_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5);
if (v_isShared_1959_ == 0)
{
lean_ctor_set_tag(v___x_1958_, 7);
lean_ctor_set(v___x_1958_, 1, v___x_1970_);
lean_ctor_set(v___x_1958_, 0, v___x_1969_);
v___x_1972_ = v___x_1958_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1969_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v___x_1970_);
v___x_1972_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; size_t v___x_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1973_ = l_Nat_reprFast(v_snd_1956_);
v___x_1974_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
v___x_1975_ = l_Lean_MessageData_ofFormat(v___x_1974_);
v___x_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1972_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6));
v___x_1978_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1968_);
lean_ctor_set(v___x_1978_, 1, v___x_1976_);
lean_ctor_set(v___x_1978_, 2, v___x_1977_);
v___x_1979_ = ((size_t)1ULL);
v___x_1980_ = lean_usize_add(v_i_1945_, v___x_1979_);
v___x_1981_ = lean_array_uset(v_bs_x27_1961_, v_i_1945_, v___x_1978_);
v_i_1945_ = v___x_1980_;
v_bs_1946_ = v___x_1981_;
goto _start;
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_bs_x27_1961_);
lean_del_object(v___x_1958_);
lean_dec(v_snd_1956_);
v_a_1984_ = lean_ctor_get(v___x_1962_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1962_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1962_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___boxed(lean_object* v_sz_1993_, lean_object* v_i_1994_, lean_object* v_bs_1995_, lean_object* v___y_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_){
_start:
{
size_t v_sz_boxed_2001_; size_t v_i_boxed_2002_; lean_object* v_res_2003_; 
v_sz_boxed_2001_ = lean_unbox_usize(v_sz_1993_);
lean_dec(v_sz_1993_);
v_i_boxed_2002_ = lean_unbox_usize(v_i_1994_);
lean_dec(v_i_1994_);
v_res_2003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(v_sz_boxed_2001_, v_i_boxed_2002_, v_bs_1995_, v___y_1996_, v___y_1997_, v___y_1998_, v___y_1999_);
lean_dec(v___y_1999_);
lean_dec_ref(v___y_1998_);
lean_dec(v___y_1997_);
lean_dec_ref(v___y_1996_);
return v_res_2003_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0(void){
_start:
{
lean_object* v___x_2004_; uint8_t v___x_2005_; double v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2004_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
v___x_2005_ = 1;
v___x_2006_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2);
v___x_2007_ = lean_box(0);
v___x_2008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1));
v___x_2009_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
lean_ctor_set(v___x_2009_, 1, v___x_2007_);
lean_ctor_set(v___x_2009_, 2, v___x_2004_);
lean_ctor_set_float(v___x_2009_, sizeof(void*)*3, v___x_2006_);
lean_ctor_set_float(v___x_2009_, sizeof(void*)*3 + 8, v___x_2006_);
lean_ctor_set_uint8(v___x_2009_, sizeof(void*)*3 + 16, v___x_2005_);
return v___x_2009_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3(void){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2));
v___x_2014_ = l_Lean_MessageData_ofFormat(v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(lean_object* v_thms_2015_, lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___y_2024_; lean_object* v___x_2047_; lean_object* v_data_2048_; lean_object* v___x_2049_; lean_object* v___y_2051_; lean_object* v___y_2052_; uint8_t v___x_2054_; 
v___x_2021_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_thms_2015_);
v___x_2022_ = lean_unsigned_to_nat(0u);
v___x_2047_ = lean_array_get_size(v___x_2021_);
v_data_2048_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(v___x_2021_, v___x_2022_, v___x_2047_);
lean_dec_ref(v___x_2021_);
v___x_2049_ = lean_array_get_size(v_data_2048_);
v___x_2054_ = lean_nat_dec_eq(v___x_2049_, v___x_2022_);
if (v___x_2054_ == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___y_2058_; uint8_t v___x_2060_; 
v___x_2055_ = lean_unsigned_to_nat(1u);
v___x_2056_ = lean_nat_sub(v___x_2049_, v___x_2055_);
v___x_2060_ = lean_nat_dec_le(v___x_2022_, v___x_2056_);
if (v___x_2060_ == 0)
{
lean_inc(v___x_2056_);
v___y_2058_ = v___x_2056_;
goto v___jp_2057_;
}
else
{
v___y_2058_ = v___x_2022_;
goto v___jp_2057_;
}
v___jp_2057_:
{
uint8_t v___x_2059_; 
v___x_2059_ = lean_nat_dec_le(v___y_2058_, v___x_2056_);
if (v___x_2059_ == 0)
{
lean_dec(v___x_2056_);
lean_inc(v___y_2058_);
v___y_2051_ = v___y_2058_;
v___y_2052_ = v___y_2058_;
goto v___jp_2050_;
}
else
{
v___y_2051_ = v___y_2058_;
v___y_2052_ = v___x_2056_;
goto v___jp_2050_;
}
}
}
else
{
v___y_2024_ = v_data_2048_;
goto v___jp_2023_;
}
v___jp_2023_:
{
size_t v_sz_2025_; size_t v___x_2026_; lean_object* v___x_2027_; 
v_sz_2025_ = lean_array_size(v___y_2024_);
v___x_2026_ = ((size_t)0ULL);
v___x_2027_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(v_sz_2025_, v___x_2026_, v___y_2024_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2038_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2038_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2032_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0);
v___x_2033_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3);
v___x_2034_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
lean_ctor_set(v___x_2034_, 2, v_a_2028_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2034_);
v___x_2036_ = v___x_2030_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
v_a_2039_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2027_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2027_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
v___jp_2050_:
{
lean_object* v___x_2053_; 
v___x_2053_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v___x_2049_, v_data_2048_, v___y_2051_, v___y_2052_);
lean_dec(v___y_2052_);
v___y_2024_ = v___x_2053_;
goto v___jp_2023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___boxed(lean_object* v_thms_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(v_thms_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec_ref(v_thms_2061_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(lean_object* v_00_u03b2_2068_, lean_object* v_m_2069_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_m_2069_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___boxed(lean_object* v_00_u03b2_2071_, lean_object* v_m_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(v_00_u03b2_2071_, v_m_2072_);
lean_dec_ref(v_m_2072_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(lean_object* v_n_2074_, lean_object* v_as_2075_, lean_object* v_lo_2076_, lean_object* v_hi_2077_, lean_object* v_w_2078_, lean_object* v_hlo_2079_, lean_object* v_hhi_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_2074_, v_as_2075_, v_lo_2076_, v_hi_2077_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___boxed(lean_object* v_n_2082_, lean_object* v_as_2083_, lean_object* v_lo_2084_, lean_object* v_hi_2085_, lean_object* v_w_2086_, lean_object* v_hlo_2087_, lean_object* v_hhi_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(v_n_2082_, v_as_2083_, v_lo_2084_, v_hi_2085_, v_w_2086_, v_hlo_2087_, v_hhi_2088_);
lean_dec(v_hi_2085_);
lean_dec(v_n_2082_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(lean_object* v_00_u03c3_2090_, lean_object* v_00_u03b2_2091_, lean_object* v_map_2092_, lean_object* v_f_2093_, lean_object* v_init_2094_){
_start:
{
lean_object* v___x_2095_; 
v___x_2095_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_map_2092_, v_f_2093_, v_init_2094_);
return v___x_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2096_, lean_object* v_00_u03b2_2097_, lean_object* v_map_2098_, lean_object* v_f_2099_, lean_object* v_init_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(v_00_u03c3_2096_, v_00_u03b2_2097_, v_map_2098_, v_f_2099_, v_init_2100_);
lean_dec_ref(v_map_2098_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(lean_object* v_n_2102_, lean_object* v_lo_2103_, lean_object* v_hi_2104_, lean_object* v_hhi_2105_, lean_object* v_pivot_2106_, lean_object* v_as_2107_, lean_object* v_i_2108_, lean_object* v_k_2109_, lean_object* v_ilo_2110_, lean_object* v_ik_2111_, lean_object* v_w_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_2104_, v_pivot_2106_, v_as_2107_, v_i_2108_, v_k_2109_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___boxed(lean_object* v_n_2114_, lean_object* v_lo_2115_, lean_object* v_hi_2116_, lean_object* v_hhi_2117_, lean_object* v_pivot_2118_, lean_object* v_as_2119_, lean_object* v_i_2120_, lean_object* v_k_2121_, lean_object* v_ilo_2122_, lean_object* v_ik_2123_, lean_object* v_w_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(v_n_2114_, v_lo_2115_, v_hi_2116_, v_hhi_2117_, v_pivot_2118_, v_as_2119_, v_i_2120_, v_k_2121_, v_ilo_2122_, v_ik_2123_, v_w_2124_);
lean_dec_ref(v_pivot_2118_);
lean_dec(v_hi_2116_);
lean_dec(v_lo_2115_);
lean_dec(v_n_2114_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(lean_object* v_map_2126_, lean_object* v_f_2127_, lean_object* v_init_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2127_, v_map_2126_, v_init_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_2130_, lean_object* v_f_2131_, lean_object* v_init_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(v_map_2130_, v_f_2131_, v_init_2132_);
lean_dec_ref(v_map_2130_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2134_, lean_object* v_00_u03b2_2135_, lean_object* v_map_2136_, lean_object* v_f_2137_, lean_object* v_init_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2137_, v_map_2136_, v_init_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_2140_, lean_object* v_00_u03b2_2141_, lean_object* v_map_2142_, lean_object* v_f_2143_, lean_object* v_init_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(v_00_u03c3_2140_, v_00_u03b2_2141_, v_map_2142_, v_f_2143_, v_init_2144_);
lean_dec_ref(v_map_2142_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2146_, lean_object* v_constName_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2154_, lean_object* v_constName_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(v_00_u03b1_2154_, v_constName_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03c3_2162_, lean_object* v_00_u03b1_2163_, lean_object* v_00_u03b2_2164_, lean_object* v_f_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2165_, v_x_2166_, v_x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03c3_2169_, lean_object* v_00_u03b1_2170_, lean_object* v_00_u03b2_2171_, lean_object* v_f_2172_, lean_object* v_x_2173_, lean_object* v_x_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(v_00_u03c3_2169_, v_00_u03b1_2170_, v_00_u03b2_2171_, v_f_2172_, v_x_2173_, v_x_2174_);
lean_dec_ref(v_x_2173_);
return v_res_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(lean_object* v_00_u03b1_2176_, lean_object* v_ref_2177_, lean_object* v_constName_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_2177_, v_constName_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b1_2185_, lean_object* v_ref_2186_, lean_object* v_constName_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(v_00_u03b1_2185_, v_ref_2186_, v_constName_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v_ref_2186_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(lean_object* v_00_u03b1_2194_, lean_object* v_00_u03b2_2195_, lean_object* v_00_u03c3_2196_, lean_object* v_f_2197_, lean_object* v_as_2198_, size_t v_i_2199_, size_t v_stop_2200_, lean_object* v_b_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_2197_, v_as_2198_, v_i_2199_, v_stop_2200_, v_b_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___boxed(lean_object* v_00_u03b1_2203_, lean_object* v_00_u03b2_2204_, lean_object* v_00_u03c3_2205_, lean_object* v_f_2206_, lean_object* v_as_2207_, lean_object* v_i_2208_, lean_object* v_stop_2209_, lean_object* v_b_2210_){
_start:
{
size_t v_i_boxed_2211_; size_t v_stop_boxed_2212_; lean_object* v_res_2213_; 
v_i_boxed_2211_ = lean_unbox_usize(v_i_2208_);
lean_dec(v_i_2208_);
v_stop_boxed_2212_ = lean_unbox_usize(v_stop_2209_);
lean_dec(v_stop_2209_);
v_res_2213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(v_00_u03b1_2203_, v_00_u03b2_2204_, v_00_u03c3_2205_, v_f_2206_, v_as_2207_, v_i_boxed_2211_, v_stop_boxed_2212_, v_b_2210_);
lean_dec_ref(v_as_2207_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(lean_object* v_00_u03c3_2214_, lean_object* v_00_u03b1_2215_, lean_object* v_00_u03b2_2216_, lean_object* v_f_2217_, lean_object* v_keys_2218_, lean_object* v_vals_2219_, lean_object* v_heq_2220_, lean_object* v_i_2221_, lean_object* v_acc_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_2217_, v_keys_2218_, v_vals_2219_, v_i_2221_, v_acc_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03c3_2224_, lean_object* v_00_u03b1_2225_, lean_object* v_00_u03b2_2226_, lean_object* v_f_2227_, lean_object* v_keys_2228_, lean_object* v_vals_2229_, lean_object* v_heq_2230_, lean_object* v_i_2231_, lean_object* v_acc_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(v_00_u03c3_2224_, v_00_u03b1_2225_, v_00_u03b2_2226_, v_f_2227_, v_keys_2228_, v_vals_2229_, v_heq_2230_, v_i_2231_, v_acc_2232_);
lean_dec_ref(v_vals_2229_);
lean_dec_ref(v_keys_2228_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(lean_object* v_00_u03b1_2234_, lean_object* v_ref_2235_, lean_object* v_msg_2236_, lean_object* v_declHint_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v___x_2243_; 
v___x_2243_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_2235_, v_msg_2236_, v_declHint_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___boxed(lean_object* v_00_u03b1_2244_, lean_object* v_ref_2245_, lean_object* v_msg_2246_, lean_object* v_declHint_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(v_00_u03b1_2244_, v_ref_2245_, v_msg_2246_, v_declHint_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v_ref_2245_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(lean_object* v_msg_2254_, lean_object* v_declHint_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_2254_, v_declHint_2255_, v___y_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___boxed(lean_object* v_msg_2262_, lean_object* v_declHint_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(v_msg_2262_, v_declHint_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(lean_object* v_00_u03b1_2270_, lean_object* v_ref_2271_, lean_object* v_msg_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_2271_, v_msg_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___boxed(lean_object* v_00_u03b1_2279_, lean_object* v_ref_2280_, lean_object* v_msg_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(v_00_u03b1_2279_, v_ref_2280_, v_msg_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
lean_dec(v_ref_2280_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_2288_, lean_object* v_msg_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2295_; 
v___x_2295_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_2296_, lean_object* v_msg_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(v_00_u03b1_2296_, v_msg_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(lean_object* v_k_2304_, lean_object* v_b_2305_, lean_object* v_c_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v___x_2312_; 
lean_inc(v___y_2310_);
lean_inc_ref(v___y_2309_);
lean_inc(v___y_2308_);
lean_inc_ref(v___y_2307_);
v___x_2312_ = lean_apply_7(v_k_2304_, v_b_2305_, v_c_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_, lean_box(0));
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed(lean_object* v_k_2313_, lean_object* v_b_2314_, lean_object* v_c_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(v_k_2313_, v_b_2314_, v_c_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(lean_object* v_type_2322_, lean_object* v_k_2323_, uint8_t v_cleanupAnnotations_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v___f_2330_; uint8_t v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___f_2330_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2330_, 0, v_k_2323_);
v___x_2331_ = 0;
v___x_2332_ = lean_box(0);
v___x_2333_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2331_, v___x_2332_, v_type_2322_, v___f_2330_, v_cleanupAnnotations_2324_, v___x_2331_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
v_a_2342_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2333_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2333_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___boxed(lean_object* v_type_2350_, lean_object* v_k_2351_, lean_object* v_cleanupAnnotations_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2358_; lean_object* v_res_2359_; 
v_cleanupAnnotations_boxed_2358_ = lean_unbox(v_cleanupAnnotations_2352_);
v_res_2359_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v_type_2350_, v_k_2351_, v_cleanupAnnotations_boxed_2358_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(lean_object* v_00_u03b1_2360_, lean_object* v_type_2361_, lean_object* v_k_2362_, uint8_t v_cleanupAnnotations_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v_type_2361_, v_k_2362_, v_cleanupAnnotations_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___boxed(lean_object* v_00_u03b1_2370_, lean_object* v_type_2371_, lean_object* v_k_2372_, lean_object* v_cleanupAnnotations_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2379_; lean_object* v_res_2380_; 
v_cleanupAnnotations_boxed_2379_ = lean_unbox(v_cleanupAnnotations_2373_);
v_res_2380_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(v_00_u03b1_2370_, v_type_2371_, v_k_2372_, v_cleanupAnnotations_boxed_2379_, v___y_2374_, v___y_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
return v_res_2380_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = lean_box(0);
v___x_2385_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1));
v___x_2386_ = l_Lean_mkConst(v___x_2385_, v___x_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(lean_object* v_x_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2395_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3);
v___x_2396_ = 0;
v___x_2397_ = lean_box(0);
v___x_2398_ = l_Lean_Meta_mkFreshExprMVar(v___x_2395_, v___x_2396_, v___x_2397_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2407_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2401_ = v___x_2398_;
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2398_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2407_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2403_; lean_object* v___x_2405_; 
v___x_2403_ = l_Lean_Expr_mvarId_x21(v_a_2399_);
lean_dec(v_a_2399_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 0, v___x_2403_);
v___x_2405_ = v___x_2401_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v___x_2403_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
v_a_2408_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2398_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2398_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___boxed(lean_object* v_x_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(v_x_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec_ref(v_x_2416_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2423_, lean_object* v_b_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; 
lean_inc(v___y_2428_);
lean_inc_ref(v___y_2427_);
lean_inc(v___y_2426_);
lean_inc_ref(v___y_2425_);
v___x_2430_ = lean_apply_6(v_k_2423_, v_b_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, lean_box(0));
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2431_, lean_object* v_b_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(v_k_2431_, v_b_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec_ref(v___y_2433_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_name_2439_, uint8_t v_bi_2440_, lean_object* v_type_2441_, lean_object* v_k_2442_, uint8_t v_kind_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___f_2449_; lean_object* v___x_2450_; 
v___f_2449_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2449_, 0, v_k_2442_);
v___x_2450_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2439_, v_bi_2440_, v_type_2441_, v___f_2449_, v_kind_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2458_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2453_ = v___x_2450_;
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_a_2451_);
lean_dec(v___x_2450_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2458_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2456_; 
if (v_isShared_2454_ == 0)
{
v___x_2456_ = v___x_2453_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_a_2451_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
v_a_2459_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2450_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2450_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_name_2467_, lean_object* v_bi_2468_, lean_object* v_type_2469_, lean_object* v_k_2470_, lean_object* v_kind_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
uint8_t v_bi_boxed_2477_; uint8_t v_kind_boxed_2478_; lean_object* v_res_2479_; 
v_bi_boxed_2477_ = lean_unbox(v_bi_2468_);
v_kind_boxed_2478_ = lean_unbox(v_kind_2471_);
v_res_2479_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2467_, v_bi_boxed_2477_, v_type_2469_, v_k_2470_, v_kind_boxed_2478_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(lean_object* v_name_2480_, lean_object* v_type_2481_, lean_object* v_k_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
uint8_t v___x_2488_; uint8_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = 0;
v___x_2489_ = 0;
v___x_2490_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2480_, v___x_2488_, v_type_2481_, v_k_2482_, v___x_2489_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg___boxed(lean_object* v_name_2491_, lean_object* v_type_2492_, lean_object* v_k_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v_name_2491_, v_type_2492_, v_k_2493_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(lean_object* v___f_2503_, lean_object* v_x_2504_, lean_object* v_type_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1));
v___x_2512_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v___x_2511_, v_type_2505_, v___f_2503_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
return v___x_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___boxed(lean_object* v___f_2513_, lean_object* v_x_2514_, lean_object* v_type_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(v___f_2513_, v_x_2514_, v_type_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec_ref(v_x_2514_);
return v_res_2521_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(uint8_t v_suppressElabErrors_2528_, lean_object* v_x_2529_){
_start:
{
if (lean_obj_tag(v_x_2529_) == 1)
{
lean_object* v_pre_2530_; 
v_pre_2530_ = lean_ctor_get(v_x_2529_, 0);
switch(lean_obj_tag(v_pre_2530_))
{
case 1:
{
lean_object* v_pre_2531_; 
v_pre_2531_ = lean_ctor_get(v_pre_2530_, 0);
switch(lean_obj_tag(v_pre_2531_))
{
case 0:
{
lean_object* v_str_2532_; lean_object* v_str_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v_str_2532_ = lean_ctor_get(v_x_2529_, 1);
v_str_2533_ = lean_ctor_get(v_pre_2530_, 1);
v___x_2534_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_2535_ = lean_string_dec_eq(v_str_2533_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_2537_ = lean_string_dec_eq(v_str_2533_, v___x_2536_);
if (v___x_2537_ == 0)
{
return v___x_2537_;
}
else
{
lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0));
v___x_2539_ = lean_string_dec_eq(v_str_2532_, v___x_2538_);
if (v___x_2539_ == 0)
{
return v___x_2539_;
}
else
{
return v_suppressElabErrors_2528_;
}
}
}
else
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1));
v___x_2541_ = lean_string_dec_eq(v_str_2532_, v___x_2540_);
if (v___x_2541_ == 0)
{
return v___x_2541_;
}
else
{
return v_suppressElabErrors_2528_;
}
}
}
case 1:
{
lean_object* v_pre_2542_; 
v_pre_2542_ = lean_ctor_get(v_pre_2531_, 0);
if (lean_obj_tag(v_pre_2542_) == 0)
{
lean_object* v_str_2543_; lean_object* v_str_2544_; lean_object* v_str_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v_str_2543_ = lean_ctor_get(v_x_2529_, 1);
v_str_2544_ = lean_ctor_get(v_pre_2530_, 1);
v_str_2545_ = lean_ctor_get(v_pre_2531_, 1);
v___x_2546_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2));
v___x_2547_ = lean_string_dec_eq(v_str_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
return v___x_2547_;
}
else
{
lean_object* v___x_2548_; uint8_t v___x_2549_; 
v___x_2548_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3));
v___x_2549_ = lean_string_dec_eq(v_str_2544_, v___x_2548_);
if (v___x_2549_ == 0)
{
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2550_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4));
v___x_2551_ = lean_string_dec_eq(v_str_2543_, v___x_2550_);
if (v___x_2551_ == 0)
{
return v___x_2551_;
}
else
{
return v_suppressElabErrors_2528_;
}
}
}
}
else
{
uint8_t v___x_2552_; 
v___x_2552_ = 0;
return v___x_2552_;
}
}
default: 
{
uint8_t v___x_2553_; 
v___x_2553_ = 0;
return v___x_2553_;
}
}
}
case 0:
{
lean_object* v_str_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v_str_2554_ = lean_ctor_get(v_x_2529_, 1);
v___x_2555_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5));
v___x_2556_ = lean_string_dec_eq(v_str_2554_, v___x_2555_);
if (v___x_2556_ == 0)
{
return v___x_2556_;
}
else
{
return v_suppressElabErrors_2528_;
}
}
default: 
{
uint8_t v___x_2557_; 
v___x_2557_ = 0;
return v___x_2557_;
}
}
}
else
{
uint8_t v___x_2558_; 
v___x_2558_ = 0;
return v___x_2558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_2559_, lean_object* v_x_2560_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2561_; uint8_t v_res_2562_; lean_object* v_r_2563_; 
v_suppressElabErrors_boxed_2561_ = lean_unbox(v_suppressElabErrors_2559_);
v_res_2562_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(v_suppressElabErrors_boxed_2561_, v_x_2560_);
lean_dec(v_x_2560_);
v_r_2563_ = lean_box(v_res_2562_);
return v_r_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(lean_object* v_ref_2564_, lean_object* v_msgData_2565_, uint8_t v_severity_2566_, uint8_t v_isSilent_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___y_2574_; lean_object* v___y_2575_; uint8_t v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; uint8_t v___y_2580_; lean_object* v_toCold_2581_; lean_object* v___y_2582_; lean_object* v___y_2611_; lean_object* v___y_2612_; uint8_t v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; uint8_t v___y_2616_; uint8_t v___y_2617_; lean_object* v___y_2618_; uint8_t v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; uint8_t v___y_2642_; uint8_t v___y_2643_; lean_object* v___y_2644_; uint8_t v___y_2648_; uint8_t v___y_2649_; uint8_t v___x_2659_; uint8_t v___y_2661_; uint8_t v___x_2667_; 
v___x_2659_ = 2;
v___x_2667_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2566_, v___x_2659_);
if (v___x_2667_ == 0)
{
v___y_2661_ = v___x_2667_;
goto v___jp_2660_;
}
else
{
uint8_t v___x_2668_; 
lean_inc_ref(v_msgData_2565_);
v___x_2668_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2565_);
if (v___x_2668_ == 0)
{
v___y_2661_ = v___x_2668_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
lean_dec_ref(v_msgData_2565_);
v___x_2669_ = lean_box(0);
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
return v___x_2670_;
}
}
v___jp_2573_:
{
lean_object* v_currNamespace_2583_; lean_object* v_openDecls_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v_env_2589_; lean_object* v_nextMacroScope_2590_; lean_object* v_ngen_2591_; lean_object* v_auxDeclNGen_2592_; lean_object* v_traceState_2593_; lean_object* v_cache_2594_; lean_object* v_recordedDeps_2595_; lean_object* v_messages_2596_; lean_object* v_infoState_2597_; lean_object* v_snapshotTasks_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2609_; 
v_currNamespace_2583_ = lean_ctor_get(v_toCold_2581_, 4);
v_openDecls_2584_ = lean_ctor_get(v_toCold_2581_, 5);
lean_inc(v_openDecls_2584_);
lean_inc(v_currNamespace_2583_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v_currNamespace_2583_);
lean_ctor_set(v___x_2585_, 1, v_openDecls_2584_);
v___x_2586_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
lean_ctor_set(v___x_2586_, 1, v___y_2578_);
lean_inc_ref(v___y_2574_);
lean_inc_ref(v___y_2579_);
v___x_2587_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2587_, 0, v___y_2579_);
lean_ctor_set(v___x_2587_, 1, v___y_2577_);
lean_ctor_set(v___x_2587_, 2, v___y_2575_);
lean_ctor_set(v___x_2587_, 3, v___y_2574_);
lean_ctor_set(v___x_2587_, 4, v___x_2586_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*5, v___y_2576_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*5 + 1, v___y_2580_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*5 + 2, v_isSilent_2567_);
v___x_2588_ = lean_st_ref_take(v___y_2582_);
v_env_2589_ = lean_ctor_get(v___x_2588_, 0);
v_nextMacroScope_2590_ = lean_ctor_get(v___x_2588_, 1);
v_ngen_2591_ = lean_ctor_get(v___x_2588_, 2);
v_auxDeclNGen_2592_ = lean_ctor_get(v___x_2588_, 3);
v_traceState_2593_ = lean_ctor_get(v___x_2588_, 4);
v_cache_2594_ = lean_ctor_get(v___x_2588_, 5);
v_recordedDeps_2595_ = lean_ctor_get(v___x_2588_, 6);
v_messages_2596_ = lean_ctor_get(v___x_2588_, 7);
v_infoState_2597_ = lean_ctor_get(v___x_2588_, 8);
v_snapshotTasks_2598_ = lean_ctor_get(v___x_2588_, 9);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2588_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2600_ = v___x_2588_;
v_isShared_2601_ = v_isSharedCheck_2609_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_snapshotTasks_2598_);
lean_inc(v_infoState_2597_);
lean_inc(v_messages_2596_);
lean_inc(v_recordedDeps_2595_);
lean_inc(v_cache_2594_);
lean_inc(v_traceState_2593_);
lean_inc(v_auxDeclNGen_2592_);
lean_inc(v_ngen_2591_);
lean_inc(v_nextMacroScope_2590_);
lean_inc(v_env_2589_);
lean_dec(v___x_2588_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2609_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2602_ = lean_box(0);
v___x_2603_ = l_Lean_MessageLog_add(v___x_2587_, v_messages_2596_);
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 7, v___x_2603_);
v___x_2605_ = v___x_2600_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_env_2589_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v_nextMacroScope_2590_);
lean_ctor_set(v_reuseFailAlloc_2608_, 2, v_ngen_2591_);
lean_ctor_set(v_reuseFailAlloc_2608_, 3, v_auxDeclNGen_2592_);
lean_ctor_set(v_reuseFailAlloc_2608_, 4, v_traceState_2593_);
lean_ctor_set(v_reuseFailAlloc_2608_, 5, v_cache_2594_);
lean_ctor_set(v_reuseFailAlloc_2608_, 6, v_recordedDeps_2595_);
lean_ctor_set(v_reuseFailAlloc_2608_, 7, v___x_2603_);
lean_ctor_set(v_reuseFailAlloc_2608_, 8, v_infoState_2597_);
lean_ctor_set(v_reuseFailAlloc_2608_, 9, v_snapshotTasks_2598_);
v___x_2605_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = lean_st_ref_put(v___y_2582_, v___x_2605_);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2602_);
return v___x_2607_;
}
}
}
v___jp_2610_:
{
lean_object* v_fileName_2619_; lean_object* v_fileMap_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2636_; 
v_fileName_2619_ = lean_ctor_get(v___y_2615_, 0);
v_fileMap_2620_ = lean_ctor_get(v___y_2615_, 1);
v___x_2621_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2565_);
v___x_2622_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(v___x_2621_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2636_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2636_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_inc_ref_n(v_fileMap_2620_, 2);
v___x_2627_ = l_Lean_FileMap_toPosition(v_fileMap_2620_, v___y_2614_);
lean_dec(v___y_2614_);
v___x_2628_ = l_Lean_FileMap_toPosition(v_fileMap_2620_, v___y_2618_);
lean_dec(v___y_2618_);
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
v___x_2630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
if (v___y_2613_ == 0)
{
lean_del_object(v___x_2625_);
lean_dec_ref(v___y_2611_);
v___y_2574_ = v___x_2630_;
v___y_2575_ = v___x_2629_;
v___y_2576_ = v___y_2616_;
v___y_2577_ = v___x_2627_;
v___y_2578_ = v_a_2623_;
v___y_2579_ = v_fileName_2619_;
v___y_2580_ = v___y_2617_;
v_toCold_2581_ = v___y_2612_;
v___y_2582_ = v___y_2571_;
goto v___jp_2573_;
}
else
{
uint8_t v___x_2631_; 
lean_inc(v_a_2623_);
v___x_2631_ = l_Lean_MessageData_hasTag(v___y_2611_, v_a_2623_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
lean_dec_ref_known(v___x_2629_, 1);
lean_dec_ref(v___x_2627_);
lean_dec(v_a_2623_);
v___x_2632_ = lean_box(0);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v___x_2632_);
v___x_2634_ = v___x_2625_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
else
{
lean_del_object(v___x_2625_);
v___y_2574_ = v___x_2630_;
v___y_2575_ = v___x_2629_;
v___y_2576_ = v___y_2616_;
v___y_2577_ = v___x_2627_;
v___y_2578_ = v_a_2623_;
v___y_2579_ = v_fileName_2619_;
v___y_2580_ = v___y_2617_;
v_toCold_2581_ = v___y_2612_;
v___y_2582_ = v___y_2571_;
goto v___jp_2573_;
}
}
}
}
v___jp_2637_:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_Syntax_getTailPos_x3f(v___y_2641_, v___y_2642_);
lean_dec(v___y_2641_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_inc(v___y_2644_);
v___y_2611_ = v___y_2639_;
v___y_2612_ = v___y_2640_;
v___y_2613_ = v___y_2638_;
v___y_2614_ = v___y_2644_;
v___y_2615_ = v___y_2640_;
v___y_2616_ = v___y_2642_;
v___y_2617_ = v___y_2643_;
v___y_2618_ = v___y_2644_;
goto v___jp_2610_;
}
else
{
lean_object* v_val_2646_; 
v_val_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_val_2646_);
lean_dec_ref_known(v___x_2645_, 1);
v___y_2611_ = v___y_2639_;
v___y_2612_ = v___y_2640_;
v___y_2613_ = v___y_2638_;
v___y_2614_ = v___y_2644_;
v___y_2615_ = v___y_2640_;
v___y_2616_ = v___y_2642_;
v___y_2617_ = v___y_2643_;
v___y_2618_ = v_val_2646_;
goto v___jp_2610_;
}
}
v___jp_2647_:
{
lean_object* v_toCold_2650_; lean_object* v_ref_2651_; uint8_t v_suppressElabErrors_2652_; lean_object* v___x_2653_; lean_object* v___f_2654_; lean_object* v_ref_2655_; lean_object* v___x_2656_; 
v_toCold_2650_ = lean_ctor_get(v___y_2570_, 0);
v_ref_2651_ = lean_ctor_get(v___y_2570_, 2);
v_suppressElabErrors_2652_ = lean_ctor_get_uint8(v___y_2570_, sizeof(void*)*3 + 2);
v___x_2653_ = lean_box(v_suppressElabErrors_2652_);
v___f_2654_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2654_, 0, v___x_2653_);
v_ref_2655_ = l_Lean_replaceRef(v_ref_2564_, v_ref_2651_);
v___x_2656_ = l_Lean_Syntax_getPos_x3f(v_ref_2655_, v___y_2648_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2657_; 
v___x_2657_ = lean_unsigned_to_nat(0u);
v___y_2638_ = v_suppressElabErrors_2652_;
v___y_2639_ = v___f_2654_;
v___y_2640_ = v_toCold_2650_;
v___y_2641_ = v_ref_2655_;
v___y_2642_ = v___y_2648_;
v___y_2643_ = v___y_2649_;
v___y_2644_ = v___x_2657_;
goto v___jp_2637_;
}
else
{
lean_object* v_val_2658_; 
v_val_2658_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_val_2658_);
lean_dec_ref_known(v___x_2656_, 1);
v___y_2638_ = v_suppressElabErrors_2652_;
v___y_2639_ = v___f_2654_;
v___y_2640_ = v_toCold_2650_;
v___y_2641_ = v_ref_2655_;
v___y_2642_ = v___y_2648_;
v___y_2643_ = v___y_2649_;
v___y_2644_ = v_val_2658_;
goto v___jp_2637_;
}
}
v___jp_2660_:
{
uint8_t v___x_2662_; uint8_t v___x_2663_; 
v___x_2662_ = 1;
v___x_2663_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2566_, v___x_2662_);
if (v___x_2663_ == 0)
{
v___y_2648_ = v___y_2661_;
v___y_2649_ = v_severity_2566_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2664_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2570_);
v___x_2665_ = l_Lean_warningAsError;
v___x_2666_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(v___x_2664_, v___x_2665_);
lean_dec_ref(v___x_2664_);
if (v___x_2666_ == 0)
{
v___y_2648_ = v___y_2661_;
v___y_2649_ = v_severity_2566_;
goto v___jp_2647_;
}
else
{
v___y_2648_ = v___y_2661_;
v___y_2649_ = v___x_2659_;
goto v___jp_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_ref_2671_, lean_object* v_msgData_2672_, lean_object* v_severity_2673_, lean_object* v_isSilent_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
uint8_t v_severity_boxed_2680_; uint8_t v_isSilent_boxed_2681_; lean_object* v_res_2682_; 
v_severity_boxed_2680_ = lean_unbox(v_severity_2673_);
v_isSilent_boxed_2681_ = lean_unbox(v_isSilent_2674_);
v_res_2682_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(v_ref_2671_, v_msgData_2672_, v_severity_boxed_2680_, v_isSilent_boxed_2681_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v_ref_2671_);
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(lean_object* v_msgData_2683_, uint8_t v_severity_2684_, uint8_t v_isSilent_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
lean_object* v_ref_2691_; lean_object* v___x_2692_; 
v_ref_2691_ = lean_ctor_get(v___y_2688_, 2);
v___x_2692_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(v_ref_2691_, v_msgData_2683_, v_severity_2684_, v_isSilent_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4___boxed(lean_object* v_msgData_2693_, lean_object* v_severity_2694_, lean_object* v_isSilent_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
uint8_t v_severity_boxed_2701_; uint8_t v_isSilent_boxed_2702_; lean_object* v_res_2703_; 
v_severity_boxed_2701_ = lean_unbox(v_severity_2694_);
v_isSilent_boxed_2702_ = lean_unbox(v_isSilent_2695_);
v_res_2703_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(v_msgData_2693_, v_severity_boxed_2701_, v_isSilent_boxed_2702_, v___y_2696_, v___y_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(lean_object* v_msgData_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
uint8_t v___x_2710_; uint8_t v___x_2711_; lean_object* v___x_2712_; 
v___x_2710_ = 0;
v___x_2711_ = 0;
v___x_2712_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(v_msgData_2704_, v___x_2710_, v___x_2711_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3___boxed(lean_object* v_msgData_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v_msgData_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(lean_object* v_constName_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; lean_object* v_env_2727_; uint8_t v___x_2728_; lean_object* v___x_2729_; 
v___x_2726_ = lean_st_ref_get(v___y_2724_);
v_env_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc_ref(v_env_2727_);
lean_dec(v___x_2726_);
v___x_2728_ = 0;
lean_inc(v_constName_2720_);
v___x_2729_ = l_Lean_Environment_find_x3f(v_env_2727_, v_constName_2720_, v___x_2728_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
return v___x_2730_;
}
else
{
lean_object* v_val_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v_constName_2720_);
v_val_2731_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2729_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_val_2731_);
lean_dec(v___x_2729_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
lean_ctor_set_tag(v___x_2733_, 0);
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_val_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1___boxed(lean_object* v_constName_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(v_constName_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
return v_res_2745_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v___x_2751_ = l_Lean_stringToMessageData(v___x_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(lean_object* v_declName_2764_, lean_object* v_params_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v___f_2771_; lean_object* v___x_2772_; 
v___f_2771_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1));
lean_inc(v_declName_2764_);
v___x_2772_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(v_declName_2764_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2774_; uint8_t v___x_2775_; lean_object* v___x_2776_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
v___x_2774_ = l_Lean_ConstantInfo_type(v_a_2773_);
lean_dec(v_a_2773_);
v___x_2775_ = 0;
v___x_2776_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v___x_2774_, v___f_2771_, v___x_2775_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
lean_inc_ref(v_params_2765_);
v___x_2778_ = l_Lean_Meta_Grind_main(v_a_2777_, v_params_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2867_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2867_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2867_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v_counters_2783_; lean_object* v_config_2784_; lean_object* v_thm_2785_; lean_object* v_instances_2786_; lean_object* v_min_2787_; lean_object* v_detailed_2788_; lean_object* v___x_2789_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; uint8_t v___x_2825_; 
v_counters_2783_ = lean_ctor_get(v_a_2779_, 4);
lean_inc_ref(v_counters_2783_);
lean_dec(v_a_2779_);
v_config_2784_ = lean_ctor_get(v_params_2765_, 0);
lean_inc_ref(v_config_2784_);
lean_dec_ref(v_params_2765_);
v_thm_2785_ = lean_ctor_get(v_counters_2783_, 0);
lean_inc_ref(v_thm_2785_);
lean_dec_ref(v_counters_2783_);
v_instances_2786_ = lean_ctor_get(v_config_2784_, 5);
lean_inc(v_instances_2786_);
v_min_2787_ = lean_ctor_get(v_config_2784_, 15);
lean_inc(v_min_2787_);
v_detailed_2788_ = lean_ctor_get(v_config_2784_, 16);
lean_inc(v_detailed_2788_);
lean_dec_ref(v_config_2784_);
v___x_2789_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(v_thm_2785_);
v___x_2825_ = lean_nat_dec_lt(v_min_2787_, v___x_2789_);
if (v___x_2825_ == 0)
{
lean_dec(v_instances_2786_);
v___y_2797_ = v_a_2766_;
v___y_2798_ = v_a_2767_;
v___y_2799_ = v_a_2768_;
v___y_2800_ = v_a_2769_;
goto v___jp_2796_;
}
else
{
uint8_t v___x_2826_; 
v___x_2826_ = lean_nat_dec_le(v_instances_2786_, v___x_2789_);
lean_dec(v_instances_2786_);
if (v___x_2826_ == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2827_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5);
lean_inc(v_declName_2764_);
v___x_2828_ = l_Lean_MessageData_ofName(v_declName_2764_);
v___x_2829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7);
v___x_2831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2831_, 0, v___x_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
lean_inc(v___x_2789_);
v___x_2832_ = l_Nat_reprFast(v___x_2789_);
v___x_2833_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
v___x_2834_ = l_Lean_MessageData_ofFormat(v___x_2833_);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2831_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
v___x_2838_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2837_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_dec_ref_known(v___x_2838_, 1);
v___y_2797_ = v_a_2766_;
v___y_2798_ = v_a_2767_;
v___y_2799_ = v_a_2768_;
v___y_2800_ = v_a_2769_;
goto v___jp_2796_;
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec(v___x_2789_);
lean_dec(v_detailed_2788_);
lean_dec(v_min_2787_);
lean_dec_ref(v_thm_2785_);
lean_del_object(v___x_2781_);
lean_dec(v_declName_2764_);
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2847_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5);
lean_inc(v_declName_2764_);
v___x_2848_ = l_Lean_MessageData_ofName(v_declName_2764_);
v___x_2849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
v___x_2850_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11);
v___x_2851_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2849_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
lean_inc(v___x_2789_);
v___x_2852_ = l_Nat_reprFast(v___x_2789_);
v___x_2853_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
v___x_2854_ = l_Lean_MessageData_ofFormat(v___x_2853_);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2851_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9);
v___x_2857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
v___x_2858_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2857_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_dec_ref_known(v___x_2858_, 1);
v___y_2797_ = v_a_2766_;
v___y_2798_ = v_a_2767_;
v___y_2799_ = v_a_2768_;
v___y_2800_ = v_a_2769_;
goto v___jp_2796_;
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec(v___x_2789_);
lean_dec(v_detailed_2788_);
lean_dec(v_min_2787_);
lean_dec_ref(v_thm_2785_);
lean_del_object(v___x_2781_);
lean_dec(v_declName_2764_);
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2858_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2858_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
}
v___jp_2790_:
{
uint8_t v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2791_ = lean_nat_dec_lt(v_min_2787_, v___x_2789_);
lean_dec(v___x_2789_);
lean_dec(v_min_2787_);
v___x_2792_ = lean_box(v___x_2791_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2792_);
v___x_2794_ = v___x_2781_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
v___jp_2796_:
{
uint8_t v___x_2801_; 
v___x_2801_ = lean_nat_dec_lt(v_detailed_2788_, v___x_2789_);
lean_dec(v_detailed_2788_);
if (v___x_2801_ == 0)
{
lean_dec_ref(v_thm_2785_);
lean_dec(v_declName_2764_);
goto v___jp_2790_;
}
else
{
lean_object* v___x_2802_; 
v___x_2802_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(v_thm_2785_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec_ref(v_thm_2785_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___x_2804_ = l_Lean_MessageData_ofName(v_declName_2764_);
v___x_2805_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3);
v___x_2806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2804_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
v___x_2807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
lean_ctor_set(v___x_2807_, 1, v_a_2803_);
v___x_2808_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2807_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_dec_ref_known(v___x_2808_, 1);
goto v___jp_2790_;
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v___x_2789_);
lean_dec(v_min_2787_);
lean_del_object(v___x_2781_);
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2808_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2808_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec(v___x_2789_);
lean_dec(v_min_2787_);
lean_del_object(v___x_2781_);
lean_dec(v_declName_2764_);
v_a_2817_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2802_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2802_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v_params_2765_);
lean_dec(v_declName_2764_);
v_a_2868_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2778_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2778_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v_params_2765_);
lean_dec(v_declName_2764_);
v_a_2876_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2776_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2776_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec_ref(v_params_2765_);
lean_dec(v_declName_2764_);
v_a_2884_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2772_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2772_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___boxed(lean_object* v_declName_2892_, lean_object* v_params_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_declName_2892_, v_params_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec_ref(v_a_2894_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_2900_, lean_object* v_name_2901_, uint8_t v_bi_2902_, lean_object* v_type_2903_, lean_object* v_k_2904_, uint8_t v_kind_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2901_, v_bi_2902_, v_type_2903_, v_k_2904_, v_kind_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2912_, lean_object* v_name_2913_, lean_object* v_bi_2914_, lean_object* v_type_2915_, lean_object* v_k_2916_, lean_object* v_kind_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
uint8_t v_bi_boxed_2923_; uint8_t v_kind_boxed_2924_; lean_object* v_res_2925_; 
v_bi_boxed_2923_ = lean_unbox(v_bi_2914_);
v_kind_boxed_2924_ = lean_unbox(v_kind_2917_);
v_res_2925_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(v_00_u03b1_2912_, v_name_2913_, v_bi_boxed_2923_, v_type_2915_, v_k_2916_, v_kind_boxed_2924_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(lean_object* v_00_u03b1_2926_, lean_object* v_name_2927_, lean_object* v_type_2928_, lean_object* v_k_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v___x_2935_; 
v___x_2935_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v_name_2927_, v_type_2928_, v_k_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___boxed(lean_object* v_00_u03b1_2936_, lean_object* v_name_2937_, lean_object* v_type_2938_, lean_object* v_k_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(v_00_u03b1_2936_, v_name_2937_, v_type_2938_, v_k_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg(){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0);
v___x_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg___boxed(lean_object* v___y_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(lean_object* v_00_u03b1_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___boxed(lean_object* v_00_u03b1_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(v_00_u03b1_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(lean_object* v_a_2969_, lean_object* v_as_2970_, size_t v_sz_2971_, size_t v_i_2972_, uint8_t v_b_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
uint8_t v_a_2980_; uint8_t v_addCodeAction_2984_; 
v_addCodeAction_2984_ = lean_usize_dec_lt(v_i_2972_, v_sz_2971_);
if (v_addCodeAction_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
lean_dec_ref(v_a_2969_);
v___x_2985_ = lean_box(v_b_2973_);
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v___x_2985_);
return v___x_2986_;
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_a_2987_ = lean_array_uget_borrowed(v_as_2970_, v_i_2972_);
v___x_2988_ = lean_box(0);
lean_inc(v_a_2987_);
v___x_2989_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_2987_, v___x_2988_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
lean_inc_ref(v_a_2969_);
v___x_2991_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_a_2990_, v_a_2969_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v_a_2992_; uint8_t v___x_2993_; 
v_a_2992_ = lean_ctor_get(v___x_2991_, 0);
lean_inc(v_a_2992_);
lean_dec_ref_known(v___x_2991_, 1);
v___x_2993_ = lean_unbox(v_a_2992_);
lean_dec(v_a_2992_);
if (v___x_2993_ == 0)
{
v_a_2980_ = v_b_2973_;
goto v___jp_2979_;
}
else
{
v_a_2980_ = v_addCodeAction_2984_;
goto v___jp_2979_;
}
}
else
{
lean_dec_ref(v_a_2969_);
return v___x_2991_;
}
}
else
{
lean_object* v_a_2994_; lean_object* v___x_2996_; uint8_t v_isShared_2997_; uint8_t v_isSharedCheck_3001_; 
lean_dec_ref(v_a_2969_);
v_a_2994_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2996_ = v___x_2989_;
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
else
{
lean_inc(v_a_2994_);
lean_dec(v___x_2989_);
v___x_2996_ = lean_box(0);
v_isShared_2997_ = v_isSharedCheck_3001_;
goto v_resetjp_2995_;
}
v_resetjp_2995_:
{
lean_object* v___x_2999_; 
if (v_isShared_2997_ == 0)
{
v___x_2999_ = v___x_2996_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2994_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
}
v___jp_2979_:
{
size_t v___x_2981_; size_t v___x_2982_; 
v___x_2981_ = ((size_t)1ULL);
v___x_2982_ = lean_usize_add(v_i_2972_, v___x_2981_);
v_i_2972_ = v___x_2982_;
v_b_2973_ = v_a_2980_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg___boxed(lean_object* v_a_3002_, lean_object* v_as_3003_, lean_object* v_sz_3004_, lean_object* v_i_3005_, lean_object* v_b_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_){
_start:
{
size_t v_sz_boxed_3012_; size_t v_i_boxed_3013_; uint8_t v_b_boxed_3014_; lean_object* v_res_3015_; 
v_sz_boxed_3012_ = lean_unbox_usize(v_sz_3004_);
lean_dec(v_sz_3004_);
v_i_boxed_3013_ = lean_unbox_usize(v_i_3005_);
lean_dec(v_i_3005_);
v_b_boxed_3014_ = lean_unbox(v_b_3006_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_3002_, v_as_3003_, v_sz_boxed_3012_, v_i_boxed_3013_, v_b_boxed_3014_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_);
lean_dec(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v___y_3008_);
lean_dec_ref(v___y_3007_);
lean_dec_ref(v_as_3003_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(size_t v_sz_3023_, size_t v_i_3024_, lean_object* v_bs_3025_){
_start:
{
uint8_t v___x_3026_; 
v___x_3026_ = lean_usize_dec_lt(v_i_3024_, v_sz_3023_);
if (v___x_3026_ == 0)
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3027_, 0, v_bs_3025_);
return v___x_3027_;
}
else
{
lean_object* v_v_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; 
v_v_3028_ = lean_array_uget(v_bs_3025_, v_i_3024_);
v___x_3029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2));
lean_inc(v_v_3028_);
v___x_3030_ = l_Lean_Syntax_isOfKind(v_v_3028_, v___x_3029_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; 
lean_dec(v_v_3028_);
lean_dec_ref(v_bs_3025_);
v___x_3031_ = lean_box(0);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; lean_object* v_bs_x27_3033_; size_t v___x_3034_; size_t v___x_3035_; lean_object* v___x_3036_; 
v___x_3032_ = lean_unsigned_to_nat(0u);
v_bs_x27_3033_ = lean_array_uset(v_bs_3025_, v_i_3024_, v___x_3032_);
v___x_3034_ = ((size_t)1ULL);
v___x_3035_ = lean_usize_add(v_i_3024_, v___x_3034_);
v___x_3036_ = lean_array_uset(v_bs_x27_3033_, v_i_3024_, v_v_3028_);
v_i_3024_ = v___x_3035_;
v_bs_3025_ = v___x_3036_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___boxed(lean_object* v_sz_3038_, lean_object* v_i_3039_, lean_object* v_bs_3040_){
_start:
{
size_t v_sz_boxed_3041_; size_t v_i_boxed_3042_; lean_object* v_res_3043_; 
v_sz_boxed_3041_ = lean_unbox_usize(v_sz_3038_);
lean_dec(v_sz_3038_);
v_i_boxed_3042_ = lean_unbox_usize(v_i_3039_);
lean_dec(v_i_3039_);
v_res_3043_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_boxed_3041_, v_i_boxed_3042_, v_bs_3040_);
return v_res_3043_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9));
v___x_3060_ = l_String_toRawSubstring_x27(v___x_3059_);
return v___x_3060_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13(void){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Array_mkArray0___redArg();
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(uint8_t v___x_3067_, lean_object* v_stx_3068_, lean_object* v___x_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
if (v___x_3067_ == 0)
{
lean_object* v___x_3077_; 
lean_dec_ref(v___x_3069_);
lean_dec(v_stx_3068_);
v___x_3077_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3077_;
}
else
{
lean_object* v_toCold_3078_; lean_object* v_currRecDepth_3079_; lean_object* v_ref_3080_; uint16_t v_optionFlags_3081_; uint8_t v_suppressElabErrors_3082_; uint8_t v_checkDeprecated_3083_; uint8_t v_isRecordingDeps_3084_; lean_object* v_fileName_3085_; lean_object* v_fileMap_3086_; lean_object* v_options_3087_; lean_object* v_maxRecDepth_3088_; lean_object* v_currNamespace_3089_; lean_object* v_openDecls_3090_; lean_object* v_initHeartbeats_3091_; lean_object* v_quotContext_3092_; lean_object* v_currMacroScope_3093_; lean_object* v_cancelTk_x3f_3094_; lean_object* v_inheritedTraceOptions_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; size_t v_sz_3099_; size_t v___x_3100_; lean_object* v___x_3101_; 
v_toCold_3078_ = lean_ctor_get(v___y_3074_, 0);
v_currRecDepth_3079_ = lean_ctor_get(v___y_3074_, 1);
v_ref_3080_ = lean_ctor_get(v___y_3074_, 2);
v_optionFlags_3081_ = lean_ctor_get_uint16(v___y_3074_, sizeof(void*)*3);
v_suppressElabErrors_3082_ = lean_ctor_get_uint8(v___y_3074_, sizeof(void*)*3 + 2);
v_checkDeprecated_3083_ = lean_ctor_get_uint8(v___y_3074_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3084_ = lean_ctor_get_uint8(v___y_3074_, sizeof(void*)*3 + 4);
v_fileName_3085_ = lean_ctor_get(v_toCold_3078_, 0);
v_fileMap_3086_ = lean_ctor_get(v_toCold_3078_, 1);
v_options_3087_ = lean_ctor_get(v_toCold_3078_, 2);
v_maxRecDepth_3088_ = lean_ctor_get(v_toCold_3078_, 3);
v_currNamespace_3089_ = lean_ctor_get(v_toCold_3078_, 4);
v_openDecls_3090_ = lean_ctor_get(v_toCold_3078_, 5);
v_initHeartbeats_3091_ = lean_ctor_get(v_toCold_3078_, 6);
v_quotContext_3092_ = lean_ctor_get(v_toCold_3078_, 8);
v_currMacroScope_3093_ = lean_ctor_get(v_toCold_3078_, 9);
v_cancelTk_x3f_3094_ = lean_ctor_get(v_toCold_3078_, 10);
v_inheritedTraceOptions_3095_ = lean_ctor_get(v_toCold_3078_, 11);
v___x_3096_ = lean_unsigned_to_nat(2u);
v___x_3097_ = l_Lean_Syntax_getArg(v_stx_3068_, v___x_3096_);
v___x_3098_ = l_Lean_Syntax_getArgs(v___x_3097_);
lean_dec(v___x_3097_);
v_sz_3099_ = lean_array_size(v___x_3098_);
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_3099_, v___x_3100_, v___x_3098_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v___x_3102_; 
lean_dec_ref(v___x_3069_);
lean_dec(v_stx_3068_);
v___x_3102_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3102_;
}
else
{
lean_object* v_val_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v_ids_3109_; lean_object* v___x_3110_; 
v_val_3103_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_val_3103_);
lean_dec_ref_known(v___x_3101_, 1);
v___x_3104_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inheritedTraceOptions_3095_);
lean_inc(v_cancelTk_x3f_3094_);
lean_inc(v_currMacroScope_3093_);
lean_inc(v_quotContext_3092_);
lean_inc(v_initHeartbeats_3091_);
lean_inc(v_openDecls_3090_);
lean_inc(v_currNamespace_3089_);
lean_inc(v_maxRecDepth_3088_);
lean_inc_ref(v_options_3087_);
lean_inc_ref(v_fileMap_3086_);
lean_inc_ref(v_fileName_3085_);
v___x_3105_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3105_, 0, v_fileName_3085_);
lean_ctor_set(v___x_3105_, 1, v_fileMap_3086_);
lean_ctor_set(v___x_3105_, 2, v_options_3087_);
lean_ctor_set(v___x_3105_, 3, v_maxRecDepth_3088_);
lean_ctor_set(v___x_3105_, 4, v_currNamespace_3089_);
lean_ctor_set(v___x_3105_, 5, v_openDecls_3090_);
lean_ctor_set(v___x_3105_, 6, v_initHeartbeats_3091_);
lean_ctor_set(v___x_3105_, 7, v___x_3104_);
lean_ctor_set(v___x_3105_, 8, v_quotContext_3092_);
lean_ctor_set(v___x_3105_, 9, v_currMacroScope_3093_);
lean_ctor_set(v___x_3105_, 10, v_cancelTk_x3f_3094_);
lean_ctor_set(v___x_3105_, 11, v_inheritedTraceOptions_3095_);
lean_inc(v_ref_3080_);
lean_inc(v_currRecDepth_3079_);
v___x_3106_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3106_, 0, v___x_3105_);
lean_ctor_set(v___x_3106_, 1, v_currRecDepth_3079_);
lean_ctor_set(v___x_3106_, 2, v_ref_3080_);
lean_ctor_set_uint16(v___x_3106_, sizeof(void*)*3, v_optionFlags_3081_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*3 + 2, v_suppressElabErrors_3082_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*3 + 3, v_checkDeprecated_3083_);
lean_ctor_set_uint8(v___x_3106_, sizeof(void*)*3 + 4, v_isRecordingDeps_3084_);
v___x_3107_ = lean_unsigned_to_nat(3u);
v___x_3108_ = l_Lean_Syntax_getArg(v_stx_3068_, v___x_3107_);
v_ids_3109_ = l_Lean_Syntax_getArgs(v___x_3108_);
lean_dec(v___x_3108_);
v___x_3110_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_val_3103_, v___y_3070_, v___x_3106_, v___y_3075_);
if (lean_obj_tag(v___x_3110_) == 0)
{
lean_object* v_a_3111_; lean_object* v___x_3112_; 
v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc(v_a_3111_);
lean_dec_ref_known(v___x_3110_, 1);
v___x_3112_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_a_3111_, v___y_3072_, v___y_3073_, v___x_3106_, v___y_3075_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; uint8_t v___x_3114_; size_t v_sz_3115_; lean_object* v___x_3116_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v___x_3114_ = 0;
v_sz_3115_ = lean_array_size(v_ids_3109_);
v___x_3116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_3113_, v_ids_3109_, v_sz_3115_, v___x_3100_, v___x_3114_, v___y_3072_, v___y_3073_, v___x_3106_, v___y_3075_);
lean_dec_ref(v_ids_3109_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3165_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3119_ = v___x_3116_;
v_isShared_3120_ = v_isSharedCheck_3165_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___x_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3165_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_unbox(v_a_3117_);
lean_dec(v_a_3117_);
if (v___x_3121_ == 0)
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
lean_dec_ref_known(v___x_3106_, 3);
lean_dec_ref(v___x_3069_);
lean_dec(v_stx_3068_);
v___x_3122_ = lean_box(0);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3122_);
v___x_3124_ = v___x_3119_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
else
{
lean_object* v___x_3126_; lean_object* v_map_3127_; lean_object* v___x_3128_; uint8_t v___y_3130_; lean_object* v___x_3158_; 
v___x_3126_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___x_3106_);
v_map_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_map_3127_);
lean_dec_ref(v___x_3126_);
v___x_3128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3));
v___x_3158_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3127_, v___x_3128_);
lean_dec(v_map_3127_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_del_object(v___x_3119_);
v___y_3130_ = v___x_3114_;
goto v___jp_3129_;
}
else
{
lean_object* v_val_3159_; 
v_val_3159_ = lean_ctor_get(v___x_3158_, 0);
lean_inc(v_val_3159_);
lean_dec_ref_known(v___x_3158_, 1);
if (lean_obj_tag(v_val_3159_) == 1)
{
uint8_t v_v_3160_; 
v_v_3160_ = lean_ctor_get_uint8(v_val_3159_, 0);
lean_dec_ref_known(v_val_3159_, 0);
if (v_v_3160_ == 0)
{
lean_del_object(v___x_3119_);
v___y_3130_ = v_v_3160_;
goto v___jp_3129_;
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3163_; 
lean_dec_ref_known(v___x_3106_, 3);
lean_dec_ref(v___x_3069_);
lean_dec(v_stx_3068_);
v___x_3161_ = lean_box(0);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v___x_3161_);
v___x_3163_ = v___x_3119_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3161_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
else
{
lean_dec(v_val_3159_);
lean_del_object(v___x_3119_);
v___y_3130_ = v___x_3114_;
goto v___jp_3129_;
}
}
v___jp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3131_ = l_Lean_SourceInfo_fromRef(v_ref_3080_, v___y_3130_);
v___x_3132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5));
v___x_3133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0));
v___x_3134_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6));
v___x_3135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7));
lean_inc_ref(v___x_3069_);
v___x_3136_ = l_Lean_Name_mkStr4(v___x_3069_, v___x_3133_, v___x_3134_, v___x_3135_);
v___x_3137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8));
v___x_3138_ = l_Lean_Name_mkStr4(v___x_3069_, v___x_3133_, v___x_3134_, v___x_3137_);
lean_inc_n(v___x_3131_, 6);
v___x_3139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3131_);
lean_ctor_set(v___x_3139_, 1, v___x_3137_);
v___x_3140_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10);
v___x_3141_ = lean_box(0);
v___x_3142_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3131_);
lean_ctor_set(v___x_3142_, 1, v___x_3140_);
lean_ctor_set(v___x_3142_, 2, v___x_3128_);
lean_ctor_set(v___x_3142_, 3, v___x_3141_);
v___x_3143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12));
v___x_3144_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13);
v___x_3145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3131_);
lean_ctor_set(v___x_3145_, 1, v___x_3143_);
lean_ctor_set(v___x_3145_, 2, v___x_3144_);
v___x_3146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14));
v___x_3147_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3131_);
lean_ctor_set(v___x_3147_, 1, v___x_3146_);
v___x_3148_ = l_Lean_Syntax_node4(v___x_3131_, v___x_3138_, v___x_3139_, v___x_3142_, v___x_3145_, v___x_3147_);
v___x_3149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3131_);
lean_ctor_set(v___x_3149_, 1, v___x_3135_);
lean_inc(v_stx_3068_);
v___x_3150_ = l_Lean_Syntax_node3(v___x_3131_, v___x_3136_, v___x_3148_, v___x_3149_, v_stx_3068_);
v___x_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3132_);
lean_ctor_set(v___x_3151_, 1, v___x_3150_);
v___x_3152_ = lean_box(0);
v___x_3153_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3151_);
lean_ctor_set(v___x_3153_, 1, v___x_3152_);
lean_ctor_set(v___x_3153_, 2, v___x_3152_);
lean_ctor_set(v___x_3153_, 3, v___x_3152_);
lean_ctor_set(v___x_3153_, 4, v___x_3152_);
lean_ctor_set(v___x_3153_, 5, v___x_3152_);
v___x_3154_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15));
v___x_3155_ = 4;
v___x_3156_ = l_Lean_MessageData_nil;
v___x_3157_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_3068_, v___x_3153_, v___x_3152_, v___x_3154_, v___x_3152_, v___x_3155_, v___x_3156_, v___x_3106_, v___y_3075_);
lean_dec_ref_known(v___x_3106_, 3);
return v___x_3157_;
}
}
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec_ref_known(v___x_3106_, 3);
lean_dec_ref(v___x_3069_);
lean_dec(v_stx_3068_);
v_a_3166_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3116_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3116_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec_ref(v_ids_3109_);
lean_dec_ref_known(v___x_3106_, 3);
lean_dec_ref(v___x_3069_);
lean_dec(v_stx_3068_);
v_a_3174_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3112_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3112_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
lean_dec_ref(v_ids_3109_);
lean_dec_ref_known(v___x_3106_, 3);
lean_dec_ref(v___x_3069_);
lean_dec(v_stx_3068_);
v_a_3182_ = lean_ctor_get(v___x_3110_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3110_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3110_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3110_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed(lean_object* v___x_3190_, lean_object* v_stx_3191_, lean_object* v___x_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
uint8_t v___x_5625__boxed_3200_; lean_object* v_res_3201_; 
v___x_5625__boxed_3200_ = lean_unbox(v___x_3190_);
v_res_3201_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(v___x_5625__boxed_3200_, v_stx_3191_, v___x_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(lean_object* v_stx_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; lean_object* v___x_3214_; lean_object* v___f_3215_; lean_object* v___x_3216_; 
v___x_3211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_3212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1));
lean_inc(v_stx_3207_);
v___x_3213_ = l_Lean_Syntax_isOfKind(v_stx_3207_, v___x_3212_);
v___x_3214_ = lean_box(v___x_3213_);
v___f_3215_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3215_, 0, v___x_3214_);
lean_closure_set(v___f_3215_, 1, v_stx_3207_);
lean_closure_set(v___f_3215_, 2, v___x_3211_);
v___x_3216_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3215_, v_a_3208_, v_a_3209_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed(lean_object* v_stx_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(v_stx_3217_, v_a_3218_, v_a_3219_);
lean_dec(v_a_3219_);
lean_dec_ref(v_a_3218_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(lean_object* v_a_3222_, lean_object* v_as_3223_, size_t v_sz_3224_, size_t v_i_3225_, uint8_t v_b_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_3222_, v_as_3223_, v_sz_3224_, v_i_3225_, v_b_3226_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___boxed(lean_object* v_a_3235_, lean_object* v_as_3236_, lean_object* v_sz_3237_, lean_object* v_i_3238_, lean_object* v_b_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_){
_start:
{
size_t v_sz_boxed_3247_; size_t v_i_boxed_3248_; uint8_t v_b_boxed_3249_; lean_object* v_res_3250_; 
v_sz_boxed_3247_ = lean_unbox_usize(v_sz_3237_);
lean_dec(v_sz_3237_);
v_i_boxed_3248_ = lean_unbox_usize(v_i_3238_);
lean_dec(v_i_3238_);
v_b_boxed_3249_ = lean_unbox(v_b_3239_);
v_res_3250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(v_a_3235_, v_as_3236_, v_sz_boxed_3247_, v_i_boxed_3248_, v_b_boxed_3249_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec_ref(v_as_3236_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1(){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3256_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3257_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1));
v___x_3258_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1));
v___x_3259_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed), 4, 0);
v___x_3260_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3256_, v___x_3257_, v___x_3258_, v___x_3259_);
return v___x_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___boxed(lean_object* v_a_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1();
return v_res_3262_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(lean_object* v_name_3263_, lean_object* v_suff_3264_){
_start:
{
if (lean_obj_tag(v_name_3263_) == 1)
{
lean_object* v_str_3265_; uint8_t v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; uint8_t v___x_3270_; 
v_str_3265_ = lean_ctor_get(v_name_3263_, 1);
v___x_3266_ = 1;
v___x_3267_ = l_Lean_Name_toString(v_suff_3264_, v___x_3266_);
v___x_3268_ = lean_string_utf8_byte_size(v_str_3265_);
v___x_3269_ = lean_string_utf8_byte_size(v___x_3267_);
v___x_3270_ = lean_nat_dec_le(v___x_3269_, v___x_3268_);
if (v___x_3270_ == 0)
{
lean_dec_ref(v___x_3267_);
return v___x_3270_;
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3271_ = lean_unsigned_to_nat(0u);
v___x_3272_ = lean_nat_sub(v___x_3268_, v___x_3269_);
v___x_3273_ = lean_string_memcmp(v_str_3265_, v___x_3267_, v___x_3272_, v___x_3271_, v___x_3269_);
lean_dec(v___x_3272_);
lean_dec_ref(v___x_3267_);
return v___x_3273_;
}
}
else
{
uint8_t v___x_3274_; 
lean_dec(v_suff_3264_);
v___x_3274_ = 0;
return v___x_3274_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix___boxed(lean_object* v_name_3275_, lean_object* v_suff_3276_){
_start:
{
uint8_t v_res_3277_; lean_object* v_r_3278_; 
v_res_3277_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(v_name_3275_, v_suff_3276_);
lean_dec(v_name_3275_);
v_r_3278_ = lean_box(v_res_3277_);
return v_r_3278_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(lean_object* v___x_3279_, lean_object* v_as_3280_, size_t v_i_3281_, size_t v_stop_3282_){
_start:
{
uint8_t v___x_3283_; 
v___x_3283_ = lean_usize_dec_eq(v_i_3281_, v_stop_3282_);
if (v___x_3283_ == 0)
{
lean_object* v___x_3284_; uint8_t v___x_3285_; 
v___x_3284_ = lean_array_uget_borrowed(v_as_3280_, v_i_3281_);
v___x_3285_ = l_Lean_Name_isPrefixOf(v___x_3284_, v___x_3279_);
if (v___x_3285_ == 0)
{
size_t v___x_3286_; size_t v___x_3287_; 
v___x_3286_ = ((size_t)1ULL);
v___x_3287_ = lean_usize_add(v_i_3281_, v___x_3286_);
v_i_3281_ = v___x_3287_;
goto _start;
}
else
{
return v___x_3285_;
}
}
else
{
uint8_t v___x_3289_; 
v___x_3289_ = 0;
return v___x_3289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1___boxed(lean_object* v___x_3290_, lean_object* v_as_3291_, lean_object* v_i_3292_, lean_object* v_stop_3293_){
_start:
{
size_t v_i_boxed_3294_; size_t v_stop_boxed_3295_; uint8_t v_res_3296_; lean_object* v_r_3297_; 
v_i_boxed_3294_ = lean_unbox_usize(v_i_3292_);
lean_dec(v_i_3292_);
v_stop_boxed_3295_ = lean_unbox_usize(v_stop_3293_);
lean_dec(v_stop_3293_);
v_res_3296_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(v___x_3290_, v_as_3291_, v_i_boxed_3294_, v_stop_boxed_3295_);
lean_dec_ref(v_as_3291_);
lean_dec(v___x_3290_);
v_r_3297_ = lean_box(v_res_3296_);
return v_r_3297_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(lean_object* v_declName_3301_, lean_object* v_init_3302_, lean_object* v_x_3303_){
_start:
{
if (lean_obj_tag(v_x_3303_) == 0)
{
lean_object* v_k_3304_; lean_object* v_l_3305_; lean_object* v_r_3306_; lean_object* v___x_3307_; 
v_k_3304_ = lean_ctor_get(v_x_3303_, 1);
lean_inc(v_k_3304_);
v_l_3305_ = lean_ctor_get(v_x_3303_, 3);
lean_inc(v_l_3305_);
v_r_3306_ = lean_ctor_get(v_x_3303_, 4);
lean_inc(v_r_3306_);
lean_dec_ref_known(v_x_3303_, 5);
v___x_3307_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3301_, v_init_3302_, v_l_3305_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_dec(v_r_3306_);
lean_dec(v_k_3304_);
return v___x_3307_;
}
else
{
lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3321_; 
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3307_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; 
v_unused_3322_ = lean_ctor_get(v___x_3307_, 0);
lean_dec(v_unused_3322_);
v___x_3309_ = v___x_3307_;
v_isShared_3310_ = v_isSharedCheck_3321_;
goto v_resetjp_3308_;
}
else
{
lean_dec(v___x_3307_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3321_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3311_ = lean_box(0);
v___x_3312_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(v_declName_3301_, v_k_3304_);
if (v___x_3312_ == 0)
{
lean_object* v___x_3313_; 
lean_del_object(v___x_3309_);
v___x_3313_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0));
v_init_3302_ = v___x_3313_;
v_x_3303_ = v_r_3306_;
goto _start;
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3319_; 
lean_dec(v_r_3306_);
v___x_3315_ = lean_box(v___x_3312_);
v___x_3316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
v___x_3317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v___x_3311_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set_tag(v___x_3309_, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3317_);
v___x_3319_ = v___x_3309_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
else
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3323_, 0, v_init_3302_);
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___boxed(lean_object* v_declName_3324_, lean_object* v_init_3325_, lean_object* v_x_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3324_, v_init_3325_, v_x_3326_);
lean_dec(v_declName_3324_);
return v_res_3327_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(lean_object* v_declName_3331_, lean_object* v_as_3332_, size_t v_i_3333_, size_t v_stop_3334_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = lean_usize_dec_eq(v_i_3333_, v_stop_3334_);
if (v___x_3335_ == 0)
{
uint8_t v___x_3336_; uint8_t v___y_3338_; lean_object* v___x_3342_; lean_object* v___x_3343_; uint8_t v___x_3344_; 
v___x_3336_ = 1;
v___x_3342_ = lean_array_uget_borrowed(v_as_3332_, v_i_3333_);
v___x_3343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1));
v___x_3344_ = lean_name_eq(v___x_3342_, v___x_3343_);
if (v___x_3344_ == 0)
{
uint8_t v___x_3345_; 
v___x_3345_ = l_Lean_Name_isPrefixOf(v___x_3342_, v_declName_3331_);
v___y_3338_ = v___x_3345_;
goto v___jp_3337_;
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
lean_inc(v_declName_3331_);
v___x_3346_ = l_Lean_Name_components(v_declName_3331_);
v___x_3347_ = l_List_lengthTR___redArg(v___x_3346_);
lean_dec(v___x_3346_);
v___x_3348_ = lean_unsigned_to_nat(1u);
v___x_3349_ = lean_nat_dec_eq(v___x_3347_, v___x_3348_);
lean_dec(v___x_3347_);
v___y_3338_ = v___x_3349_;
goto v___jp_3337_;
}
v___jp_3337_:
{
if (v___y_3338_ == 0)
{
size_t v___x_3339_; size_t v___x_3340_; 
v___x_3339_ = ((size_t)1ULL);
v___x_3340_ = lean_usize_add(v_i_3333_, v___x_3339_);
v_i_3333_ = v___x_3340_;
goto _start;
}
else
{
lean_dec(v_declName_3331_);
return v___x_3336_;
}
}
}
else
{
uint8_t v___x_3350_; 
lean_dec(v_declName_3331_);
v___x_3350_ = 0;
return v___x_3350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___boxed(lean_object* v_declName_3351_, lean_object* v_as_3352_, lean_object* v_i_3353_, lean_object* v_stop_3354_){
_start:
{
size_t v_i_boxed_3355_; size_t v_stop_boxed_3356_; uint8_t v_res_3357_; lean_object* v_r_3358_; 
v_i_boxed_3355_ = lean_unbox_usize(v_i_3353_);
lean_dec(v_i_3353_);
v_stop_boxed_3356_ = lean_unbox_usize(v_stop_3354_);
lean_dec(v_stop_3354_);
v_res_3357_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(v_declName_3351_, v_as_3352_, v_i_boxed_3355_, v_stop_boxed_3356_);
lean_dec_ref(v_as_3352_);
v_r_3358_ = lean_box(v_res_3357_);
return v_r_3358_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(lean_object* v_prefixes_x3f_3359_, uint8_t v_inModule_3360_, lean_object* v___x_3361_, lean_object* v___x_3362_, lean_object* v___x_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_){
_start:
{
if (lean_obj_tag(v_a_3364_) == 0)
{
lean_object* v___x_3366_; 
lean_dec(v___x_3363_);
v___x_3366_ = lean_array_to_list(v_a_3365_);
return v___x_3366_;
}
else
{
lean_object* v_head_3367_; lean_object* v_tail_3368_; lean_object* v_val_3370_; 
v_head_3367_ = lean_ctor_get(v_a_3364_, 0);
lean_inc(v_head_3367_);
v_tail_3368_ = lean_ctor_get(v_a_3364_, 1);
lean_inc(v_tail_3368_);
lean_dec_ref_known(v_a_3364_, 2);
if (lean_obj_tag(v_head_3367_) == 0)
{
lean_object* v_declName_3373_; uint8_t v___x_3374_; 
v_declName_3373_ = lean_ctor_get(v_head_3367_, 0);
lean_inc(v_declName_3373_);
lean_dec_ref_known(v_head_3367_, 1);
v___x_3374_ = l_Lean_NameSet_contains(v___x_3362_, v_declName_3373_);
if (v___x_3374_ == 0)
{
lean_object* v___x_3375_; lean_object* v___y_3404_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v_a_3411_; 
v___x_3375_ = lean_box(0);
v___x_3409_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0));
lean_inc(v___x_3363_);
v___x_3410_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3373_, v___x_3409_, v___x_3363_);
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
lean_inc(v_a_3411_);
lean_dec_ref(v___x_3410_);
v___y_3404_ = v_a_3411_;
goto v___jp_3403_;
v___jp_3376_:
{
if (lean_obj_tag(v_prefixes_x3f_3359_) == 1)
{
if (v_inModule_3360_ == 0)
{
lean_object* v_val_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v_val_3377_ = lean_ctor_get(v_prefixes_x3f_3359_, 0);
v___x_3378_ = lean_unsigned_to_nat(0u);
v___x_3379_ = lean_array_get_size(v_val_3377_);
v___x_3380_ = lean_nat_dec_lt(v___x_3378_, v___x_3379_);
if (v___x_3380_ == 0)
{
lean_dec(v_declName_3373_);
v_a_3364_ = v_tail_3368_;
goto _start;
}
else
{
if (v___x_3380_ == 0)
{
lean_dec(v_declName_3373_);
v_a_3364_ = v_tail_3368_;
goto _start;
}
else
{
size_t v___x_3383_; size_t v___x_3384_; uint8_t v___x_3385_; 
v___x_3383_ = ((size_t)0ULL);
v___x_3384_ = lean_usize_of_nat(v___x_3379_);
lean_inc(v_declName_3373_);
v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(v_declName_3373_, v_val_3377_, v___x_3383_, v___x_3384_);
if (v___x_3385_ == 0)
{
lean_dec(v_declName_3373_);
v_a_3364_ = v_tail_3368_;
goto _start;
}
else
{
v_val_3370_ = v_declName_3373_;
goto v___jp_3369_;
}
}
}
}
else
{
lean_object* v_val_3387_; lean_object* v___x_3388_; 
v_val_3387_ = lean_ctor_get(v_prefixes_x3f_3359_, 0);
v___x_3388_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3361_, v_declName_3373_);
if (lean_obj_tag(v___x_3388_) == 1)
{
lean_object* v_val_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v_val_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_val_3389_);
lean_dec_ref_known(v___x_3388_, 1);
v___x_3390_ = lean_unsigned_to_nat(0u);
v___x_3391_ = lean_array_get_size(v_val_3387_);
v___x_3392_ = lean_nat_dec_lt(v___x_3390_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_dec(v_val_3389_);
lean_dec(v_declName_3373_);
v_a_3364_ = v_tail_3368_;
goto _start;
}
else
{
lean_object* v___x_3394_; 
v___x_3394_ = l_Lean_Environment_header(v___x_3361_);
if (v___x_3392_ == 0)
{
lean_dec_ref(v___x_3394_);
lean_dec(v_val_3389_);
lean_dec(v_declName_3373_);
v_a_3364_ = v_tail_3368_;
goto _start;
}
else
{
lean_object* v_moduleNames_3396_; lean_object* v___x_3397_; size_t v___x_3398_; size_t v___x_3399_; uint8_t v___x_3400_; 
v_moduleNames_3396_ = lean_ctor_get(v___x_3394_, 4);
lean_inc_ref(v_moduleNames_3396_);
lean_dec_ref(v___x_3394_);
v___x_3397_ = lean_array_get(v___x_3375_, v_moduleNames_3396_, v_val_3389_);
lean_dec(v_val_3389_);
lean_dec_ref(v_moduleNames_3396_);
v___x_3398_ = ((size_t)0ULL);
v___x_3399_ = lean_usize_of_nat(v___x_3391_);
v___x_3400_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(v___x_3397_, v_val_3387_, v___x_3398_, v___x_3399_);
lean_dec(v___x_3397_);
if (v___x_3400_ == 0)
{
lean_dec(v_declName_3373_);
v_a_3364_ = v_tail_3368_;
goto _start;
}
else
{
v_val_3370_ = v_declName_3373_;
goto v___jp_3369_;
}
}
}
}
else
{
lean_dec(v___x_3388_);
lean_dec(v_declName_3373_);
v_a_3364_ = v_tail_3368_;
goto _start;
}
}
}
else
{
v_val_3370_ = v_declName_3373_;
goto v___jp_3369_;
}
}
v___jp_3403_:
{
lean_object* v_fst_3405_; 
v_fst_3405_ = lean_ctor_get(v___y_3404_, 0);
lean_inc(v_fst_3405_);
lean_dec_ref(v___y_3404_);
if (lean_obj_tag(v_fst_3405_) == 0)
{
goto v___jp_3376_;
}
else
{
lean_object* v_val_3406_; uint8_t v___x_3407_; 
v_val_3406_ = lean_ctor_get(v_fst_3405_, 0);
lean_inc(v_val_3406_);
lean_dec_ref_known(v_fst_3405_, 1);
v___x_3407_ = lean_unbox(v_val_3406_);
lean_dec(v_val_3406_);
if (v___x_3407_ == 0)
{
goto v___jp_3376_;
}
else
{
lean_dec(v_declName_3373_);
v_a_3364_ = v_tail_3368_;
goto _start;
}
}
}
}
else
{
lean_dec(v_declName_3373_);
v_a_3364_ = v_tail_3368_;
goto _start;
}
}
else
{
lean_dec(v_head_3367_);
v_a_3364_ = v_tail_3368_;
goto _start;
}
v___jp_3369_:
{
lean_object* v___x_3371_; 
v___x_3371_ = lean_array_push(v_a_3365_, v_val_3370_);
v_a_3364_ = v_tail_3368_;
v_a_3365_ = v___x_3371_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3___boxed(lean_object* v_prefixes_x3f_3414_, lean_object* v_inModule_3415_, lean_object* v___x_3416_, lean_object* v___x_3417_, lean_object* v___x_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
uint8_t v_inModule_boxed_3421_; lean_object* v_res_3422_; 
v_inModule_boxed_3421_ = lean_unbox(v_inModule_3415_);
v_res_3422_ = l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(v_prefixes_x3f_3414_, v_inModule_boxed_3421_, v___x_3416_, v___x_3417_, v___x_3418_, v_a_3419_, v_a_3420_);
lean_dec(v___x_3417_);
lean_dec_ref(v___x_3416_);
lean_dec(v_prefixes_x3f_3414_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(lean_object* v_prefixes_x3f_3425_, uint8_t v_inModule_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v_env_3431_; lean_object* v___x_3432_; lean_object* v_toEnvExtension_3433_; lean_object* v_asyncMode_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v_env_3438_; lean_object* v___x_3439_; lean_object* v_toEnvExtension_3440_; lean_object* v_asyncMode_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v___x_3429_ = lean_box(1);
v___x_3430_ = lean_st_ref_get(v_a_3427_);
v_env_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc_ref(v_env_3431_);
lean_dec(v___x_3430_);
v___x_3432_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_3433_ = lean_ctor_get(v___x_3432_, 0);
v_asyncMode_3434_ = lean_ctor_get(v_toEnvExtension_3433_, 2);
v___x_3435_ = lean_box(0);
v___x_3436_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3429_, v___x_3432_, v_env_3431_, v_asyncMode_3434_, v___x_3435_);
v___x_3437_ = lean_st_ref_get(v_a_3427_);
v_env_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc_ref(v_env_3438_);
lean_dec(v___x_3437_);
v___x_3439_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_3440_ = lean_ctor_get(v___x_3439_, 0);
v_asyncMode_3441_ = lean_ctor_get(v_toEnvExtension_3440_, 2);
v___x_3442_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3429_, v___x_3439_, v_env_3438_, v_asyncMode_3441_, v___x_3435_);
v___x_3443_ = l_Lean_Meta_Grind_grindExt;
v___x_3444_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3443_, v_a_3427_);
if (lean_obj_tag(v___x_3444_) == 0)
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3457_; 
v_a_3445_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3447_ = v___x_3444_;
v_isShared_3448_ = v_isSharedCheck_3457_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3444_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3457_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v_env_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3455_; 
v___x_3449_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_a_3445_);
lean_dec(v_a_3445_);
v___x_3450_ = lean_st_ref_get(v_a_3427_);
v_env_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc_ref(v_env_3451_);
lean_dec(v___x_3450_);
v___x_3452_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0));
v___x_3453_ = l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(v_prefixes_x3f_3425_, v_inModule_3426_, v_env_3451_, v___x_3436_, v___x_3442_, v___x_3449_, v___x_3452_);
lean_dec(v___x_3436_);
lean_dec_ref(v_env_3451_);
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v___x_3453_);
v___x_3455_ = v___x_3447_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
return v___x_3455_;
}
}
}
else
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_dec(v___x_3442_);
lean_dec(v___x_3436_);
v_a_3458_ = lean_ctor_get(v___x_3444_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3444_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3444_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___boxed(lean_object* v_prefixes_x3f_3466_, lean_object* v_inModule_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
uint8_t v_inModule_boxed_3470_; lean_object* v_res_3471_; 
v_inModule_boxed_3470_ = lean_unbox(v_inModule_3467_);
v_res_3471_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v_prefixes_x3f_3466_, v_inModule_boxed_3470_, v_a_3468_);
lean_dec(v_a_3468_);
lean_dec(v_prefixes_x3f_3466_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(lean_object* v_prefixes_x3f_3472_, uint8_t v_inModule_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v_prefixes_x3f_3472_, v_inModule_3473_, v_a_3475_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___boxed(lean_object* v_prefixes_x3f_3478_, lean_object* v_inModule_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
uint8_t v_inModule_boxed_3483_; lean_object* v_res_3484_; 
v_inModule_boxed_3483_ = lean_unbox(v_inModule_3479_);
v_res_3484_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(v_prefixes_x3f_3478_, v_inModule_boxed_3483_, v_a_3480_, v_a_3481_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_prefixes_x3f_3478_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(size_t v_sz_3485_, size_t v_i_3486_, lean_object* v_bs_3487_){
_start:
{
uint8_t v___x_3488_; 
v___x_3488_ = lean_usize_dec_lt(v_i_3486_, v_sz_3485_);
if (v___x_3488_ == 0)
{
return v_bs_3487_;
}
else
{
lean_object* v_v_3489_; lean_object* v___x_3490_; lean_object* v_bs_x27_3491_; lean_object* v___x_3492_; size_t v___x_3493_; size_t v___x_3494_; lean_object* v___x_3495_; 
v_v_3489_ = lean_array_uget(v_bs_3487_, v_i_3486_);
v___x_3490_ = lean_unsigned_to_nat(0u);
v_bs_x27_3491_ = lean_array_uset(v_bs_3487_, v_i_3486_, v___x_3490_);
v___x_3492_ = l_Lean_TSyntax_getId(v_v_3489_);
lean_dec(v_v_3489_);
v___x_3493_ = ((size_t)1ULL);
v___x_3494_ = lean_usize_add(v_i_3486_, v___x_3493_);
v___x_3495_ = lean_array_uset(v_bs_x27_3491_, v_i_3486_, v___x_3492_);
v_i_3486_ = v___x_3494_;
v_bs_3487_ = v___x_3495_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4___boxed(lean_object* v_sz_3497_, lean_object* v_i_3498_, lean_object* v_bs_3499_){
_start:
{
size_t v_sz_boxed_3500_; size_t v_i_boxed_3501_; lean_object* v_res_3502_; 
v_sz_boxed_3500_ = lean_unbox_usize(v_sz_3497_);
lean_dec(v_sz_3497_);
v_i_boxed_3501_ = lean_unbox_usize(v_i_3498_);
lean_dec(v_i_3498_);
v_res_3502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(v_sz_boxed_3500_, v_i_boxed_3501_, v_bs_3499_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(lean_object* v_hi_3503_, lean_object* v_pivot_3504_, lean_object* v_as_3505_, lean_object* v_i_3506_, lean_object* v_k_3507_){
_start:
{
uint8_t v___x_3508_; 
v___x_3508_ = lean_nat_dec_lt(v_k_3507_, v_hi_3503_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_dec(v_k_3507_);
v___x_3509_ = lean_array_fswap(v_as_3505_, v_i_3506_, v_hi_3503_);
v___x_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3510_, 0, v_i_3506_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
return v___x_3510_;
}
else
{
lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3511_ = lean_array_fget_borrowed(v_as_3505_, v_k_3507_);
v___x_3512_ = l_Lean_Name_lt(v___x_3511_, v_pivot_3504_);
if (v___x_3512_ == 0)
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3513_ = lean_unsigned_to_nat(1u);
v___x_3514_ = lean_nat_add(v_k_3507_, v___x_3513_);
lean_dec(v_k_3507_);
v_k_3507_ = v___x_3514_;
goto _start;
}
else
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3516_ = lean_array_fswap(v_as_3505_, v_i_3506_, v_k_3507_);
v___x_3517_ = lean_unsigned_to_nat(1u);
v___x_3518_ = lean_nat_add(v_i_3506_, v___x_3517_);
lean_dec(v_i_3506_);
v___x_3519_ = lean_nat_add(v_k_3507_, v___x_3517_);
lean_dec(v_k_3507_);
v_as_3505_ = v___x_3516_;
v_i_3506_ = v___x_3518_;
v_k_3507_ = v___x_3519_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg___boxed(lean_object* v_hi_3521_, lean_object* v_pivot_3522_, lean_object* v_as_3523_, lean_object* v_i_3524_, lean_object* v_k_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_3521_, v_pivot_3522_, v_as_3523_, v_i_3524_, v_k_3525_);
lean_dec(v_pivot_3522_);
lean_dec(v_hi_3521_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(lean_object* v_n_3527_, lean_object* v_as_3528_, lean_object* v_lo_3529_, lean_object* v_hi_3530_){
_start:
{
lean_object* v___y_3532_; uint8_t v___x_3542_; 
v___x_3542_ = lean_nat_dec_lt(v_lo_3529_, v_hi_3530_);
if (v___x_3542_ == 0)
{
lean_dec(v_lo_3529_);
return v_as_3528_;
}
else
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v_mid_3545_; lean_object* v___y_3547_; lean_object* v___y_3553_; lean_object* v___x_3558_; lean_object* v___x_3559_; uint8_t v___x_3560_; 
v___x_3543_ = lean_nat_add(v_lo_3529_, v_hi_3530_);
v___x_3544_ = lean_unsigned_to_nat(1u);
v_mid_3545_ = lean_nat_shiftr(v___x_3543_, v___x_3544_);
lean_dec(v___x_3543_);
v___x_3558_ = lean_array_fget_borrowed(v_as_3528_, v_mid_3545_);
v___x_3559_ = lean_array_fget_borrowed(v_as_3528_, v_lo_3529_);
v___x_3560_ = l_Lean_Name_lt(v___x_3558_, v___x_3559_);
if (v___x_3560_ == 0)
{
v___y_3553_ = v_as_3528_;
goto v___jp_3552_;
}
else
{
lean_object* v___x_3561_; 
v___x_3561_ = lean_array_fswap(v_as_3528_, v_lo_3529_, v_mid_3545_);
v___y_3553_ = v___x_3561_;
goto v___jp_3552_;
}
v___jp_3546_:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; uint8_t v___x_3550_; 
v___x_3548_ = lean_array_fget_borrowed(v___y_3547_, v_mid_3545_);
v___x_3549_ = lean_array_fget_borrowed(v___y_3547_, v_hi_3530_);
v___x_3550_ = l_Lean_Name_lt(v___x_3548_, v___x_3549_);
if (v___x_3550_ == 0)
{
lean_dec(v_mid_3545_);
v___y_3532_ = v___y_3547_;
goto v___jp_3531_;
}
else
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_array_fswap(v___y_3547_, v_mid_3545_, v_hi_3530_);
lean_dec(v_mid_3545_);
v___y_3532_ = v___x_3551_;
goto v___jp_3531_;
}
}
v___jp_3552_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v___x_3554_ = lean_array_fget_borrowed(v___y_3553_, v_hi_3530_);
v___x_3555_ = lean_array_fget_borrowed(v___y_3553_, v_lo_3529_);
v___x_3556_ = l_Lean_Name_lt(v___x_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
v___y_3547_ = v___y_3553_;
goto v___jp_3546_;
}
else
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_array_fswap(v___y_3553_, v_lo_3529_, v_hi_3530_);
v___y_3547_ = v___x_3557_;
goto v___jp_3546_;
}
}
}
v___jp_3531_:
{
lean_object* v_pivot_3533_; lean_object* v___x_3534_; lean_object* v_fst_3535_; lean_object* v_snd_3536_; uint8_t v___x_3537_; 
v_pivot_3533_ = lean_array_fget(v___y_3532_, v_hi_3530_);
lean_inc_n(v_lo_3529_, 2);
v___x_3534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_3530_, v_pivot_3533_, v___y_3532_, v_lo_3529_, v_lo_3529_);
lean_dec(v_pivot_3533_);
v_fst_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_fst_3535_);
v_snd_3536_ = lean_ctor_get(v___x_3534_, 1);
lean_inc(v_snd_3536_);
lean_dec_ref(v___x_3534_);
v___x_3537_ = lean_nat_dec_le(v_hi_3530_, v_fst_3535_);
if (v___x_3537_ == 0)
{
lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_3527_, v_snd_3536_, v_lo_3529_, v_fst_3535_);
v___x_3539_ = lean_unsigned_to_nat(1u);
v___x_3540_ = lean_nat_add(v_fst_3535_, v___x_3539_);
lean_dec(v_fst_3535_);
v_as_3528_ = v___x_3538_;
v_lo_3529_ = v___x_3540_;
goto _start;
}
else
{
lean_dec(v_fst_3535_);
lean_dec(v_lo_3529_);
return v_snd_3536_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg___boxed(lean_object* v_n_3562_, lean_object* v_as_3563_, lean_object* v_lo_3564_, lean_object* v_hi_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_3562_, v_as_3563_, v_lo_3564_, v_hi_3565_);
lean_dec(v_hi_3565_);
lean_dec(v_n_3562_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3567_, lean_object* v_msgData_3568_, uint8_t v_severity_3569_, uint8_t v_isSilent_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; uint8_t v___y_3582_; uint8_t v___y_3583_; lean_object* v_toCold_3584_; lean_object* v___y_3585_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; uint8_t v___y_3617_; lean_object* v___y_3618_; uint8_t v___y_3619_; uint8_t v___y_3620_; lean_object* v___y_3621_; uint8_t v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3644_; uint8_t v___y_3645_; uint8_t v___y_3646_; lean_object* v___y_3647_; uint8_t v___y_3651_; uint8_t v___y_3652_; uint8_t v___x_3662_; uint8_t v___y_3664_; uint8_t v___x_3670_; 
v___x_3662_ = 2;
v___x_3670_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3569_, v___x_3662_);
if (v___x_3670_ == 0)
{
v___y_3664_ = v___x_3670_;
goto v___jp_3663_;
}
else
{
uint8_t v___x_3671_; 
lean_inc_ref(v_msgData_3568_);
v___x_3671_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3568_);
if (v___x_3671_ == 0)
{
v___y_3664_ = v___x_3671_;
goto v___jp_3663_;
}
else
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_dec_ref(v_msgData_3568_);
v___x_3672_ = lean_box(0);
v___x_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
return v___x_3673_;
}
}
v___jp_3576_:
{
lean_object* v_currNamespace_3586_; lean_object* v_openDecls_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v_env_3592_; lean_object* v_nextMacroScope_3593_; lean_object* v_ngen_3594_; lean_object* v_auxDeclNGen_3595_; lean_object* v_traceState_3596_; lean_object* v_cache_3597_; lean_object* v_recordedDeps_3598_; lean_object* v_messages_3599_; lean_object* v_infoState_3600_; lean_object* v_snapshotTasks_3601_; lean_object* v___x_3603_; uint8_t v_isShared_3604_; uint8_t v_isSharedCheck_3612_; 
v_currNamespace_3586_ = lean_ctor_get(v_toCold_3584_, 4);
v_openDecls_3587_ = lean_ctor_get(v_toCold_3584_, 5);
lean_inc(v_openDecls_3587_);
lean_inc(v_currNamespace_3586_);
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v_currNamespace_3586_);
lean_ctor_set(v___x_3588_, 1, v_openDecls_3587_);
v___x_3589_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
lean_ctor_set(v___x_3589_, 1, v___y_3578_);
lean_inc_ref(v___y_3579_);
lean_inc_ref(v___y_3577_);
v___x_3590_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3590_, 0, v___y_3577_);
lean_ctor_set(v___x_3590_, 1, v___y_3581_);
lean_ctor_set(v___x_3590_, 2, v___y_3580_);
lean_ctor_set(v___x_3590_, 3, v___y_3579_);
lean_ctor_set(v___x_3590_, 4, v___x_3589_);
lean_ctor_set_uint8(v___x_3590_, sizeof(void*)*5, v___y_3583_);
lean_ctor_set_uint8(v___x_3590_, sizeof(void*)*5 + 1, v___y_3582_);
lean_ctor_set_uint8(v___x_3590_, sizeof(void*)*5 + 2, v_isSilent_3570_);
v___x_3591_ = lean_st_ref_take(v___y_3585_);
v_env_3592_ = lean_ctor_get(v___x_3591_, 0);
v_nextMacroScope_3593_ = lean_ctor_get(v___x_3591_, 1);
v_ngen_3594_ = lean_ctor_get(v___x_3591_, 2);
v_auxDeclNGen_3595_ = lean_ctor_get(v___x_3591_, 3);
v_traceState_3596_ = lean_ctor_get(v___x_3591_, 4);
v_cache_3597_ = lean_ctor_get(v___x_3591_, 5);
v_recordedDeps_3598_ = lean_ctor_get(v___x_3591_, 6);
v_messages_3599_ = lean_ctor_get(v___x_3591_, 7);
v_infoState_3600_ = lean_ctor_get(v___x_3591_, 8);
v_snapshotTasks_3601_ = lean_ctor_get(v___x_3591_, 9);
v_isSharedCheck_3612_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3603_ = v___x_3591_;
v_isShared_3604_ = v_isSharedCheck_3612_;
goto v_resetjp_3602_;
}
else
{
lean_inc(v_snapshotTasks_3601_);
lean_inc(v_infoState_3600_);
lean_inc(v_messages_3599_);
lean_inc(v_recordedDeps_3598_);
lean_inc(v_cache_3597_);
lean_inc(v_traceState_3596_);
lean_inc(v_auxDeclNGen_3595_);
lean_inc(v_ngen_3594_);
lean_inc(v_nextMacroScope_3593_);
lean_inc(v_env_3592_);
lean_dec(v___x_3591_);
v___x_3603_ = lean_box(0);
v_isShared_3604_ = v_isSharedCheck_3612_;
goto v_resetjp_3602_;
}
v_resetjp_3602_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3605_ = lean_box(0);
v___x_3606_ = l_Lean_MessageLog_add(v___x_3590_, v_messages_3599_);
if (v_isShared_3604_ == 0)
{
lean_ctor_set(v___x_3603_, 7, v___x_3606_);
v___x_3608_ = v___x_3603_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_env_3592_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_nextMacroScope_3593_);
lean_ctor_set(v_reuseFailAlloc_3611_, 2, v_ngen_3594_);
lean_ctor_set(v_reuseFailAlloc_3611_, 3, v_auxDeclNGen_3595_);
lean_ctor_set(v_reuseFailAlloc_3611_, 4, v_traceState_3596_);
lean_ctor_set(v_reuseFailAlloc_3611_, 5, v_cache_3597_);
lean_ctor_set(v_reuseFailAlloc_3611_, 6, v_recordedDeps_3598_);
lean_ctor_set(v_reuseFailAlloc_3611_, 7, v___x_3606_);
lean_ctor_set(v_reuseFailAlloc_3611_, 8, v_infoState_3600_);
lean_ctor_set(v_reuseFailAlloc_3611_, 9, v_snapshotTasks_3601_);
v___x_3608_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_st_ref_put(v___y_3585_, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3605_);
return v___x_3610_;
}
}
}
v___jp_3613_:
{
lean_object* v_fileName_3622_; lean_object* v_fileMap_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3639_; 
v_fileName_3622_ = lean_ctor_get(v___y_3618_, 0);
v_fileMap_3623_ = lean_ctor_get(v___y_3618_, 1);
v___x_3624_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3568_);
v___x_3625_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(v___x_3624_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3628_ = v___x_3625_;
v_isShared_3629_ = v_isSharedCheck_3639_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3625_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3639_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
lean_inc_ref_n(v_fileMap_3623_, 2);
v___x_3630_ = l_Lean_FileMap_toPosition(v_fileMap_3623_, v___y_3616_);
lean_dec(v___y_3616_);
v___x_3631_ = l_Lean_FileMap_toPosition(v_fileMap_3623_, v___y_3621_);
lean_dec(v___y_3621_);
v___x_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3631_);
v___x_3633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
if (v___y_3617_ == 0)
{
lean_del_object(v___x_3628_);
lean_dec_ref(v___y_3615_);
v___y_3577_ = v_fileName_3622_;
v___y_3578_ = v_a_3626_;
v___y_3579_ = v___x_3633_;
v___y_3580_ = v___x_3632_;
v___y_3581_ = v___x_3630_;
v___y_3582_ = v___y_3620_;
v___y_3583_ = v___y_3619_;
v_toCold_3584_ = v___y_3614_;
v___y_3585_ = v___y_3574_;
goto v___jp_3576_;
}
else
{
uint8_t v___x_3634_; 
lean_inc(v_a_3626_);
v___x_3634_ = l_Lean_MessageData_hasTag(v___y_3615_, v_a_3626_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; lean_object* v___x_3637_; 
lean_dec_ref_known(v___x_3632_, 1);
lean_dec_ref(v___x_3630_);
lean_dec(v_a_3626_);
v___x_3635_ = lean_box(0);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 0, v___x_3635_);
v___x_3637_ = v___x_3628_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
else
{
lean_del_object(v___x_3628_);
v___y_3577_ = v_fileName_3622_;
v___y_3578_ = v_a_3626_;
v___y_3579_ = v___x_3633_;
v___y_3580_ = v___x_3632_;
v___y_3581_ = v___x_3630_;
v___y_3582_ = v___y_3620_;
v___y_3583_ = v___y_3619_;
v_toCold_3584_ = v___y_3614_;
v___y_3585_ = v___y_3574_;
goto v___jp_3576_;
}
}
}
}
v___jp_3640_:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lean_Syntax_getTailPos_x3f(v___y_3644_, v___y_3646_);
lean_dec(v___y_3644_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_inc(v___y_3647_);
v___y_3614_ = v___y_3642_;
v___y_3615_ = v___y_3643_;
v___y_3616_ = v___y_3647_;
v___y_3617_ = v___y_3641_;
v___y_3618_ = v___y_3642_;
v___y_3619_ = v___y_3646_;
v___y_3620_ = v___y_3645_;
v___y_3621_ = v___y_3647_;
goto v___jp_3613_;
}
else
{
lean_object* v_val_3649_; 
v_val_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_val_3649_);
lean_dec_ref_known(v___x_3648_, 1);
v___y_3614_ = v___y_3642_;
v___y_3615_ = v___y_3643_;
v___y_3616_ = v___y_3647_;
v___y_3617_ = v___y_3641_;
v___y_3618_ = v___y_3642_;
v___y_3619_ = v___y_3646_;
v___y_3620_ = v___y_3645_;
v___y_3621_ = v_val_3649_;
goto v___jp_3613_;
}
}
v___jp_3650_:
{
lean_object* v_toCold_3653_; lean_object* v_ref_3654_; uint8_t v_suppressElabErrors_3655_; lean_object* v___x_3656_; lean_object* v___f_3657_; lean_object* v_ref_3658_; lean_object* v___x_3659_; 
v_toCold_3653_ = lean_ctor_get(v___y_3573_, 0);
v_ref_3654_ = lean_ctor_get(v___y_3573_, 2);
v_suppressElabErrors_3655_ = lean_ctor_get_uint8(v___y_3573_, sizeof(void*)*3 + 2);
v___x_3656_ = lean_box(v_suppressElabErrors_3655_);
v___f_3657_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3657_, 0, v___x_3656_);
v_ref_3658_ = l_Lean_replaceRef(v_ref_3567_, v_ref_3654_);
v___x_3659_ = l_Lean_Syntax_getPos_x3f(v_ref_3658_, v___y_3651_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v___x_3660_; 
v___x_3660_ = lean_unsigned_to_nat(0u);
v___y_3641_ = v_suppressElabErrors_3655_;
v___y_3642_ = v_toCold_3653_;
v___y_3643_ = v___f_3657_;
v___y_3644_ = v_ref_3658_;
v___y_3645_ = v___y_3652_;
v___y_3646_ = v___y_3651_;
v___y_3647_ = v___x_3660_;
goto v___jp_3640_;
}
else
{
lean_object* v_val_3661_; 
v_val_3661_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_val_3661_);
lean_dec_ref_known(v___x_3659_, 1);
v___y_3641_ = v_suppressElabErrors_3655_;
v___y_3642_ = v_toCold_3653_;
v___y_3643_ = v___f_3657_;
v___y_3644_ = v_ref_3658_;
v___y_3645_ = v___y_3652_;
v___y_3646_ = v___y_3651_;
v___y_3647_ = v_val_3661_;
goto v___jp_3640_;
}
}
v___jp_3663_:
{
uint8_t v___x_3665_; uint8_t v___x_3666_; 
v___x_3665_ = 1;
v___x_3666_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3569_, v___x_3665_);
if (v___x_3666_ == 0)
{
v___y_3651_ = v___y_3664_;
v___y_3652_ = v_severity_3569_;
goto v___jp_3650_;
}
else
{
lean_object* v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v___x_3667_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3573_);
v___x_3668_ = l_Lean_warningAsError;
v___x_3669_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(v___x_3667_, v___x_3668_);
lean_dec_ref(v___x_3667_);
if (v___x_3669_ == 0)
{
v___y_3651_ = v___y_3664_;
v___y_3652_ = v_severity_3569_;
goto v___jp_3650_;
}
else
{
v___y_3651_ = v___y_3664_;
v___y_3652_ = v___x_3662_;
goto v___jp_3650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3674_, lean_object* v_msgData_3675_, lean_object* v_severity_3676_, lean_object* v_isSilent_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
uint8_t v_severity_boxed_3683_; uint8_t v_isSilent_boxed_3684_; lean_object* v_res_3685_; 
v_severity_boxed_3683_ = lean_unbox(v_severity_3676_);
v_isSilent_boxed_3684_ = lean_unbox(v_isSilent_3677_);
v_res_3685_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_3674_, v_msgData_3675_, v_severity_boxed_3683_, v_isSilent_boxed_3684_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
lean_dec(v_ref_3674_);
return v_res_3685_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(lean_object* v_msgData_3686_, uint8_t v_severity_3687_, uint8_t v_isSilent_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
lean_object* v_ref_3696_; lean_object* v___x_3697_; 
v_ref_3696_ = lean_ctor_get(v___y_3693_, 2);
v___x_3697_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_3696_, v_msgData_3686_, v_severity_3687_, v_isSilent_3688_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0___boxed(lean_object* v_msgData_3698_, lean_object* v_severity_3699_, lean_object* v_isSilent_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
uint8_t v_severity_boxed_3708_; uint8_t v_isSilent_boxed_3709_; lean_object* v_res_3710_; 
v_severity_boxed_3708_ = lean_unbox(v_severity_3699_);
v_isSilent_boxed_3709_ = lean_unbox(v_isSilent_3700_);
v_res_3710_ = l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(v_msgData_3698_, v_severity_boxed_3708_, v_isSilent_boxed_3709_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(lean_object* v_msgData_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
uint8_t v___x_3719_; uint8_t v___x_3720_; lean_object* v___x_3721_; 
v___x_3719_ = 2;
v___x_3720_ = 0;
v___x_3721_ = l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(v_msgData_3711_, v___x_3719_, v___x_3720_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0___boxed(lean_object* v_msgData_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(v_msgData_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec_ref(v___y_3723_);
return v_res_3730_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0));
v___x_3733_ = l_Lean_stringToMessageData(v___x_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(lean_object* v_a_3734_, lean_object* v_as_3735_, size_t v_sz_3736_, size_t v_i_3737_, lean_object* v_b_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v_snd_3747_; uint8_t v___x_3751_; 
v___x_3751_ = lean_usize_dec_lt(v_i_3737_, v_sz_3736_);
if (v___x_3751_ == 0)
{
lean_object* v___x_3752_; 
lean_dec_ref(v_a_3734_);
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v_b_3738_);
return v___x_3752_;
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3754_; 
v_a_3753_ = lean_array_uget_borrowed(v_as_3735_, v_i_3737_);
lean_inc_ref(v_a_3734_);
lean_inc(v_a_3753_);
v___x_3754_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_a_3753_, v_a_3734_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; uint8_t v___x_3756_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
v___x_3756_ = lean_unbox(v_a_3755_);
lean_dec(v_a_3755_);
if (v___x_3756_ == 0)
{
v_snd_3747_ = v_b_3738_;
goto v___jp_3746_;
}
else
{
lean_object* v___x_3757_; 
lean_inc(v_a_3753_);
v___x_3757_ = lean_array_push(v_b_3738_, v_a_3753_);
v_snd_3747_ = v___x_3757_;
goto v___jp_3746_;
}
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3784_; 
v_a_3758_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3760_ = v___x_3754_;
v_isShared_3761_ = v_isSharedCheck_3784_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3754_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3784_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
uint8_t v___x_3762_; 
v___x_3762_ = l_Lean_Exception_isInterrupt(v_a_3758_);
if (v___x_3762_ == 0)
{
uint8_t v___x_3763_; 
lean_inc(v_a_3758_);
v___x_3763_ = l_Lean_Exception_isRuntime(v_a_3758_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; 
lean_del_object(v___x_3760_);
lean_inc(v_a_3753_);
v___x_3764_ = l_Lean_MessageData_ofName(v_a_3753_);
v___x_3765_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3767_ = l_Lean_Exception_toMessageData(v_a_3758_);
v___x_3768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3766_);
lean_ctor_set(v___x_3768_, 1, v___x_3767_);
v___x_3769_ = l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(v___x_3768_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_dec_ref_known(v___x_3769_, 1);
v_snd_3747_ = v_b_3738_;
goto v___jp_3746_;
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec_ref(v_b_3738_);
lean_dec_ref(v_a_3734_);
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
else
{
lean_object* v___x_3779_; 
lean_dec_ref(v_b_3738_);
lean_dec_ref(v_a_3734_);
if (v_isShared_3761_ == 0)
{
v___x_3779_ = v___x_3760_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3758_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
else
{
lean_object* v___x_3782_; 
lean_dec_ref(v_b_3738_);
lean_dec_ref(v_a_3734_);
if (v_isShared_3761_ == 0)
{
v___x_3782_ = v___x_3760_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3758_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
}
v___jp_3746_:
{
size_t v___x_3748_; size_t v___x_3749_; 
v___x_3748_ = ((size_t)1ULL);
v___x_3749_ = lean_usize_add(v_i_3737_, v___x_3748_);
v_i_3737_ = v___x_3749_;
v_b_3738_ = v_snd_3747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___boxed(lean_object* v_a_3785_, lean_object* v_as_3786_, lean_object* v_sz_3787_, lean_object* v_i_3788_, lean_object* v_b_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
size_t v_sz_boxed_3797_; size_t v_i_boxed_3798_; lean_object* v_res_3799_; 
v_sz_boxed_3797_ = lean_unbox_usize(v_sz_3787_);
lean_dec(v_sz_3787_);
v_i_boxed_3798_ = lean_unbox_usize(v_i_3788_);
lean_dec(v_i_3788_);
v_res_3799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(v_a_3785_, v_as_3786_, v_sz_boxed_3797_, v_i_boxed_3798_, v_b_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_);
lean_dec(v___y_3795_);
lean_dec_ref(v___y_3794_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec_ref(v_as_3786_);
return v_res_3799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(uint8_t v___x_3801_, lean_object* v_as_3802_, size_t v_sz_3803_, size_t v_i_3804_, lean_object* v_b_3805_){
_start:
{
uint8_t v___x_3807_; 
v___x_3807_ = lean_usize_dec_lt(v_i_3804_, v_sz_3803_);
if (v___x_3807_ == 0)
{
lean_object* v___x_3808_; 
v___x_3808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3808_, 0, v_b_3805_);
return v___x_3808_;
}
else
{
lean_object* v___x_3809_; lean_object* v_a_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; size_t v___x_3816_; size_t v___x_3817_; 
v___x_3809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v_a_3810_ = lean_array_uget_borrowed(v_as_3802_, v_i_3804_);
v___x_3811_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0));
lean_inc(v_a_3810_);
v___x_3812_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_3810_, v___x_3801_);
v___x_3813_ = lean_string_append(v___x_3811_, v___x_3812_);
lean_dec_ref(v___x_3812_);
v___x_3814_ = lean_string_append(v___x_3813_, v___x_3809_);
v___x_3815_ = lean_string_append(v_b_3805_, v___x_3814_);
lean_dec_ref(v___x_3814_);
v___x_3816_ = ((size_t)1ULL);
v___x_3817_ = lean_usize_add(v_i_3804_, v___x_3816_);
v_i_3804_ = v___x_3817_;
v_b_3805_ = v___x_3815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___boxed(lean_object* v___x_3819_, lean_object* v_as_3820_, lean_object* v_sz_3821_, lean_object* v_i_3822_, lean_object* v_b_3823_, lean_object* v___y_3824_){
_start:
{
uint8_t v___x_10644__boxed_3825_; size_t v_sz_boxed_3826_; size_t v_i_boxed_3827_; lean_object* v_res_3828_; 
v___x_10644__boxed_3825_ = lean_unbox(v___x_3819_);
v_sz_boxed_3826_ = lean_unbox_usize(v_sz_3821_);
lean_dec(v_sz_3821_);
v_i_boxed_3827_ = lean_unbox_usize(v_i_3822_);
lean_dec(v_i_3822_);
v_res_3828_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v___x_10644__boxed_3825_, v_as_3820_, v_sz_boxed_3826_, v_i_boxed_3827_, v_b_3823_);
lean_dec_ref(v_as_3820_);
return v_res_3828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(uint8_t v___x_3830_, lean_object* v_stx_3831_, uint8_t v___x_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
if (v___x_3830_ == 0)
{
lean_object* v___x_3840_; 
lean_dec(v_stx_3831_);
v___x_3840_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3840_;
}
else
{
lean_object* v_toCold_3841_; lean_object* v_currRecDepth_3842_; lean_object* v_ref_3843_; uint16_t v_optionFlags_3844_; uint8_t v_suppressElabErrors_3845_; uint8_t v_checkDeprecated_3846_; uint8_t v_isRecordingDeps_3847_; lean_object* v_fileName_3848_; lean_object* v_fileMap_3849_; lean_object* v_options_3850_; lean_object* v_maxRecDepth_3851_; lean_object* v_currNamespace_3852_; lean_object* v_openDecls_3853_; lean_object* v_initHeartbeats_3854_; lean_object* v_quotContext_3855_; lean_object* v_currMacroScope_3856_; lean_object* v_cancelTk_x3f_3857_; lean_object* v_inheritedTraceOptions_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; size_t v_sz_3862_; size_t v___x_3863_; lean_object* v___x_3864_; 
v_toCold_3841_ = lean_ctor_get(v___y_3837_, 0);
v_currRecDepth_3842_ = lean_ctor_get(v___y_3837_, 1);
v_ref_3843_ = lean_ctor_get(v___y_3837_, 2);
v_optionFlags_3844_ = lean_ctor_get_uint16(v___y_3837_, sizeof(void*)*3);
v_suppressElabErrors_3845_ = lean_ctor_get_uint8(v___y_3837_, sizeof(void*)*3 + 2);
v_checkDeprecated_3846_ = lean_ctor_get_uint8(v___y_3837_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3847_ = lean_ctor_get_uint8(v___y_3837_, sizeof(void*)*3 + 4);
v_fileName_3848_ = lean_ctor_get(v_toCold_3841_, 0);
v_fileMap_3849_ = lean_ctor_get(v_toCold_3841_, 1);
v_options_3850_ = lean_ctor_get(v_toCold_3841_, 2);
v_maxRecDepth_3851_ = lean_ctor_get(v_toCold_3841_, 3);
v_currNamespace_3852_ = lean_ctor_get(v_toCold_3841_, 4);
v_openDecls_3853_ = lean_ctor_get(v_toCold_3841_, 5);
v_initHeartbeats_3854_ = lean_ctor_get(v_toCold_3841_, 6);
v_quotContext_3855_ = lean_ctor_get(v_toCold_3841_, 8);
v_currMacroScope_3856_ = lean_ctor_get(v_toCold_3841_, 9);
v_cancelTk_x3f_3857_ = lean_ctor_get(v_toCold_3841_, 10);
v_inheritedTraceOptions_3858_ = lean_ctor_get(v_toCold_3841_, 11);
v___x_3859_ = lean_unsigned_to_nat(2u);
v___x_3860_ = l_Lean_Syntax_getArg(v_stx_3831_, v___x_3859_);
v___x_3861_ = l_Lean_Syntax_getArgs(v___x_3860_);
lean_dec(v___x_3860_);
v_sz_3862_ = lean_array_size(v___x_3861_);
v___x_3863_ = ((size_t)0ULL);
v___x_3864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_3862_, v___x_3863_, v___x_3861_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v___x_3865_; 
lean_dec(v_stx_3831_);
v___x_3865_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3865_;
}
else
{
lean_object* v_val_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_4078_; 
v_val_3866_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_3868_ = v___x_3864_;
v_isShared_3869_ = v_isSharedCheck_4078_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_val_3866_);
lean_dec(v___x_3864_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_4078_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3870_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; uint8_t v___y_3973_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v_m_x3f_4011_; lean_object* v_ids_x3f_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v_m_x3f_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; uint8_t v___x_4067_; 
v___x_3870_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inheritedTraceOptions_3858_);
lean_inc(v_cancelTk_x3f_3857_);
lean_inc(v_currMacroScope_3856_);
lean_inc(v_quotContext_3855_);
lean_inc(v_initHeartbeats_3854_);
lean_inc(v_openDecls_3853_);
lean_inc(v_currNamespace_3852_);
lean_inc(v_maxRecDepth_3851_);
lean_inc_ref(v_options_3850_);
lean_inc_ref(v_fileMap_3849_);
lean_inc_ref(v_fileName_3848_);
v___x_3961_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3961_, 0, v_fileName_3848_);
lean_ctor_set(v___x_3961_, 1, v_fileMap_3849_);
lean_ctor_set(v___x_3961_, 2, v_options_3850_);
lean_ctor_set(v___x_3961_, 3, v_maxRecDepth_3851_);
lean_ctor_set(v___x_3961_, 4, v_currNamespace_3852_);
lean_ctor_set(v___x_3961_, 5, v_openDecls_3853_);
lean_ctor_set(v___x_3961_, 6, v_initHeartbeats_3854_);
lean_ctor_set(v___x_3961_, 7, v___x_3870_);
lean_ctor_set(v___x_3961_, 8, v_quotContext_3855_);
lean_ctor_set(v___x_3961_, 9, v_currMacroScope_3856_);
lean_ctor_set(v___x_3961_, 10, v_cancelTk_x3f_3857_);
lean_ctor_set(v___x_3961_, 11, v_inheritedTraceOptions_3858_);
lean_inc(v_ref_3843_);
lean_inc(v_currRecDepth_3842_);
v___x_3962_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v_currRecDepth_3842_);
lean_ctor_set(v___x_3962_, 2, v_ref_3843_);
lean_ctor_set_uint16(v___x_3962_, sizeof(void*)*3, v_optionFlags_3844_);
lean_ctor_set_uint8(v___x_3962_, sizeof(void*)*3 + 2, v_suppressElabErrors_3845_);
lean_ctor_set_uint8(v___x_3962_, sizeof(void*)*3 + 3, v_checkDeprecated_3846_);
lean_ctor_set_uint8(v___x_3962_, sizeof(void*)*3 + 4, v_isRecordingDeps_3847_);
v___x_3963_ = lean_unsigned_to_nat(1u);
v___x_4051_ = lean_unsigned_to_nat(3u);
v___x_4052_ = l_Lean_Syntax_getArg(v_stx_3831_, v___x_4051_);
v___x_4067_ = l_Lean_Syntax_isNone(v___x_4052_);
if (v___x_4067_ == 0)
{
uint8_t v___x_4068_; 
lean_inc(v___x_4052_);
v___x_4068_ = l_Lean_Syntax_matchesNull(v___x_4052_, v___x_4051_);
if (v___x_4068_ == 0)
{
lean_object* v___x_4069_; 
lean_dec(v___x_4052_);
lean_dec_ref_known(v___x_3962_, 3);
lean_del_object(v___x_3868_);
lean_dec(v_val_3866_);
lean_dec(v_stx_3831_);
v___x_4069_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_4069_;
}
else
{
lean_object* v___x_4070_; uint8_t v___x_4071_; 
v___x_4070_ = l_Lean_Syntax_getArg(v___x_4052_, v___x_3963_);
v___x_4071_ = l_Lean_Syntax_isNone(v___x_4070_);
if (v___x_4071_ == 0)
{
uint8_t v___x_4072_; 
lean_inc(v___x_4070_);
v___x_4072_ = l_Lean_Syntax_matchesNull(v___x_4070_, v___x_3963_);
if (v___x_4072_ == 0)
{
lean_object* v___x_4073_; 
lean_dec(v___x_4070_);
lean_dec(v___x_4052_);
lean_dec_ref_known(v___x_3962_, 3);
lean_del_object(v___x_3868_);
lean_dec(v_val_3866_);
lean_dec(v_stx_3831_);
v___x_4073_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_4073_;
}
else
{
lean_object* v_m_x3f_4074_; lean_object* v___x_4075_; 
v_m_x3f_4074_ = l_Lean_Syntax_getArg(v___x_4070_, v___x_3870_);
lean_dec(v___x_4070_);
v___x_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4075_, 0, v_m_x3f_4074_);
v_m_x3f_4054_ = v___x_4075_;
v___y_4055_ = v___y_3833_;
v___y_4056_ = v___y_3834_;
v___y_4057_ = v___y_3835_;
v___y_4058_ = v___y_3836_;
v___y_4059_ = v___x_3962_;
v___y_4060_ = v___y_3838_;
goto v___jp_4053_;
}
}
else
{
lean_object* v___x_4076_; 
lean_dec(v___x_4070_);
v___x_4076_ = lean_box(0);
v_m_x3f_4054_ = v___x_4076_;
v___y_4055_ = v___y_3833_;
v___y_4056_ = v___y_3834_;
v___y_4057_ = v___y_3835_;
v___y_4058_ = v___y_3836_;
v___y_4059_ = v___x_3962_;
v___y_4060_ = v___y_3838_;
goto v___jp_4053_;
}
}
}
else
{
lean_object* v___x_4077_; 
lean_dec(v___x_4052_);
lean_del_object(v___x_3868_);
v___x_4077_ = lean_box(0);
v_m_x3f_4011_ = v___x_4077_;
v_ids_x3f_4012_ = v___x_4077_;
v___y_4013_ = v___y_3833_;
v___y_4014_ = v___y_3834_;
v___y_4015_ = v___y_3835_;
v___y_4016_ = v___y_3836_;
v___y_4017_ = v___x_3962_;
v___y_4018_ = v___y_3838_;
goto v___jp_4010_;
}
v___jp_3871_:
{
lean_object* v___x_3880_; size_t v_sz_3881_; lean_object* v___x_3882_; 
v___x_3880_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0));
v_sz_3881_ = lean_array_size(v___y_3879_);
v___x_3882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(v___y_3878_, v___y_3879_, v_sz_3881_, v___x_3863_, v___x_3880_, v___y_3873_, v___y_3876_, v___y_3875_, v___y_3872_, v___y_3877_, v___y_3874_);
lean_dec_ref(v___y_3879_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v_a_3883_; lean_object* v___x_3885_; uint8_t v_isShared_3886_; uint8_t v_isSharedCheck_3926_; 
v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3885_ = v___x_3882_;
v_isShared_3886_ = v_isSharedCheck_3926_;
goto v_resetjp_3884_;
}
else
{
lean_inc(v_a_3883_);
lean_dec(v___x_3882_);
v___x_3885_ = lean_box(0);
v_isShared_3886_ = v_isSharedCheck_3926_;
goto v_resetjp_3884_;
}
v_resetjp_3884_:
{
lean_object* v___x_3887_; uint8_t v___x_3888_; 
v___x_3887_ = lean_array_get_size(v_a_3883_);
v___x_3888_ = lean_nat_dec_eq(v___x_3887_, v___x_3870_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
lean_del_object(v___x_3885_);
v___x_3889_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5));
lean_inc(v_stx_3831_);
v___x_3890_ = l_Lean_PrettyPrinter_ppCategory(v___x_3889_, v_stx_3831_, v___y_3877_, v___y_3874_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; size_t v_sz_3896_; lean_object* v___x_3897_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
v___x_3892_ = l_Std_Format_defWidth;
v___x_3893_ = l_Std_Format_pretty(v_a_3891_, v___x_3892_, v___x_3870_, v___x_3870_);
v___x_3894_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v___x_3895_ = lean_string_append(v___x_3893_, v___x_3894_);
v_sz_3896_ = lean_array_size(v_a_3883_);
v___x_3897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v___x_3830_, v_a_3883_, v_sz_3896_, v___x_3863_, v___x_3895_);
lean_dec(v_a_3883_);
if (lean_obj_tag(v___x_3897_) == 0)
{
lean_object* v_a_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; uint8_t v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; 
v_a_3898_ = lean_ctor_get(v___x_3897_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v___x_3897_, 1);
v___x_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3899_, 0, v_a_3898_);
v___x_3900_ = lean_box(0);
v___x_3901_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3899_);
lean_ctor_set(v___x_3901_, 1, v___x_3900_);
lean_ctor_set(v___x_3901_, 2, v___x_3900_);
lean_ctor_set(v___x_3901_, 3, v___x_3900_);
lean_ctor_set(v___x_3901_, 4, v___x_3900_);
lean_ctor_set(v___x_3901_, 5, v___x_3900_);
v___x_3902_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0));
v___x_3903_ = 4;
v___x_3904_ = l_Lean_MessageData_nil;
v___x_3905_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_3831_, v___x_3901_, v___x_3900_, v___x_3902_, v___x_3900_, v___x_3903_, v___x_3904_, v___y_3877_, v___y_3874_);
lean_dec_ref(v___y_3877_);
return v___x_3905_;
}
else
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
lean_dec_ref(v___y_3877_);
lean_dec(v_stx_3831_);
v_a_3906_ = lean_ctor_get(v___x_3897_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3897_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v___x_3897_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v___x_3897_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_dec(v_a_3883_);
lean_dec_ref(v___y_3877_);
lean_dec(v_stx_3831_);
v_a_3914_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3890_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3890_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
else
{
lean_object* v___x_3922_; lean_object* v___x_3924_; 
lean_dec(v_a_3883_);
lean_dec_ref(v___y_3877_);
lean_dec(v_stx_3831_);
v___x_3922_ = lean_box(0);
if (v_isShared_3886_ == 0)
{
lean_ctor_set(v___x_3885_, 0, v___x_3922_);
v___x_3924_ = v___x_3885_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
else
{
lean_object* v_a_3927_; lean_object* v___x_3929_; uint8_t v_isShared_3930_; uint8_t v_isSharedCheck_3934_; 
lean_dec_ref(v___y_3877_);
lean_dec(v_stx_3831_);
v_a_3927_ = lean_ctor_get(v___x_3882_, 0);
v_isSharedCheck_3934_ = !lean_is_exclusive(v___x_3882_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3929_ = v___x_3882_;
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
else
{
lean_inc(v_a_3927_);
lean_dec(v___x_3882_);
v___x_3929_ = lean_box(0);
v_isShared_3930_ = v_isSharedCheck_3934_;
goto v_resetjp_3928_;
}
v_resetjp_3928_:
{
lean_object* v___x_3932_; 
if (v_isShared_3930_ == 0)
{
v___x_3932_ = v___x_3929_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
}
v___jp_3935_:
{
lean_object* v___x_3947_; 
v___x_3947_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v___y_3940_, v___y_3944_, v___y_3939_, v___y_3946_);
lean_dec(v___y_3946_);
lean_dec(v___y_3940_);
v___y_3872_ = v___y_3936_;
v___y_3873_ = v___y_3937_;
v___y_3874_ = v___y_3938_;
v___y_3875_ = v___y_3941_;
v___y_3876_ = v___y_3942_;
v___y_3877_ = v___y_3943_;
v___y_3878_ = v___y_3945_;
v___y_3879_ = v___x_3947_;
goto v___jp_3871_;
}
v___jp_3948_:
{
uint8_t v___x_3960_; 
v___x_3960_ = lean_nat_dec_le(v___y_3959_, v___y_3949_);
if (v___x_3960_ == 0)
{
lean_dec(v___y_3949_);
lean_inc(v___y_3959_);
v___y_3936_ = v___y_3950_;
v___y_3937_ = v___y_3951_;
v___y_3938_ = v___y_3952_;
v___y_3939_ = v___y_3959_;
v___y_3940_ = v___y_3953_;
v___y_3941_ = v___y_3954_;
v___y_3942_ = v___y_3955_;
v___y_3943_ = v___y_3957_;
v___y_3944_ = v___y_3956_;
v___y_3945_ = v___y_3958_;
v___y_3946_ = v___y_3959_;
goto v___jp_3935_;
}
else
{
v___y_3936_ = v___y_3950_;
v___y_3937_ = v___y_3951_;
v___y_3938_ = v___y_3952_;
v___y_3939_ = v___y_3959_;
v___y_3940_ = v___y_3953_;
v___y_3941_ = v___y_3954_;
v___y_3942_ = v___y_3955_;
v___y_3943_ = v___y_3957_;
v___y_3944_ = v___y_3956_;
v___y_3945_ = v___y_3958_;
v___y_3946_ = v___y_3949_;
goto v___jp_3935_;
}
}
v___jp_3964_:
{
lean_object* v___x_3974_; 
v___x_3974_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v___y_3972_, v___y_3973_, v___y_3967_);
lean_dec(v___y_3972_);
if (lean_obj_tag(v___x_3974_) == 0)
{
lean_object* v_a_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v_a_3975_ = lean_ctor_get(v___x_3974_, 0);
lean_inc(v_a_3975_);
lean_dec_ref_known(v___x_3974_, 1);
v___x_3976_ = lean_array_mk(v_a_3975_);
v___x_3977_ = lean_array_get_size(v___x_3976_);
v___x_3978_ = lean_nat_dec_eq(v___x_3977_, v___x_3870_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; uint8_t v___x_3980_; 
v___x_3979_ = lean_nat_sub(v___x_3977_, v___x_3963_);
v___x_3980_ = lean_nat_dec_le(v___x_3870_, v___x_3979_);
if (v___x_3980_ == 0)
{
lean_inc(v___x_3979_);
v___y_3949_ = v___x_3979_;
v___y_3950_ = v___y_3965_;
v___y_3951_ = v___y_3966_;
v___y_3952_ = v___y_3967_;
v___y_3953_ = v___x_3977_;
v___y_3954_ = v___y_3968_;
v___y_3955_ = v___y_3969_;
v___y_3956_ = v___x_3976_;
v___y_3957_ = v___y_3970_;
v___y_3958_ = v___y_3971_;
v___y_3959_ = v___x_3979_;
goto v___jp_3948_;
}
else
{
v___y_3949_ = v___x_3979_;
v___y_3950_ = v___y_3965_;
v___y_3951_ = v___y_3966_;
v___y_3952_ = v___y_3967_;
v___y_3953_ = v___x_3977_;
v___y_3954_ = v___y_3968_;
v___y_3955_ = v___y_3969_;
v___y_3956_ = v___x_3976_;
v___y_3957_ = v___y_3970_;
v___y_3958_ = v___y_3971_;
v___y_3959_ = v___x_3870_;
goto v___jp_3948_;
}
}
else
{
v___y_3872_ = v___y_3965_;
v___y_3873_ = v___y_3966_;
v___y_3874_ = v___y_3967_;
v___y_3875_ = v___y_3968_;
v___y_3876_ = v___y_3969_;
v___y_3877_ = v___y_3970_;
v___y_3878_ = v___y_3971_;
v___y_3879_ = v___x_3976_;
goto v___jp_3871_;
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec_ref(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v_stx_3831_);
v_a_3981_ = lean_ctor_get(v___x_3974_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3974_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3974_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3974_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
v___jp_3989_:
{
uint8_t v___x_3998_; 
v___x_3998_ = 0;
v___y_3965_ = v___y_3990_;
v___y_3966_ = v___y_3991_;
v___y_3967_ = v___y_3992_;
v___y_3968_ = v___y_3993_;
v___y_3969_ = v___y_3994_;
v___y_3970_ = v___y_3995_;
v___y_3971_ = v___y_3996_;
v___y_3972_ = v___y_3997_;
v___y_3973_ = v___x_3998_;
goto v___jp_3964_;
}
v___jp_3999_:
{
if (lean_obj_tag(v___y_4003_) == 1)
{
lean_object* v_val_4009_; 
v_val_4009_ = lean_ctor_get(v___y_4003_, 0);
lean_inc(v_val_4009_);
lean_dec_ref_known(v___y_4003_, 1);
if (lean_obj_tag(v_val_4009_) == 1)
{
lean_dec_ref_known(v_val_4009_, 1);
v___y_3965_ = v___y_4000_;
v___y_3966_ = v___y_4001_;
v___y_3967_ = v___y_4002_;
v___y_3968_ = v___y_4004_;
v___y_3969_ = v___y_4005_;
v___y_3970_ = v___y_4006_;
v___y_3971_ = v___y_4007_;
v___y_3972_ = v___y_4008_;
v___y_3973_ = v___x_3832_;
goto v___jp_3964_;
}
else
{
lean_dec(v_val_4009_);
v___y_3990_ = v___y_4000_;
v___y_3991_ = v___y_4001_;
v___y_3992_ = v___y_4002_;
v___y_3993_ = v___y_4004_;
v___y_3994_ = v___y_4005_;
v___y_3995_ = v___y_4006_;
v___y_3996_ = v___y_4007_;
v___y_3997_ = v___y_4008_;
goto v___jp_3989_;
}
}
else
{
lean_dec(v___y_4003_);
v___y_3990_ = v___y_4000_;
v___y_3991_ = v___y_4001_;
v___y_3992_ = v___y_4002_;
v___y_3993_ = v___y_4004_;
v___y_3994_ = v___y_4005_;
v___y_3995_ = v___y_4006_;
v___y_3996_ = v___y_4007_;
v___y_3997_ = v___y_4008_;
goto v___jp_3989_;
}
}
v___jp_4010_:
{
lean_object* v___x_4019_; 
v___x_4019_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_val_3866_, v___y_4013_, v___y_4017_, v___y_4018_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v___x_4021_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref_known(v___x_4019_, 1);
v___x_4021_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_a_4020_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
if (lean_obj_tag(v___x_4021_) == 0)
{
if (lean_obj_tag(v_ids_x3f_4012_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4023_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4021_, 1);
v___x_4023_ = lean_box(0);
v___y_4000_ = v___y_4016_;
v___y_4001_ = v___y_4013_;
v___y_4002_ = v___y_4018_;
v___y_4003_ = v_m_x3f_4011_;
v___y_4004_ = v___y_4015_;
v___y_4005_ = v___y_4014_;
v___y_4006_ = v___y_4017_;
v___y_4007_ = v_a_4022_;
v___y_4008_ = v___x_4023_;
goto v___jp_3999_;
}
else
{
lean_object* v_a_4024_; lean_object* v_val_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4034_; 
v_a_4024_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4021_, 1);
v_val_4025_ = lean_ctor_get(v_ids_x3f_4012_, 0);
v_isSharedCheck_4034_ = !lean_is_exclusive(v_ids_x3f_4012_);
if (v_isSharedCheck_4034_ == 0)
{
v___x_4027_ = v_ids_x3f_4012_;
v_isShared_4028_ = v_isSharedCheck_4034_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_val_4025_);
lean_dec(v_ids_x3f_4012_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4034_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
size_t v_sz_4029_; lean_object* v___x_4030_; lean_object* v___x_4032_; 
v_sz_4029_ = lean_array_size(v_val_4025_);
v___x_4030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(v_sz_4029_, v___x_3863_, v_val_4025_);
if (v_isShared_4028_ == 0)
{
lean_ctor_set(v___x_4027_, 0, v___x_4030_);
v___x_4032_ = v___x_4027_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
v___y_4000_ = v___y_4016_;
v___y_4001_ = v___y_4013_;
v___y_4002_ = v___y_4018_;
v___y_4003_ = v_m_x3f_4011_;
v___y_4004_ = v___y_4015_;
v___y_4005_ = v___y_4014_;
v___y_4006_ = v___y_4017_;
v___y_4007_ = v_a_4024_;
v___y_4008_ = v___x_4032_;
goto v___jp_3999_;
}
}
}
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec_ref(v___y_4017_);
lean_dec(v_ids_x3f_4012_);
lean_dec(v_m_x3f_4011_);
lean_dec(v_stx_3831_);
v_a_4035_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4021_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4021_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
else
{
lean_object* v_a_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4050_; 
lean_dec_ref(v___y_4017_);
lean_dec(v_ids_x3f_4012_);
lean_dec(v_m_x3f_4011_);
lean_dec(v_stx_3831_);
v_a_4043_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4050_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4045_ = v___x_4019_;
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_a_4043_);
lean_dec(v___x_4019_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4050_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___x_4048_; 
if (v_isShared_4046_ == 0)
{
v___x_4048_ = v___x_4045_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4049_; 
v_reuseFailAlloc_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
v___x_4048_ = v_reuseFailAlloc_4049_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
return v___x_4048_;
}
}
}
}
v___jp_4053_:
{
lean_object* v___x_4061_; lean_object* v_ids_x3f_4062_; lean_object* v___x_4064_; 
v___x_4061_ = l_Lean_Syntax_getArg(v___x_4052_, v___x_3859_);
lean_dec(v___x_4052_);
v_ids_x3f_4062_ = l_Lean_Syntax_getArgs(v___x_4061_);
lean_dec(v___x_4061_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v_m_x3f_4054_);
v___x_4064_ = v___x_3868_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_m_x3f_4054_);
v___x_4064_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
lean_object* v___x_4065_; 
v___x_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4065_, 0, v_ids_x3f_4062_);
v_m_x3f_4011_ = v___x_4064_;
v_ids_x3f_4012_ = v___x_4065_;
v___y_4013_ = v___y_4055_;
v___y_4014_ = v___y_4056_;
v___y_4015_ = v___y_4057_;
v___y_4016_ = v___y_4058_;
v___y_4017_ = v___y_4059_;
v___y_4018_ = v___y_4060_;
goto v___jp_4010_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed(lean_object* v___x_4079_, lean_object* v_stx_4080_, lean_object* v___x_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
uint8_t v___x_10681__boxed_4089_; uint8_t v___x_10682__boxed_4090_; lean_object* v_res_4091_; 
v___x_10681__boxed_4089_ = lean_unbox(v___x_4079_);
v___x_10682__boxed_4090_ = lean_unbox(v___x_4081_);
v_res_4091_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(v___x_10681__boxed_4089_, v_stx_4080_, v___x_10682__boxed_4090_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(lean_object* v_stx_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_){
_start:
{
lean_object* v___x_4101_; uint8_t v___x_4102_; uint8_t v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___f_4106_; lean_object* v___x_4107_; 
v___x_4101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1));
lean_inc(v_stx_4097_);
v___x_4102_ = l_Lean_Syntax_isOfKind(v_stx_4097_, v___x_4101_);
v___x_4103_ = 1;
v___x_4104_ = lean_box(v___x_4102_);
v___x_4105_ = lean_box(v___x_4103_);
v___f_4106_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4106_, 0, v___x_4104_);
lean_closure_set(v___f_4106_, 1, v_stx_4097_);
lean_closure_set(v___f_4106_, 2, v___x_4105_);
v___x_4107_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_4106_, v_a_4098_, v_a_4099_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed(lean_object* v_stx_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(v_stx_4108_, v_a_4109_, v_a_4110_);
lean_dec(v_a_4110_);
lean_dec_ref(v_a_4109_);
return v_res_4112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(uint8_t v___x_4113_, lean_object* v_as_4114_, size_t v_sz_4115_, size_t v_i_4116_, lean_object* v_b_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
lean_object* v___x_4125_; 
v___x_4125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v___x_4113_, v_as_4114_, v_sz_4115_, v_i_4116_, v_b_4117_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___boxed(lean_object* v___x_4126_, lean_object* v_as_4127_, lean_object* v_sz_4128_, lean_object* v_i_4129_, lean_object* v_b_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_){
_start:
{
uint8_t v___x_11168__boxed_4138_; size_t v_sz_boxed_4139_; size_t v_i_boxed_4140_; lean_object* v_res_4141_; 
v___x_11168__boxed_4138_ = lean_unbox(v___x_4126_);
v_sz_boxed_4139_ = lean_unbox_usize(v_sz_4128_);
lean_dec(v_sz_4128_);
v_i_boxed_4140_ = lean_unbox_usize(v_i_4129_);
lean_dec(v_i_4129_);
v_res_4141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(v___x_11168__boxed_4138_, v_as_4127_, v_sz_boxed_4139_, v_i_boxed_4140_, v_b_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
lean_dec(v___y_4136_);
lean_dec_ref(v___y_4135_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec_ref(v_as_4127_);
return v_res_4141_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(lean_object* v_n_4142_, lean_object* v_as_4143_, lean_object* v_lo_4144_, lean_object* v_hi_4145_, lean_object* v_w_4146_, lean_object* v_hlo_4147_, lean_object* v_hhi_4148_){
_start:
{
lean_object* v___x_4149_; 
v___x_4149_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_4142_, v_as_4143_, v_lo_4144_, v_hi_4145_);
return v___x_4149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___boxed(lean_object* v_n_4150_, lean_object* v_as_4151_, lean_object* v_lo_4152_, lean_object* v_hi_4153_, lean_object* v_w_4154_, lean_object* v_hlo_4155_, lean_object* v_hhi_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(v_n_4150_, v_as_4151_, v_lo_4152_, v_hi_4153_, v_w_4154_, v_hlo_4155_, v_hhi_4156_);
lean_dec(v_hi_4153_);
lean_dec(v_n_4150_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(lean_object* v_n_4158_, lean_object* v_lo_4159_, lean_object* v_hi_4160_, lean_object* v_hhi_4161_, lean_object* v_pivot_4162_, lean_object* v_as_4163_, lean_object* v_i_4164_, lean_object* v_k_4165_, lean_object* v_ilo_4166_, lean_object* v_ik_4167_, lean_object* v_w_4168_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_4160_, v_pivot_4162_, v_as_4163_, v_i_4164_, v_k_4165_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___boxed(lean_object* v_n_4170_, lean_object* v_lo_4171_, lean_object* v_hi_4172_, lean_object* v_hhi_4173_, lean_object* v_pivot_4174_, lean_object* v_as_4175_, lean_object* v_i_4176_, lean_object* v_k_4177_, lean_object* v_ilo_4178_, lean_object* v_ik_4179_, lean_object* v_w_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(v_n_4170_, v_lo_4171_, v_hi_4172_, v_hhi_4173_, v_pivot_4174_, v_as_4175_, v_i_4176_, v_k_4177_, v_ilo_4178_, v_ik_4179_, v_w_4180_);
lean_dec(v_pivot_4174_);
lean_dec(v_hi_4172_);
lean_dec(v_lo_4171_);
lean_dec(v_n_4170_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(lean_object* v_ref_4182_, lean_object* v_msgData_4183_, uint8_t v_severity_4184_, uint8_t v_isSilent_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_){
_start:
{
lean_object* v___x_4193_; 
v___x_4193_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_4182_, v_msgData_4183_, v_severity_4184_, v_isSilent_4185_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
return v___x_4193_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4194_, lean_object* v_msgData_4195_, lean_object* v_severity_4196_, lean_object* v_isSilent_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_){
_start:
{
uint8_t v_severity_boxed_4205_; uint8_t v_isSilent_boxed_4206_; lean_object* v_res_4207_; 
v_severity_boxed_4205_ = lean_unbox(v_severity_4196_);
v_isSilent_boxed_4206_ = lean_unbox(v_isSilent_4197_);
v_res_4207_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(v_ref_4194_, v_msgData_4195_, v_severity_boxed_4205_, v_isSilent_boxed_4206_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v___y_4201_);
lean_dec_ref(v___y_4200_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v_ref_4194_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1(){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4213_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1));
v___x_4215_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1));
v___x_4216_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed), 4, 0);
v___x_4217_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4213_, v___x_4214_, v___x_4215_, v___x_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___boxed(lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1();
return v_res_4219_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Lint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Config(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Lint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Grind_Lint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Init_Grind_Lint(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Config(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Grind_Lint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Grind_Lint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Grind_Lint(builtin);
}
#ifdef __cplusplus
}
#endif
