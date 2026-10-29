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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` is already in the `#grind_lint` skip suffix set"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5;
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*17 + 40, .m_other = 17, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 1, 1, 0, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
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
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_153_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1);
v___x_154_ = lean_unsigned_to_nat(0u);
v___x_155_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
lean_ctor_set(v___x_155_, 2, v___x_154_);
lean_ctor_set(v___x_155_, 3, v___x_154_);
lean_ctor_set(v___x_155_, 4, v___x_153_);
lean_ctor_set(v___x_155_, 5, v___x_153_);
lean_ctor_set(v___x_155_, 6, v___x_153_);
lean_ctor_set(v___x_155_, 7, v___x_153_);
lean_ctor_set(v___x_155_, 8, v___x_153_);
lean_ctor_set(v___x_155_, 9, v___x_153_);
lean_ctor_set(v___x_155_, 10, v___x_153_);
lean_ctor_set(v___x_155_, 11, v___x_152_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_unsigned_to_nat(32u);
v___x_157_ = lean_mk_empty_array_with_capacity(v___x_156_);
v___x_158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_159_ = ((size_t)5ULL);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_unsigned_to_nat(32u);
v___x_162_ = lean_mk_empty_array_with_capacity(v___x_161_);
v___x_163_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3);
v___x_164_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_160_);
lean_ctor_set(v___x_164_, 3, v___x_160_);
lean_ctor_set_usize(v___x_164_, 4, v___x_159_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = lean_box(1);
v___x_166_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4);
v___x_167_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1);
v___x_168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_165_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(lean_object* v_msgData_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v___x_173_; lean_object* v_toCold_174_; lean_object* v_env_175_; lean_object* v_options_176_; uint8_t v___x_177_; lean_object* v_env_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_173_ = lean_st_ref_get(v___y_171_);
v_toCold_174_ = lean_ctor_get(v___y_170_, 0);
v_env_175_ = lean_ctor_get(v___x_173_, 0);
lean_inc_ref(v_env_175_);
lean_dec(v___x_173_);
v_options_176_ = lean_ctor_get(v_toCold_174_, 2);
v___x_177_ = 0;
v_env_178_ = l_Lean_Environment_setRecordingDeps(v_env_175_, v___x_177_);
v___x_179_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2);
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_176_);
v___x_181_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_181_, 0, v_env_178_);
lean_ctor_set(v___x_181_, 1, v___x_179_);
lean_ctor_set(v___x_181_, 2, v___x_180_);
lean_ctor_set(v___x_181_, 3, v_options_176_);
v___x_182_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_msgData_169_);
v___x_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_msgData_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(v_msgData_184_, v___y_185_, v___y_186_);
lean_dec(v___y_186_);
lean_dec_ref(v___y_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(lean_object* v_msg_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_ref_193_; lean_object* v___x_194_; lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
v_ref_193_ = lean_ctor_get(v___y_190_, 2);
v___x_194_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(v_msg_189_, v___y_190_, v___y_191_);
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
lean_inc(v_ref_193_);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v_ref_193_);
lean_ctor_set(v___x_199_, 1, v_a_195_);
if (v_isShared_198_ == 0)
{
lean_ctor_set_tag(v___x_197_, 1);
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg___boxed(lean_object* v_msg_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v_msg_204_, v___y_205_, v___y_206_);
lean_dec(v___y_206_);
lean_dec_ref(v___y_205_);
return v_res_208_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__0));
v___x_211_ = l_Lean_stringToMessageData(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__2));
v___x_214_ = l_Lean_stringToMessageData(v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(lean_object* v_declName_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = l_Lean_Meta_Grind_grindExt;
lean_inc(v_declName_215_);
v___x_220_ = l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(v___x_219_, v_declName_215_, v_a_217_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_236_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_236_ == 0)
{
v___x_223_ = v___x_220_;
v_isShared_224_ = v_isSharedCheck_236_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_220_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_236_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
uint8_t v___x_225_; 
v___x_225_ = lean_unbox(v_a_221_);
lean_dec(v_a_221_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
lean_del_object(v___x_223_);
v___x_226_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
v___x_227_ = l_Lean_MessageData_ofName(v_declName_215_);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_228_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v___x_230_, v_a_216_, v_a_217_);
return v___x_231_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_234_; 
lean_dec(v_declName_215_);
v___x_232_ = lean_box(0);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 0, v___x_232_);
v___x_234_ = v___x_223_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_235_, 0, v___x_232_);
v___x_234_ = v_reuseFailAlloc_235_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
return v___x_234_;
}
}
}
}
else
{
lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_244_; 
lean_dec(v_declName_215_);
v_a_237_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_244_ == 0)
{
v___x_239_ = v___x_220_;
v_isShared_240_ = v_isSharedCheck_244_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_dec(v___x_220_);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___boxed(lean_object* v_declName_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_declName_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0(lean_object* v_00_u03b1_250_, lean_object* v_msg_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v_msg_251_, v___y_252_, v___y_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___boxed(lean_object* v_00_u03b1_256_, lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0(v_00_u03b1_256_, v_msg_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
return v_res_261_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_box(0);
v___x_263_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg(){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___boxed(lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4(lean_object* v_00_u03b1_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___boxed(lean_object* v_00_u03b1_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4(v_00_u03b1_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_279_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg(){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___closed__0);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg___boxed(lean_object* v___dummy_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg();
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___lam__0(lean_object* v_addEntryFn_286_, lean_object* v___x_287_, lean_object* v_s_288_){
_start:
{
lean_object* v_importedEntries_289_; lean_object* v_state_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_298_; 
v_importedEntries_289_ = lean_ctor_get(v_s_288_, 0);
v_state_290_ = lean_ctor_get(v_s_288_, 1);
v_isSharedCheck_298_ = !lean_is_exclusive(v_s_288_);
if (v_isSharedCheck_298_ == 0)
{
v___x_292_ = v_s_288_;
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_state_290_);
lean_inc(v_importedEntries_289_);
lean_dec(v_s_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_298_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v_state_294_; lean_object* v___x_296_; 
v_state_294_ = lean_apply_2(v_addEntryFn_286_, v_state_290_, v___x_287_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v_state_294_);
v___x_296_ = v___x_292_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v_importedEntries_289_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v_state_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(lean_object* v_opts_299_, lean_object* v_opt_300_){
_start:
{
lean_object* v_name_301_; lean_object* v_defValue_302_; lean_object* v_map_303_; lean_object* v___x_304_; 
v_name_301_ = lean_ctor_get(v_opt_300_, 0);
v_defValue_302_ = lean_ctor_get(v_opt_300_, 1);
v_map_303_ = lean_ctor_get(v_opts_299_, 0);
v___x_304_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_303_, v_name_301_);
if (lean_obj_tag(v___x_304_) == 0)
{
uint8_t v___x_305_; 
v___x_305_ = lean_unbox(v_defValue_302_);
return v___x_305_;
}
else
{
lean_object* v_val_306_; 
v_val_306_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_val_306_);
lean_dec_ref_known(v___x_304_, 1);
if (lean_obj_tag(v_val_306_) == 1)
{
uint8_t v_v_307_; 
v_v_307_ = lean_ctor_get_uint8(v_val_306_, 0);
lean_dec_ref_known(v_val_306_, 0);
return v_v_307_;
}
else
{
uint8_t v___x_308_; 
lean_dec(v_val_306_);
v___x_308_ = lean_unbox(v_defValue_302_);
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5___boxed(lean_object* v_opts_309_, lean_object* v_opt_310_){
_start:
{
uint8_t v_res_311_; lean_object* v_r_312_; 
v_res_311_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(v_opts_309_, v_opt_310_);
lean_dec_ref(v_opt_310_);
lean_dec_ref(v_opts_309_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_box(1);
v___x_314_ = l_Lean_MessageData_ofFormat(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__3(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__2));
v___x_319_ = l_Lean_MessageData_ofFormat(v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6(lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
return v_x_320_;
}
else
{
lean_object* v_head_322_; lean_object* v_tail_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_345_; 
v_head_322_ = lean_ctor_get(v_x_321_, 0);
v_tail_323_ = lean_ctor_get(v_x_321_, 1);
v_isSharedCheck_345_ = !lean_is_exclusive(v_x_321_);
if (v_isSharedCheck_345_ == 0)
{
v___x_325_ = v_x_321_;
v_isShared_326_ = v_isSharedCheck_345_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_tail_323_);
lean_inc(v_head_322_);
lean_dec(v_x_321_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_345_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_before_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_343_; 
v_before_327_ = lean_ctor_get(v_head_322_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_head_322_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; 
v_unused_344_ = lean_ctor_get(v_head_322_, 1);
lean_dec(v_unused_344_);
v___x_329_ = v_head_322_;
v_isShared_330_ = v_isSharedCheck_343_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_before_327_);
lean_dec(v_head_322_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_343_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_331_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0);
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 7);
lean_ctor_set(v___x_329_, 1, v___x_331_);
lean_ctor_set(v___x_329_, 0, v_x_320_);
v___x_333_ = v___x_329_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_x_320_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_342_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_334_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__3);
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 7);
lean_ctor_set(v___x_325_, 1, v___x_334_);
lean_ctor_set(v___x_325_, 0, v___x_333_);
v___x_336_ = v___x_325_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_334_);
v___x_336_ = v_reuseFailAlloc_341_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = l_Lean_MessageData_ofSyntax(v_before_327_);
v___x_338_ = l_Lean_indentD(v___x_337_);
v___x_339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_336_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v_x_320_ = v___x_339_;
v_x_321_ = v_tail_323_;
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
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__1));
v___x_350_ = l_Lean_MessageData_ofFormat(v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg(lean_object* v_msgData_351_, lean_object* v_macroStack_352_, lean_object* v___y_353_){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_355_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_353_);
v___x_356_ = l_Lean_Elab_pp_macroStack;
v___x_357_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(v___x_355_, v___x_356_);
lean_dec_ref(v___x_355_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_dec(v_macroStack_352_);
v___x_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_358_, 0, v_msgData_351_);
return v___x_358_;
}
else
{
if (lean_obj_tag(v_macroStack_352_) == 0)
{
lean_object* v___x_359_; 
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v_msgData_351_);
return v___x_359_;
}
else
{
lean_object* v_head_360_; lean_object* v_after_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_376_; 
v_head_360_ = lean_ctor_get(v_macroStack_352_, 0);
lean_inc(v_head_360_);
v_after_361_ = lean_ctor_get(v_head_360_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_head_360_);
if (v_isSharedCheck_376_ == 0)
{
lean_object* v_unused_377_; 
v_unused_377_ = lean_ctor_get(v_head_360_, 0);
lean_dec(v_unused_377_);
v___x_363_ = v_head_360_;
v_isShared_364_ = v_isSharedCheck_376_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_after_361_);
lean_dec(v_head_360_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_376_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; lean_object* v___x_367_; 
v___x_365_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6___closed__0);
if (v_isShared_364_ == 0)
{
lean_ctor_set_tag(v___x_363_, 7);
lean_ctor_set(v___x_363_, 1, v___x_365_);
lean_ctor_set(v___x_363_, 0, v_msgData_351_);
v___x_367_ = v___x_363_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_msgData_351_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_365_);
v___x_367_ = v_reuseFailAlloc_375_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v_msgData_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_368_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___closed__2);
v___x_369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = l_Lean_MessageData_ofSyntax(v_after_361_);
v___x_371_ = l_Lean_indentD(v___x_370_);
v_msgData_372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_372_, 0, v___x_369_);
lean_ctor_set(v_msgData_372_, 1, v___x_371_);
v___x_373_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__6(v_msgData_372_, v_macroStack_352_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg___boxed(lean_object* v_msgData_378_, lean_object* v_macroStack_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg(v_msgData_378_, v_macroStack_379_, v___y_380_);
lean_dec_ref(v___y_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(lean_object* v_msgData_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; lean_object* v_env_390_; uint8_t v___x_391_; lean_object* v_env_392_; lean_object* v___x_393_; lean_object* v_toCold_394_; lean_object* v_mctx_395_; lean_object* v_lctx_396_; lean_object* v_options_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_389_ = lean_st_ref_get(v___y_387_);
v_env_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc_ref(v_env_390_);
lean_dec(v___x_389_);
v___x_391_ = 0;
v_env_392_ = l_Lean_Environment_setRecordingDeps(v_env_390_, v___x_391_);
v___x_393_ = lean_st_ref_get(v___y_385_);
v_toCold_394_ = lean_ctor_get(v___y_386_, 0);
v_mctx_395_ = lean_ctor_get(v___x_393_, 0);
lean_inc_ref(v_mctx_395_);
lean_dec(v___x_393_);
v_lctx_396_ = lean_ctor_get(v___y_384_, 2);
v_options_397_ = lean_ctor_get(v_toCold_394_, 2);
lean_inc_ref(v_options_397_);
lean_inc_ref(v_lctx_396_);
v___x_398_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_398_, 0, v_env_392_);
lean_ctor_set(v___x_398_, 1, v_mctx_395_);
lean_ctor_set(v___x_398_, 2, v_lctx_396_);
lean_ctor_set(v___x_398_, 3, v_options_397_);
v___x_399_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v_msgData_383_);
v___x_400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2___boxed(lean_object* v_msgData_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(v_msgData_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(lean_object* v_msg_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_ref_416_; lean_object* v_macroStack_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v_a_420_; lean_object* v___x_421_; lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_430_; 
v_ref_416_ = lean_ctor_get(v___y_413_, 2);
v_macroStack_417_ = lean_ctor_get(v___y_409_, 1);
v___x_418_ = l_Lean_Elab_getBetterRef(v_ref_416_, v_macroStack_417_);
v___x_419_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(v_msg_408_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref(v___x_419_);
lean_inc(v_macroStack_417_);
v___x_421_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg(v_a_420_, v_macroStack_417_, v___y_413_);
v_a_422_ = lean_ctor_get(v___x_421_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_430_ == 0)
{
v___x_424_ = v___x_421_;
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_421_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_430_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_418_);
lean_ctor_set(v___x_426_, 1, v_a_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set_tag(v___x_424_, 1);
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_428_ = v___x_424_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg___boxed(lean_object* v_msg_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(v_msg_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_439_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v___x_442_);
lean_ctor_set(v___x_443_, 1, v___x_442_);
return v___x_443_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2(void){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___redArg();
return v___x_444_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__0);
v___x_446_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2);
v___x_447_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v___x_445_);
lean_ctor_set(v___x_447_, 2, v___x_445_);
lean_ctor_set(v___x_447_, 3, v___x_445_);
lean_ctor_set(v___x_447_, 4, v___x_445_);
lean_ctor_set(v___x_447_, 5, v___x_445_);
lean_ctor_set(v___x_447_, 6, v___x_445_);
return v___x_447_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__4));
v___x_450_ = l_Lean_stringToMessageData(v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(uint8_t v___y_451_, lean_object* v_as_452_, size_t v_sz_453_, size_t v_i_454_, lean_object* v_b_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = lean_usize_dec_lt(v_i_454_, v_sz_453_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_464_, 0, v_b_455_);
return v___x_464_;
}
else
{
lean_object* v___x_465_; lean_object* v___y_467_; lean_object* v_nextMacroScope_468_; lean_object* v_ngen_469_; lean_object* v_auxDeclNGen_470_; lean_object* v_traceState_471_; lean_object* v_recordedDeps_472_; lean_object* v_messages_473_; lean_object* v_infoState_474_; lean_object* v_snapshotTasks_475_; lean_object* v___y_476_; lean_object* v___y_477_; lean_object* v___x_499_; lean_object* v_a_500_; lean_object* v___x_501_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___x_525_; lean_object* v_env_526_; lean_object* v___x_527_; lean_object* v_toEnvExtension_528_; lean_object* v_asyncMode_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_465_ = lean_box(0);
v___x_499_ = lean_box(1);
v_a_500_ = lean_array_uget_borrowed(v_as_452_, v_i_454_);
v___x_501_ = l_Lean_TSyntax_getId(v_a_500_);
v___x_525_ = lean_st_ref_get(v___y_461_);
v_env_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_env_526_);
lean_dec(v___x_525_);
v___x_527_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_528_ = lean_ctor_get(v___x_527_, 0);
v_asyncMode_529_ = lean_ctor_get(v_toEnvExtension_528_, 2);
v___x_530_ = lean_box(0);
v___x_531_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_499_, v___x_527_, v_env_526_, v_asyncMode_529_, v___x_530_);
v___x_532_ = l_Lean_NameSet_contains(v___x_531_, v___x_501_);
lean_dec(v___x_531_);
if (v___x_532_ == 0)
{
v___y_503_ = v___y_459_;
v___y_504_ = v___y_461_;
goto v___jp_502_;
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_533_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v___x_501_);
v___x_534_ = l_Lean_MessageData_ofName(v___x_501_);
v___x_535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_533_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
v___x_536_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__5);
v___x_537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
v___x_538_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(v___x_537_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_dec_ref_known(v___x_538_, 1);
v___y_503_ = v___y_459_;
v___y_504_ = v___y_461_;
goto v___jp_502_;
}
else
{
lean_dec(v___x_501_);
return v___x_538_;
}
}
v___jp_466_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_mctx_482_; lean_object* v_zetaDeltaFVarIds_483_; lean_object* v_postponed_484_; lean_object* v_diag_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_497_; 
v___x_478_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1);
v___x_479_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_479_, 0, v___y_477_);
lean_ctor_set(v___x_479_, 1, v_nextMacroScope_468_);
lean_ctor_set(v___x_479_, 2, v_ngen_469_);
lean_ctor_set(v___x_479_, 3, v_auxDeclNGen_470_);
lean_ctor_set(v___x_479_, 4, v_traceState_471_);
lean_ctor_set(v___x_479_, 5, v___x_478_);
lean_ctor_set(v___x_479_, 6, v_recordedDeps_472_);
lean_ctor_set(v___x_479_, 7, v_messages_473_);
lean_ctor_set(v___x_479_, 8, v_infoState_474_);
lean_ctor_set(v___x_479_, 9, v_snapshotTasks_475_);
v___x_480_ = lean_st_ref_put(v___y_476_, v___x_479_);
v___x_481_ = lean_st_ref_take(v___y_467_);
v_mctx_482_ = lean_ctor_get(v___x_481_, 0);
v_zetaDeltaFVarIds_483_ = lean_ctor_get(v___x_481_, 2);
v_postponed_484_ = lean_ctor_get(v___x_481_, 3);
v_diag_485_ = lean_ctor_get(v___x_481_, 4);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_497_ == 0)
{
lean_object* v_unused_498_; 
v_unused_498_ = lean_ctor_get(v___x_481_, 1);
lean_dec(v_unused_498_);
v___x_487_ = v___x_481_;
v_isShared_488_ = v_isSharedCheck_497_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_diag_485_);
lean_inc(v_postponed_484_);
lean_inc(v_zetaDeltaFVarIds_483_);
lean_inc(v_mctx_482_);
lean_dec(v___x_481_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_497_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_mctx_482_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v___x_489_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_zetaDeltaFVarIds_483_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_postponed_484_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_diag_485_);
v___x_491_ = v_reuseFailAlloc_496_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; size_t v___x_493_; size_t v___x_494_; 
v___x_492_ = lean_st_ref_put(v___y_467_, v___x_491_);
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_454_, v___x_493_);
v_i_454_ = v___x_494_;
v_b_455_ = v___x_465_;
goto _start;
}
}
}
v___jp_502_:
{
lean_object* v___x_505_; lean_object* v_env_506_; lean_object* v_nextMacroScope_507_; lean_object* v_ngen_508_; lean_object* v_auxDeclNGen_509_; lean_object* v_traceState_510_; lean_object* v_recordedDeps_511_; lean_object* v_messages_512_; lean_object* v_infoState_513_; lean_object* v_snapshotTasks_514_; lean_object* v___x_515_; lean_object* v_toEnvExtension_516_; lean_object* v_addEntryFn_517_; lean_object* v_asyncMode_518_; uint8_t v_logWrites_519_; lean_object* v___f_520_; lean_object* v___x_521_; 
v___x_505_ = lean_st_ref_take(v___y_504_);
v_env_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc_ref(v_env_506_);
v_nextMacroScope_507_ = lean_ctor_get(v___x_505_, 1);
lean_inc(v_nextMacroScope_507_);
v_ngen_508_ = lean_ctor_get(v___x_505_, 2);
lean_inc_ref(v_ngen_508_);
v_auxDeclNGen_509_ = lean_ctor_get(v___x_505_, 3);
lean_inc_ref(v_auxDeclNGen_509_);
v_traceState_510_ = lean_ctor_get(v___x_505_, 4);
lean_inc_ref(v_traceState_510_);
v_recordedDeps_511_ = lean_ctor_get(v___x_505_, 6);
lean_inc_ref(v_recordedDeps_511_);
v_messages_512_ = lean_ctor_get(v___x_505_, 7);
lean_inc_ref(v_messages_512_);
v_infoState_513_ = lean_ctor_get(v___x_505_, 8);
lean_inc_ref(v_infoState_513_);
v_snapshotTasks_514_ = lean_ctor_get(v___x_505_, 9);
lean_inc_ref(v_snapshotTasks_514_);
lean_dec(v___x_505_);
v___x_515_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_516_ = lean_ctor_get(v___x_515_, 0);
v_addEntryFn_517_ = lean_ctor_get(v___x_515_, 3);
v_asyncMode_518_ = lean_ctor_get(v_toEnvExtension_516_, 2);
v_logWrites_519_ = lean_ctor_get_uint8(v_toEnvExtension_516_, sizeof(void*)*6);
lean_inc(v_addEntryFn_517_);
v___f_520_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___lam__0), 3, 2);
lean_closure_set(v___f_520_, 0, v_addEntryFn_517_);
lean_closure_set(v___f_520_, 1, v___x_501_);
v___x_521_ = lean_box(0);
if (v_logWrites_519_ == 0)
{
lean_object* v___x_522_; 
lean_inc_ref(v_toEnvExtension_516_);
v___x_522_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_516_, v_env_506_, v___f_520_, v_asyncMode_518_, v___x_521_, v___y_451_);
v___y_467_ = v___y_503_;
v_nextMacroScope_468_ = v_nextMacroScope_507_;
v_ngen_469_ = v_ngen_508_;
v_auxDeclNGen_470_ = v_auxDeclNGen_509_;
v_traceState_471_ = v_traceState_510_;
v_recordedDeps_472_ = v_recordedDeps_511_;
v_messages_473_ = v_messages_512_;
v_infoState_474_ = v_infoState_513_;
v_snapshotTasks_475_ = v_snapshotTasks_514_;
v___y_476_ = v___y_504_;
v___y_477_ = v___x_522_;
goto v___jp_466_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_inc_ref_n(v_toEnvExtension_516_, 2);
v___x_523_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_516_, v_env_506_);
lean_dec_ref(v_env_506_);
v___x_524_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_516_, v___x_523_, v___f_520_, v_asyncMode_518_, v___x_521_, v___y_451_);
v___y_467_ = v___y_503_;
v_nextMacroScope_468_ = v_nextMacroScope_507_;
v_ngen_469_ = v_ngen_508_;
v_auxDeclNGen_470_ = v_auxDeclNGen_509_;
v_traceState_471_ = v_traceState_510_;
v_recordedDeps_472_ = v_recordedDeps_511_;
v_messages_473_ = v_messages_512_;
v_infoState_474_ = v_infoState_513_;
v_snapshotTasks_475_ = v_snapshotTasks_514_;
v___y_476_ = v___y_504_;
v___y_477_ = v___x_524_;
goto v___jp_466_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___boxed(lean_object* v___y_539_, lean_object* v_as_540_, lean_object* v_sz_541_, lean_object* v_i_542_, lean_object* v_b_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
uint8_t v___y_7984__boxed_551_; size_t v_sz_boxed_552_; size_t v_i_boxed_553_; lean_object* v_res_554_; 
v___y_7984__boxed_551_ = lean_unbox(v___y_539_);
v_sz_boxed_552_ = lean_unbox_usize(v_sz_541_);
lean_dec(v_sz_541_);
v_i_boxed_553_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(v___y_7984__boxed_551_, v_as_540_, v_sz_boxed_552_, v_i_boxed_553_, v_b_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
lean_dec(v___y_547_);
lean_dec_ref(v___y_546_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec_ref(v_as_540_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___lam__0(lean_object* v_addEntryFn_555_, lean_object* v_a_556_, lean_object* v_s_557_){
_start:
{
lean_object* v_importedEntries_558_; lean_object* v_state_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_importedEntries_558_ = lean_ctor_get(v_s_557_, 0);
v_state_559_ = lean_ctor_get(v_s_557_, 1);
v_isSharedCheck_567_ = !lean_is_exclusive(v_s_557_);
if (v_isSharedCheck_567_ == 0)
{
v___x_561_ = v_s_557_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_state_559_);
lean_inc(v_importedEntries_558_);
lean_dec(v_s_557_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_state_563_; lean_object* v___x_565_; 
v_state_563_ = lean_apply_2(v_addEntryFn_555_, v_state_559_, v_a_556_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 1, v_state_563_);
v___x_565_ = v___x_561_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_importedEntries_558_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_state_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1(void){
_start:
{
lean_object* v___x_569_; lean_object* v___x_570_; 
v___x_569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0));
v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(uint8_t v___x_571_, lean_object* v_as_572_, size_t v_sz_573_, size_t v_i_574_, lean_object* v_b_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v___x_583_; 
v___x_583_ = lean_usize_dec_lt(v_i_574_, v_sz_573_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v_b_575_);
return v___x_584_;
}
else
{
lean_object* v___x_585_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v_nextMacroScope_589_; lean_object* v_ngen_590_; lean_object* v_auxDeclNGen_591_; lean_object* v_traceState_592_; lean_object* v_recordedDeps_593_; lean_object* v_messages_594_; lean_object* v_infoState_595_; lean_object* v_snapshotTasks_596_; lean_object* v___y_597_; lean_object* v___x_619_; lean_object* v_a_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_585_ = lean_box(0);
v___x_619_ = lean_box(1);
v_a_620_ = lean_array_uget_borrowed(v_as_572_, v_i_574_);
v___x_621_ = lean_box(0);
lean_inc(v_a_620_);
v___x_622_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_620_, v___x_621_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_622_) == 0)
{
lean_object* v_a_623_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___x_647_; 
v_a_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc_n(v_a_623_, 2);
lean_dec_ref_known(v___x_622_, 1);
v___x_647_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_a_623_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_647_) == 0)
{
lean_object* v___x_648_; lean_object* v_env_649_; lean_object* v___x_650_; lean_object* v_toEnvExtension_651_; lean_object* v_asyncMode_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
lean_dec_ref_known(v___x_647_, 1);
v___x_648_ = lean_st_ref_get(v___y_581_);
v_env_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_env_649_);
lean_dec(v___x_648_);
v___x_650_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_651_ = lean_ctor_get(v___x_650_, 0);
v_asyncMode_652_ = lean_ctor_get(v_toEnvExtension_651_, 2);
v___x_653_ = lean_box(0);
v___x_654_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_619_, v___x_650_, v_env_649_, v_asyncMode_652_, v___x_653_);
v___x_655_ = l_Lean_NameSet_contains(v___x_654_, v_a_623_);
lean_dec(v___x_654_);
if (v___x_655_ == 0)
{
v___y_625_ = v___y_579_;
v___y_626_ = v___y_581_;
goto v___jp_624_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v_a_623_);
v___x_657_ = l_Lean_MessageData_ofName(v_a_623_);
v___x_658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(v___x_660_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_dec_ref_known(v___x_661_, 1);
v___y_625_ = v___y_579_;
v___y_626_ = v___y_581_;
goto v___jp_624_;
}
else
{
lean_dec(v_a_623_);
return v___x_661_;
}
}
}
else
{
lean_dec(v_a_623_);
return v___x_647_;
}
v___jp_624_:
{
lean_object* v___x_627_; lean_object* v_env_628_; lean_object* v_nextMacroScope_629_; lean_object* v_ngen_630_; lean_object* v_auxDeclNGen_631_; lean_object* v_traceState_632_; lean_object* v_recordedDeps_633_; lean_object* v_messages_634_; lean_object* v_infoState_635_; lean_object* v_snapshotTasks_636_; lean_object* v___x_637_; lean_object* v_toEnvExtension_638_; lean_object* v_addEntryFn_639_; lean_object* v_asyncMode_640_; uint8_t v_logWrites_641_; lean_object* v___f_642_; lean_object* v___x_643_; 
v___x_627_ = lean_st_ref_take(v___y_626_);
v_env_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc_ref(v_env_628_);
v_nextMacroScope_629_ = lean_ctor_get(v___x_627_, 1);
lean_inc(v_nextMacroScope_629_);
v_ngen_630_ = lean_ctor_get(v___x_627_, 2);
lean_inc_ref(v_ngen_630_);
v_auxDeclNGen_631_ = lean_ctor_get(v___x_627_, 3);
lean_inc_ref(v_auxDeclNGen_631_);
v_traceState_632_ = lean_ctor_get(v___x_627_, 4);
lean_inc_ref(v_traceState_632_);
v_recordedDeps_633_ = lean_ctor_get(v___x_627_, 6);
lean_inc_ref(v_recordedDeps_633_);
v_messages_634_ = lean_ctor_get(v___x_627_, 7);
lean_inc_ref(v_messages_634_);
v_infoState_635_ = lean_ctor_get(v___x_627_, 8);
lean_inc_ref(v_infoState_635_);
v_snapshotTasks_636_ = lean_ctor_get(v___x_627_, 9);
lean_inc_ref(v_snapshotTasks_636_);
lean_dec(v___x_627_);
v___x_637_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_638_ = lean_ctor_get(v___x_637_, 0);
v_addEntryFn_639_ = lean_ctor_get(v___x_637_, 3);
v_asyncMode_640_ = lean_ctor_get(v_toEnvExtension_638_, 2);
v_logWrites_641_ = lean_ctor_get_uint8(v_toEnvExtension_638_, sizeof(void*)*6);
lean_inc(v_addEntryFn_639_);
v___f_642_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_642_, 0, v_addEntryFn_639_);
lean_closure_set(v___f_642_, 1, v_a_623_);
v___x_643_ = lean_box(0);
if (v_logWrites_641_ == 0)
{
lean_object* v___x_644_; 
lean_inc_ref(v_toEnvExtension_638_);
v___x_644_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_638_, v_env_628_, v___f_642_, v_asyncMode_640_, v___x_643_, v___x_571_);
v___y_587_ = v___y_625_;
v___y_588_ = v___y_626_;
v_nextMacroScope_589_ = v_nextMacroScope_629_;
v_ngen_590_ = v_ngen_630_;
v_auxDeclNGen_591_ = v_auxDeclNGen_631_;
v_traceState_592_ = v_traceState_632_;
v_recordedDeps_593_ = v_recordedDeps_633_;
v_messages_594_ = v_messages_634_;
v_infoState_595_ = v_infoState_635_;
v_snapshotTasks_596_ = v_snapshotTasks_636_;
v___y_597_ = v___x_644_;
goto v___jp_586_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; 
lean_inc_ref_n(v_toEnvExtension_638_, 2);
v___x_645_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_638_, v_env_628_);
lean_dec_ref(v_env_628_);
v___x_646_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_638_, v___x_645_, v___f_642_, v_asyncMode_640_, v___x_643_, v___x_571_);
v___y_587_ = v___y_625_;
v___y_588_ = v___y_626_;
v_nextMacroScope_589_ = v_nextMacroScope_629_;
v_ngen_590_ = v_ngen_630_;
v_auxDeclNGen_591_ = v_auxDeclNGen_631_;
v_traceState_592_ = v_traceState_632_;
v_recordedDeps_593_ = v_recordedDeps_633_;
v_messages_594_ = v_messages_634_;
v_infoState_595_ = v_infoState_635_;
v_snapshotTasks_596_ = v_snapshotTasks_636_;
v___y_597_ = v___x_646_;
goto v___jp_586_;
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
v_a_662_ = lean_ctor_get(v___x_622_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_622_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_622_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_622_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_a_662_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
v___jp_586_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_mctx_602_; lean_object* v_zetaDeltaFVarIds_603_; lean_object* v_postponed_604_; lean_object* v_diag_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_617_; 
v___x_598_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1);
v___x_599_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_599_, 0, v___y_597_);
lean_ctor_set(v___x_599_, 1, v_nextMacroScope_589_);
lean_ctor_set(v___x_599_, 2, v_ngen_590_);
lean_ctor_set(v___x_599_, 3, v_auxDeclNGen_591_);
lean_ctor_set(v___x_599_, 4, v_traceState_592_);
lean_ctor_set(v___x_599_, 5, v___x_598_);
lean_ctor_set(v___x_599_, 6, v_recordedDeps_593_);
lean_ctor_set(v___x_599_, 7, v_messages_594_);
lean_ctor_set(v___x_599_, 8, v_infoState_595_);
lean_ctor_set(v___x_599_, 9, v_snapshotTasks_596_);
v___x_600_ = lean_st_ref_put(v___y_588_, v___x_599_);
v___x_601_ = lean_st_ref_take(v___y_587_);
v_mctx_602_ = lean_ctor_get(v___x_601_, 0);
v_zetaDeltaFVarIds_603_ = lean_ctor_get(v___x_601_, 2);
v_postponed_604_ = lean_ctor_get(v___x_601_, 3);
v_diag_605_ = lean_ctor_get(v___x_601_, 4);
v_isSharedCheck_617_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_617_ == 0)
{
lean_object* v_unused_618_; 
v_unused_618_ = lean_ctor_get(v___x_601_, 1);
lean_dec(v_unused_618_);
v___x_607_ = v___x_601_;
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_diag_605_);
lean_inc(v_postponed_604_);
lean_inc(v_zetaDeltaFVarIds_603_);
lean_inc(v_mctx_602_);
lean_dec(v___x_601_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_617_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_609_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 1, v___x_609_);
v___x_611_ = v___x_607_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_mctx_602_);
lean_ctor_set(v_reuseFailAlloc_616_, 1, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_616_, 2, v_zetaDeltaFVarIds_603_);
lean_ctor_set(v_reuseFailAlloc_616_, 3, v_postponed_604_);
lean_ctor_set(v_reuseFailAlloc_616_, 4, v_diag_605_);
v___x_611_ = v_reuseFailAlloc_616_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; size_t v___x_613_; size_t v___x_614_; 
v___x_612_ = lean_st_ref_put(v___y_587_, v___x_611_);
v___x_613_ = ((size_t)1ULL);
v___x_614_ = lean_usize_add(v_i_574_, v___x_613_);
v_i_574_ = v___x_614_;
v_b_575_ = v___x_585_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___boxed(lean_object* v___x_670_, lean_object* v_as_671_, lean_object* v_sz_672_, lean_object* v_i_673_, lean_object* v_b_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
uint8_t v___x_8155__boxed_682_; size_t v_sz_boxed_683_; size_t v_i_boxed_684_; lean_object* v_res_685_; 
v___x_8155__boxed_682_ = lean_unbox(v___x_670_);
v_sz_boxed_683_ = lean_unbox_usize(v_sz_672_);
lean_dec(v_sz_672_);
v_i_boxed_684_ = lean_unbox_usize(v_i_673_);
lean_dec(v_i_673_);
v_res_685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(v___x_8155__boxed_682_, v_as_671_, v_sz_boxed_683_, v_i_boxed_684_, v_b_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec_ref(v_as_671_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(uint8_t v___y_686_, lean_object* v_ids_687_, uint8_t v___x_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
if (v___y_686_ == 0)
{
lean_object* v___x_696_; size_t v_sz_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___x_696_ = lean_box(0);
v_sz_697_ = lean_array_size(v_ids_687_);
v___x_698_ = ((size_t)0ULL);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(v___x_688_, v_ids_687_, v_sz_697_, v___x_698_, v___x_696_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v___x_699_, 0);
lean_dec(v_unused_707_);
v___x_701_ = v___x_699_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_dec(v___x_699_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v___x_696_);
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_696_);
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
return v___x_699_;
}
}
else
{
lean_object* v___x_708_; size_t v_sz_709_; size_t v___x_710_; lean_object* v___x_711_; 
v___x_708_ = lean_box(0);
v_sz_709_ = lean_array_size(v_ids_687_);
v___x_710_ = ((size_t)0ULL);
v___x_711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(v___y_686_, v_ids_687_, v_sz_709_, v___x_710_, v___x_708_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v___x_711_, 0);
lean_dec(v_unused_719_);
v___x_713_ = v___x_711_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_dec(v___x_711_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_708_);
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_708_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
else
{
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed(lean_object* v___y_720_, lean_object* v_ids_721_, lean_object* v___x_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
uint8_t v___y_8302__boxed_730_; uint8_t v___x_8303__boxed_731_; lean_object* v_res_732_; 
v___y_8302__boxed_730_ = lean_unbox(v___y_720_);
v___x_8303__boxed_731_ = lean_unbox(v___x_722_);
v_res_732_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(v___y_8302__boxed_730_, v_ids_721_, v___x_8303__boxed_731_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec_ref(v_ids_721_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(lean_object* v_stx_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v___y_747_; uint8_t v___y_748_; lean_object* v_sfx_x3f_754_; lean_object* v___y_755_; lean_object* v___y_756_; 
v___x_742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1));
lean_inc(v_stx_738_);
v___x_743_ = l_Lean_Syntax_isOfKind(v_stx_738_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_761_; 
lean_dec(v_stx_738_);
v___x_761_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
return v___x_761_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_762_ = lean_unsigned_to_nat(2u);
v___x_763_ = l_Lean_Syntax_getArg(v_stx_738_, v___x_762_);
v___x_764_ = l_Lean_Syntax_isNone(v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_763_);
v___x_766_ = l_Lean_Syntax_matchesNull(v___x_763_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_dec(v___x_763_);
lean_dec(v_stx_738_);
v___x_767_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
return v___x_767_;
}
else
{
lean_object* v___x_768_; lean_object* v_sfx_x3f_769_; lean_object* v___x_770_; 
v___x_768_ = lean_unsigned_to_nat(0u);
v_sfx_x3f_769_ = l_Lean_Syntax_getArg(v___x_763_, v___x_768_);
lean_dec(v___x_763_);
v___x_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_770_, 0, v_sfx_x3f_769_);
v_sfx_x3f_754_ = v___x_770_;
v___y_755_ = v_a_739_;
v___y_756_ = v_a_740_;
goto v___jp_753_;
}
}
else
{
lean_object* v___x_771_; 
lean_dec(v___x_763_);
v___x_771_ = lean_box(0);
v_sfx_x3f_754_ = v___x_771_;
v___y_755_ = v_a_739_;
v___y_756_ = v_a_740_;
goto v___jp_753_;
}
}
v___jp_744_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___y_751_; lean_object* v___x_752_; 
v___x_749_ = lean_box(v___y_748_);
v___x_750_ = lean_box(v___x_743_);
v___y_751_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed), 10, 3);
lean_closure_set(v___y_751_, 0, v___x_749_);
lean_closure_set(v___y_751_, 1, v___y_746_);
lean_closure_set(v___y_751_, 2, v___x_750_);
v___x_752_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_751_, v___y_745_, v___y_747_);
return v___x_752_;
}
v___jp_753_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_ids_759_; 
v___x_757_ = lean_unsigned_to_nat(3u);
v___x_758_ = l_Lean_Syntax_getArg(v_stx_738_, v___x_757_);
lean_dec(v_stx_738_);
v_ids_759_ = l_Lean_Syntax_getArgs(v___x_758_);
lean_dec(v___x_758_);
if (lean_obj_tag(v_sfx_x3f_754_) == 0)
{
uint8_t v___x_760_; 
v___x_760_ = 0;
v___y_745_ = v___y_755_;
v___y_746_ = v_ids_759_;
v___y_747_ = v___y_756_;
v___y_748_ = v___x_760_;
goto v___jp_744_;
}
else
{
lean_dec_ref_known(v_sfx_x3f_754_, 1);
v___y_745_ = v___y_755_;
v___y_746_ = v_ids_759_;
v___y_747_ = v___y_756_;
v___y_748_ = v___x_743_;
goto v___jp_744_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed(lean_object* v_stx_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(v_stx_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(lean_object* v_00_u03b2_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg___boxed(lean_object* v___dummy_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg();
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0(lean_object* v_00_u03b2_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__2);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(lean_object* v_00_u03b1_785_, lean_object* v_msg_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(v_msg_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___boxed(lean_object* v_00_u03b1_795_, lean_object* v_msg_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(v_00_u03b1_795_, v_msg_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3(lean_object* v_msgData_805_, lean_object* v_macroStack_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___redArg(v_msgData_805_, v_macroStack_806_, v___y_811_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3___boxed(lean_object* v_msgData_815_, lean_object* v_macroStack_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3(v_msgData_815_, v_macroStack_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1(){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_830_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_831_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1));
v___x_832_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1));
v___x_833_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed), 4, 0);
v___x_834_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_830_, v___x_831_, v___x_832_, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___boxed(lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1();
return v_res_836_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0));
v___x_839_ = l_Lean_stringToMessageData(v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(uint8_t v___x_840_, lean_object* v_as_841_, size_t v_sz_842_, size_t v_i_843_, lean_object* v_b_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
uint8_t v___x_852_; 
v___x_852_ = lean_usize_dec_lt(v_i_843_, v_sz_842_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; 
v___x_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_853_, 0, v_b_844_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; lean_object* v_nextMacroScope_856_; lean_object* v_ngen_857_; lean_object* v_auxDeclNGen_858_; lean_object* v_traceState_859_; lean_object* v_recordedDeps_860_; lean_object* v_messages_861_; lean_object* v_infoState_862_; lean_object* v_snapshotTasks_863_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___x_888_; lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_854_ = lean_box(0);
v___x_888_ = lean_box(1);
v_a_889_ = lean_array_uget_borrowed(v_as_841_, v_i_843_);
v___x_890_ = lean_box(0);
lean_inc(v_a_889_);
v___x_891_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_889_, v___x_890_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v___y_894_; lean_object* v___y_895_; lean_object* v___x_916_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc_n(v_a_892_, 2);
lean_dec_ref_known(v___x_891_, 1);
v___x_916_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_a_892_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v___x_917_; lean_object* v_env_918_; lean_object* v___x_919_; lean_object* v_toEnvExtension_920_; lean_object* v_asyncMode_921_; lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
lean_dec_ref_known(v___x_916_, 1);
v___x_917_ = lean_st_ref_get(v___y_850_);
v_env_918_ = lean_ctor_get(v___x_917_, 0);
lean_inc_ref(v_env_918_);
lean_dec(v___x_917_);
v___x_919_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_920_ = lean_ctor_get(v___x_919_, 0);
v_asyncMode_921_ = lean_ctor_get(v_toEnvExtension_920_, 2);
v___x_922_ = lean_box(0);
v___x_923_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_888_, v___x_919_, v_env_918_, v_asyncMode_921_, v___x_922_);
v___x_924_ = l_Lean_NameSet_contains(v___x_923_, v_a_892_);
lean_dec(v___x_923_);
if (v___x_924_ == 0)
{
v___y_894_ = v___y_848_;
v___y_895_ = v___y_850_;
goto v___jp_893_;
}
else
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_925_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v_a_892_);
v___x_926_ = l_Lean_MessageData_ofName(v_a_892_);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___redArg(v___x_929_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_dec_ref_known(v___x_930_, 1);
v___y_894_ = v___y_848_;
v___y_895_ = v___y_850_;
goto v___jp_893_;
}
else
{
lean_dec(v_a_892_);
return v___x_930_;
}
}
}
else
{
lean_dec(v_a_892_);
return v___x_916_;
}
v___jp_893_:
{
lean_object* v___x_896_; lean_object* v_env_897_; lean_object* v_nextMacroScope_898_; lean_object* v_ngen_899_; lean_object* v_auxDeclNGen_900_; lean_object* v_traceState_901_; lean_object* v_recordedDeps_902_; lean_object* v_messages_903_; lean_object* v_infoState_904_; lean_object* v_snapshotTasks_905_; lean_object* v___x_906_; lean_object* v_toEnvExtension_907_; lean_object* v_addEntryFn_908_; lean_object* v_asyncMode_909_; uint8_t v_logWrites_910_; lean_object* v___f_911_; lean_object* v___x_912_; 
v___x_896_ = lean_st_ref_take(v___y_895_);
v_env_897_ = lean_ctor_get(v___x_896_, 0);
lean_inc_ref(v_env_897_);
v_nextMacroScope_898_ = lean_ctor_get(v___x_896_, 1);
lean_inc(v_nextMacroScope_898_);
v_ngen_899_ = lean_ctor_get(v___x_896_, 2);
lean_inc_ref(v_ngen_899_);
v_auxDeclNGen_900_ = lean_ctor_get(v___x_896_, 3);
lean_inc_ref(v_auxDeclNGen_900_);
v_traceState_901_ = lean_ctor_get(v___x_896_, 4);
lean_inc_ref(v_traceState_901_);
v_recordedDeps_902_ = lean_ctor_get(v___x_896_, 6);
lean_inc_ref(v_recordedDeps_902_);
v_messages_903_ = lean_ctor_get(v___x_896_, 7);
lean_inc_ref(v_messages_903_);
v_infoState_904_ = lean_ctor_get(v___x_896_, 8);
lean_inc_ref(v_infoState_904_);
v_snapshotTasks_905_ = lean_ctor_get(v___x_896_, 9);
lean_inc_ref(v_snapshotTasks_905_);
lean_dec(v___x_896_);
v___x_906_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_907_ = lean_ctor_get(v___x_906_, 0);
v_addEntryFn_908_ = lean_ctor_get(v___x_906_, 3);
v_asyncMode_909_ = lean_ctor_get(v_toEnvExtension_907_, 2);
v_logWrites_910_ = lean_ctor_get_uint8(v_toEnvExtension_907_, sizeof(void*)*6);
lean_inc(v_addEntryFn_908_);
v___f_911_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_911_, 0, v_addEntryFn_908_);
lean_closure_set(v___f_911_, 1, v_a_892_);
v___x_912_ = lean_box(0);
if (v_logWrites_910_ == 0)
{
lean_object* v___x_913_; 
lean_inc_ref(v_toEnvExtension_907_);
v___x_913_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_907_, v_env_897_, v___f_911_, v_asyncMode_909_, v___x_912_, v___x_840_);
v_nextMacroScope_856_ = v_nextMacroScope_898_;
v_ngen_857_ = v_ngen_899_;
v_auxDeclNGen_858_ = v_auxDeclNGen_900_;
v_traceState_859_ = v_traceState_901_;
v_recordedDeps_860_ = v_recordedDeps_902_;
v_messages_861_ = v_messages_903_;
v_infoState_862_ = v_infoState_904_;
v_snapshotTasks_863_ = v_snapshotTasks_905_;
v___y_864_ = v___y_894_;
v___y_865_ = v___y_895_;
v___y_866_ = v___x_913_;
goto v___jp_855_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_inc_ref_n(v_toEnvExtension_907_, 2);
v___x_914_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_907_, v_env_897_);
lean_dec_ref(v_env_897_);
v___x_915_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_907_, v___x_914_, v___f_911_, v_asyncMode_909_, v___x_912_, v___x_840_);
v_nextMacroScope_856_ = v_nextMacroScope_898_;
v_ngen_857_ = v_ngen_899_;
v_auxDeclNGen_858_ = v_auxDeclNGen_900_;
v_traceState_859_ = v_traceState_901_;
v_recordedDeps_860_ = v_recordedDeps_902_;
v_messages_861_ = v_messages_903_;
v_infoState_862_ = v_infoState_904_;
v_snapshotTasks_863_ = v_snapshotTasks_905_;
v___y_864_ = v___y_894_;
v___y_865_ = v___y_895_;
v___y_866_ = v___x_915_;
goto v___jp_855_;
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
v_a_931_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_891_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_891_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
v___jp_855_:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v_mctx_871_; lean_object* v_zetaDeltaFVarIds_872_; lean_object* v_postponed_873_; lean_object* v_diag_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_886_; 
v___x_867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__1);
v___x_868_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_868_, 0, v___y_866_);
lean_ctor_set(v___x_868_, 1, v_nextMacroScope_856_);
lean_ctor_set(v___x_868_, 2, v_ngen_857_);
lean_ctor_set(v___x_868_, 3, v_auxDeclNGen_858_);
lean_ctor_set(v___x_868_, 4, v_traceState_859_);
lean_ctor_set(v___x_868_, 5, v___x_867_);
lean_ctor_set(v___x_868_, 6, v_recordedDeps_860_);
lean_ctor_set(v___x_868_, 7, v_messages_861_);
lean_ctor_set(v___x_868_, 8, v_infoState_862_);
lean_ctor_set(v___x_868_, 9, v_snapshotTasks_863_);
v___x_869_ = lean_st_ref_put(v___y_865_, v___x_868_);
v___x_870_ = lean_st_ref_take(v___y_864_);
v_mctx_871_ = lean_ctor_get(v___x_870_, 0);
v_zetaDeltaFVarIds_872_ = lean_ctor_get(v___x_870_, 2);
v_postponed_873_ = lean_ctor_get(v___x_870_, 3);
v_diag_874_ = lean_ctor_get(v___x_870_, 4);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v___x_870_, 1);
lean_dec(v_unused_887_);
v___x_876_ = v___x_870_;
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_diag_874_);
lean_inc(v_postponed_873_);
lean_inc(v_zetaDeltaFVarIds_872_);
lean_inc(v_mctx_871_);
lean_dec(v___x_870_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_886_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___closed__3);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 1, v___x_878_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_mctx_871_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_885_, 2, v_zetaDeltaFVarIds_872_);
lean_ctor_set(v_reuseFailAlloc_885_, 3, v_postponed_873_);
lean_ctor_set(v_reuseFailAlloc_885_, 4, v_diag_874_);
v___x_880_ = v_reuseFailAlloc_885_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; size_t v___x_882_; size_t v___x_883_; 
v___x_881_ = lean_st_ref_put(v___y_864_, v___x_880_);
v___x_882_ = ((size_t)1ULL);
v___x_883_ = lean_usize_add(v_i_843_, v___x_882_);
v_i_843_ = v___x_883_;
v_b_844_ = v___x_854_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___boxed(lean_object* v___x_939_, lean_object* v_as_940_, lean_object* v_sz_941_, lean_object* v_i_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
uint8_t v___x_3319__boxed_951_; size_t v_sz_boxed_952_; size_t v_i_boxed_953_; lean_object* v_res_954_; 
v___x_3319__boxed_951_ = lean_unbox(v___x_939_);
v_sz_boxed_952_ = lean_unbox_usize(v_sz_941_);
lean_dec(v_sz_941_);
v_i_boxed_953_ = lean_unbox_usize(v_i_942_);
lean_dec(v_i_942_);
v_res_954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(v___x_3319__boxed_951_, v_as_940_, v_sz_boxed_952_, v_i_boxed_953_, v_b_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v_as_940_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(uint8_t v___x_955_, lean_object* v_ids_956_, size_t v_sz_957_, size_t v___x_958_, lean_object* v___x_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(v___x_955_, v_ids_956_, v_sz_957_, v___x_958_, v___x_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v___x_967_, 0);
lean_dec(v_unused_975_);
v___x_969_ = v___x_967_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_dec(v___x_967_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_959_);
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v___x_959_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
else
{
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed(lean_object* v___x_976_, lean_object* v_ids_977_, lean_object* v_sz_978_, lean_object* v___x_979_, lean_object* v___x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
uint8_t v___x_3466__boxed_988_; size_t v_sz_boxed_989_; size_t v___x_3467__boxed_990_; lean_object* v_res_991_; 
v___x_3466__boxed_988_ = lean_unbox(v___x_976_);
v_sz_boxed_989_ = lean_unbox_usize(v_sz_978_);
lean_dec(v_sz_978_);
v___x_3467__boxed_990_ = lean_unbox_usize(v___x_979_);
lean_dec(v___x_979_);
v_res_991_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(v___x_3466__boxed_988_, v_ids_977_, v_sz_boxed_989_, v___x_3467__boxed_990_, v___x_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
lean_dec(v___y_986_);
lean_dec_ref(v___y_985_);
lean_dec(v___y_984_);
lean_dec_ref(v___y_983_);
lean_dec(v___y_982_);
lean_dec_ref(v___y_981_);
lean_dec_ref(v_ids_977_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(lean_object* v_stx_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1));
lean_inc(v_stx_999_);
v___x_1004_ = l_Lean_Syntax_isOfKind(v_stx_999_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
lean_dec(v_stx_999_);
v___x_1005_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg();
return v___x_1005_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v_ids_1008_; lean_object* v___x_1009_; size_t v_sz_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___f_1014_; lean_object* v___x_1015_; 
v___x_1006_ = lean_unsigned_to_nat(2u);
v___x_1007_ = l_Lean_Syntax_getArg(v_stx_999_, v___x_1006_);
lean_dec(v_stx_999_);
v_ids_1008_ = l_Lean_Syntax_getArgs(v___x_1007_);
lean_dec(v___x_1007_);
v___x_1009_ = lean_box(0);
v_sz_1010_ = lean_array_size(v_ids_1008_);
v___x_1011_ = lean_box(v___x_1004_);
v___x_1012_ = lean_box_usize(v_sz_1010_);
v___x_1013_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1));
v___f_1014_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1014_, 0, v___x_1011_);
lean_closure_set(v___f_1014_, 1, v_ids_1008_);
lean_closure_set(v___f_1014_, 2, v___x_1012_);
lean_closure_set(v___f_1014_, 3, v___x_1013_);
lean_closure_set(v___f_1014_, 4, v___x_1009_);
v___x_1015_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1014_, v_a_1000_, v_a_1001_);
return v___x_1015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed(lean_object* v_stx_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(v_stx_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1(){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1026_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1027_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1));
v___x_1028_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1));
v___x_1029_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed), 4, 0);
v___x_1030_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1026_, v___x_1027_, v___x_1028_, v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___boxed(lean_object* v_a_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1();
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(lean_object* v_items_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig));
v___x_1056_ = l_Lean_Elab_Tactic_Grind_elabConfigItems___redArg(v___x_1055_, v_items_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg___boxed(lean_object* v_items_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_items_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec_ref(v_a_1058_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(lean_object* v_items_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_items_1063_, v_a_1064_, v_a_1068_, v_a_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___boxed(lean_object* v_items_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(v_items_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(lean_object* v_init_1081_, lean_object* v_x_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
if (lean_obj_tag(v_x_1082_) == 0)
{
lean_object* v_k_1088_; lean_object* v_l_1089_; lean_object* v_r_1090_; lean_object* v___x_1091_; 
v_k_1088_ = lean_ctor_get(v_x_1082_, 1);
lean_inc(v_k_1088_);
v_l_1089_ = lean_ctor_get(v_x_1082_, 3);
lean_inc(v_l_1089_);
v_r_1090_ = lean_ctor_get(v_x_1082_, 4);
lean_inc(v_r_1090_);
lean_dec_ref_known(v_x_1082_, 5);
v___x_1091_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_init_1081_, v_l_1089_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v_a_1093_; lean_object* v___x_1094_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v___x_1091_, 1);
v_a_1093_ = lean_ctor_get(v_a_1092_, 0);
lean_inc_n(v_a_1093_, 2);
lean_dec(v_a_1092_);
v___x_1094_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_a_1093_, v_k_1088_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; 
lean_dec(v_a_1093_);
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v_init_1081_ = v_a_1095_;
v_x_1082_ = v_r_1090_;
goto _start;
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1110_; 
v_a_1097_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1099_ = v___x_1094_;
v_isShared_1100_ = v_isSharedCheck_1110_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1094_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1110_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
uint8_t v___x_1101_; 
v___x_1101_ = l_Lean_Exception_isInterrupt(v_a_1097_);
if (v___x_1101_ == 0)
{
uint8_t v___x_1102_; 
lean_inc(v_a_1097_);
v___x_1102_ = l_Lean_Exception_isRuntime(v_a_1097_);
if (v___x_1102_ == 0)
{
lean_del_object(v___x_1099_);
lean_dec(v_a_1097_);
v_init_1081_ = v_a_1093_;
v_x_1082_ = v_r_1090_;
goto _start;
}
else
{
lean_object* v___x_1105_; 
lean_dec(v_a_1093_);
lean_dec(v_r_1090_);
if (v_isShared_1100_ == 0)
{
v___x_1105_ = v___x_1099_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1097_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
else
{
lean_object* v___x_1108_; 
lean_dec(v_a_1093_);
lean_dec(v_r_1090_);
if (v_isShared_1100_ == 0)
{
v___x_1108_ = v___x_1099_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1097_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
else
{
lean_dec(v_r_1090_);
lean_dec(v_k_1088_);
return v___x_1091_;
}
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1111_, 0, v_init_1081_);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0___boxed(lean_object* v_init_1113_, lean_object* v_x_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_init_1113_, v_x_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
lean_dec(v___y_1116_);
lean_dec_ref(v___y_1115_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(lean_object* v_config_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1128_ = lean_box(1);
v___x_1129_ = l_Lean_Meta_Grind_mkDefaultParams(v_config_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1198_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1132_ = v___x_1129_;
v_isShared_1133_ = v_isSharedCheck_1198_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1129_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1198_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_config_1134_; lean_object* v_identity_1135_; lean_object* v_extensions_1136_; lean_object* v_extra_1137_; lean_object* v_extraInj_1138_; lean_object* v_extraFacts_1139_; lean_object* v_symPrios_1140_; lean_object* v_norm_1141_; lean_object* v_normProcs_1142_; lean_object* v_anchorRefs_x3f_1143_; uint8_t v_interactive_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1197_; 
v_config_1134_ = lean_ctor_get(v_a_1130_, 0);
v_identity_1135_ = lean_ctor_get(v_a_1130_, 1);
v_extensions_1136_ = lean_ctor_get(v_a_1130_, 2);
v_extra_1137_ = lean_ctor_get(v_a_1130_, 3);
v_extraInj_1138_ = lean_ctor_get(v_a_1130_, 4);
v_extraFacts_1139_ = lean_ctor_get(v_a_1130_, 5);
v_symPrios_1140_ = lean_ctor_get(v_a_1130_, 6);
v_norm_1141_ = lean_ctor_get(v_a_1130_, 7);
v_normProcs_1142_ = lean_ctor_get(v_a_1130_, 8);
v_anchorRefs_x3f_1143_ = lean_ctor_get(v_a_1130_, 9);
v_interactive_1144_ = lean_ctor_get_uint8(v_a_1130_, sizeof(void*)*10);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_a_1130_);
if (v_isSharedCheck_1197_ == 0)
{
v___x_1146_ = v_a_1130_;
v_isShared_1147_ = v_isSharedCheck_1197_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_anchorRefs_x3f_1143_);
lean_inc(v_normProcs_1142_);
lean_inc(v_norm_1141_);
lean_inc(v_symPrios_1140_);
lean_inc(v_extraFacts_1139_);
lean_inc(v_extraInj_1138_);
lean_inc(v_extra_1137_);
lean_inc(v_extensions_1136_);
lean_inc(v_identity_1135_);
lean_inc(v_config_1134_);
lean_dec(v_a_1130_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1197_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___y_1149_; lean_object* v___x_1156_; lean_object* v_a_1158_; lean_object* v___x_1177_; lean_object* v_ematch_1178_; lean_object* v___x_1179_; lean_object* v_env_1180_; lean_object* v___x_1181_; lean_object* v_toEnvExtension_1182_; lean_object* v_asyncMode_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1177_ = lean_array_get_borrowed(v___x_1127_, v_extensions_1136_, v___x_1156_);
v_ematch_1178_ = lean_ctor_get(v___x_1177_, 3);
v___x_1179_ = lean_st_ref_get(v_a_1125_);
v_env_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc_ref(v_env_1180_);
lean_dec(v___x_1179_);
v___x_1181_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_1182_ = lean_ctor_get(v___x_1181_, 0);
v_asyncMode_1183_ = lean_ctor_get(v_toEnvExtension_1182_, 2);
v___x_1184_ = lean_box(0);
v___x_1185_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1128_, v___x_1181_, v_env_1180_, v_asyncMode_1183_, v___x_1184_);
lean_inc_ref(v_ematch_1178_);
v___x_1186_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_ematch_1178_, v___x_1185_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v_a_1188_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v_a_1188_ = lean_ctor_get(v_a_1187_, 0);
lean_inc(v_a_1188_);
lean_dec(v_a_1187_);
v_a_1158_ = v_a_1188_;
goto v___jp_1157_;
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_del_object(v___x_1146_);
lean_dec(v_anchorRefs_x3f_1143_);
lean_dec_ref(v_normProcs_1142_);
lean_dec_ref(v_norm_1141_);
lean_dec_ref(v_symPrios_1140_);
lean_dec_ref(v_extraFacts_1139_);
lean_dec_ref(v_extraInj_1138_);
lean_dec_ref(v_extra_1137_);
lean_dec_ref(v_extensions_1136_);
lean_dec(v_identity_1135_);
lean_dec_ref(v_config_1134_);
lean_del_object(v___x_1132_);
v_a_1189_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1186_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1186_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
v___jp_1148_:
{
lean_object* v___x_1151_; 
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 2, v___y_1149_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_config_1134_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v_identity_1135_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v___y_1149_);
lean_ctor_set(v_reuseFailAlloc_1155_, 3, v_extra_1137_);
lean_ctor_set(v_reuseFailAlloc_1155_, 4, v_extraInj_1138_);
lean_ctor_set(v_reuseFailAlloc_1155_, 5, v_extraFacts_1139_);
lean_ctor_set(v_reuseFailAlloc_1155_, 6, v_symPrios_1140_);
lean_ctor_set(v_reuseFailAlloc_1155_, 7, v_norm_1141_);
lean_ctor_set(v_reuseFailAlloc_1155_, 8, v_normProcs_1142_);
lean_ctor_set(v_reuseFailAlloc_1155_, 9, v_anchorRefs_x3f_1143_);
lean_ctor_set_uint8(v_reuseFailAlloc_1155_, sizeof(void*)*10, v_interactive_1144_);
v___x_1151_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 0, v___x_1151_);
v___x_1153_ = v___x_1132_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
v___jp_1157_:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = lean_array_get_size(v_extensions_1136_);
v___x_1160_ = lean_nat_dec_lt(v___x_1156_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_dec_ref(v_a_1158_);
v___y_1149_ = v_extensions_1136_;
goto v___jp_1148_;
}
else
{
lean_object* v_v_1161_; lean_object* v_casesTypes_1162_; lean_object* v_extThms_1163_; lean_object* v_funCC_1164_; lean_object* v_inj_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1175_; 
v_v_1161_ = lean_array_fget(v_extensions_1136_, v___x_1156_);
v_casesTypes_1162_ = lean_ctor_get(v_v_1161_, 0);
v_extThms_1163_ = lean_ctor_get(v_v_1161_, 1);
v_funCC_1164_ = lean_ctor_get(v_v_1161_, 2);
v_inj_1165_ = lean_ctor_get(v_v_1161_, 4);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_v_1161_);
if (v_isSharedCheck_1175_ == 0)
{
lean_object* v_unused_1176_; 
v_unused_1176_ = lean_ctor_get(v_v_1161_, 3);
lean_dec(v_unused_1176_);
v___x_1167_ = v_v_1161_;
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_inj_1165_);
lean_inc(v_funCC_1164_);
lean_inc(v_extThms_1163_);
lean_inc(v_casesTypes_1162_);
lean_dec(v_v_1161_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1175_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v_xs_x27_1170_; lean_object* v___x_1172_; 
v___x_1169_ = lean_box(0);
v_xs_x27_1170_ = lean_array_fset(v_extensions_1136_, v___x_1156_, v___x_1169_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 3, v_a_1158_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_casesTypes_1162_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_extThms_1163_);
lean_ctor_set(v_reuseFailAlloc_1174_, 2, v_funCC_1164_);
lean_ctor_set(v_reuseFailAlloc_1174_, 3, v_a_1158_);
lean_ctor_set(v_reuseFailAlloc_1174_, 4, v_inj_1165_);
v___x_1172_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_array_fset(v_xs_x27_1170_, v___x_1156_, v___x_1172_);
v___y_1149_ = v___x_1173_;
goto v___jp_1148_;
}
}
}
}
}
}
}
else
{
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams___boxed(lean_object* v_config_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_config_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(lean_object* v_x_1206_, lean_object* v_____s_1207_){
_start:
{
lean_object* v_snd_1208_; lean_object* v_r_1209_; lean_object* v___x_1210_; 
v_snd_1208_ = lean_ctor_get(v_x_1206_, 1);
v_r_1209_ = lean_nat_add(v_____s_1207_, v_snd_1208_);
v___x_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1210_, 0, v_r_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0___boxed(lean_object* v_x_1211_, lean_object* v_____s_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(v_x_1211_, v_____s_1212_);
lean_dec(v_____s_1212_);
lean_dec_ref(v_x_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0(lean_object* v_f_1214_, lean_object* v_s_1215_, lean_object* v_a_1216_, lean_object* v_b_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_a_1216_);
lean_ctor_set(v___x_1218_, 1, v_b_1217_);
v___x_1219_ = lean_apply_2(v_f_1214_, v___x_1218_, v_s_1215_);
if (lean_obj_tag(v___x_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
v_a_1220_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1219_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_a_1228_ = lean_ctor_get(v___x_1219_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1219_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1219_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1236_, lean_object* v_keys_1237_, lean_object* v_vals_1238_, lean_object* v_i_1239_, lean_object* v_acc_1240_){
_start:
{
lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1241_ = lean_array_get_size(v_keys_1237_);
v___x_1242_ = lean_nat_dec_lt(v_i_1239_, v___x_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___x_1243_; 
lean_dec(v_i_1239_);
lean_dec_ref(v_f_1236_);
v___x_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1243_, 0, v_acc_1240_);
return v___x_1243_;
}
else
{
lean_object* v_k_1244_; lean_object* v_v_1245_; lean_object* v___x_1246_; 
v_k_1244_ = lean_array_fget_borrowed(v_keys_1237_, v_i_1239_);
v_v_1245_ = lean_array_fget_borrowed(v_vals_1238_, v_i_1239_);
lean_inc_ref(v_f_1236_);
lean_inc(v_v_1245_);
lean_inc(v_k_1244_);
v___x_1246_ = lean_apply_3(v_f_1236_, v_acc_1240_, v_k_1244_, v_v_1245_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_dec(v_i_1239_);
lean_dec_ref(v_f_1236_);
return v___x_1246_;
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v___x_1248_ = lean_unsigned_to_nat(1u);
v___x_1249_ = lean_nat_add(v_i_1239_, v___x_1248_);
lean_dec(v_i_1239_);
v_i_1239_ = v___x_1249_;
v_acc_1240_ = v_a_1247_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1251_, lean_object* v_keys_1252_, lean_object* v_vals_1253_, lean_object* v_i_1254_, lean_object* v_acc_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1251_, v_keys_1252_, v_vals_1253_, v_i_1254_, v_acc_1255_);
lean_dec_ref(v_vals_1253_);
lean_dec_ref(v_keys_1252_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1257_, lean_object* v_as_1258_, size_t v_i_1259_, size_t v_stop_1260_, lean_object* v_b_1261_){
_start:
{
lean_object* v_a_1263_; lean_object* v___y_1268_; uint8_t v___x_1270_; 
v___x_1270_ = lean_usize_dec_eq(v_i_1259_, v_stop_1260_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_array_uget_borrowed(v_as_1258_, v_i_1259_);
switch(lean_obj_tag(v___x_1271_))
{
case 0:
{
lean_object* v_key_1272_; lean_object* v_val_1273_; lean_object* v___x_1274_; 
v_key_1272_ = lean_ctor_get(v___x_1271_, 0);
v_val_1273_ = lean_ctor_get(v___x_1271_, 1);
lean_inc_ref(v_f_1257_);
lean_inc(v_val_1273_);
lean_inc(v_key_1272_);
v___x_1274_ = lean_apply_3(v_f_1257_, v_b_1261_, v_key_1272_, v_val_1273_);
v___y_1268_ = v___x_1274_;
goto v___jp_1267_;
}
case 1:
{
lean_object* v_node_1275_; lean_object* v___x_1276_; 
v_node_1275_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_node_1275_);
lean_inc_ref(v_f_1257_);
v___x_1276_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1257_, v_node_1275_, v_b_1261_);
v___y_1268_ = v___x_1276_;
goto v___jp_1267_;
}
default: 
{
v_a_1263_ = v_b_1261_;
goto v___jp_1262_;
}
}
}
else
{
lean_object* v___x_1277_; 
lean_dec_ref(v_f_1257_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v_b_1261_);
return v___x_1277_;
}
v___jp_1262_:
{
size_t v___x_1264_; size_t v___x_1265_; 
v___x_1264_ = ((size_t)1ULL);
v___x_1265_ = lean_usize_add(v_i_1259_, v___x_1264_);
v_i_1259_ = v___x_1265_;
v_b_1261_ = v_a_1263_;
goto _start;
}
v___jp_1267_:
{
if (lean_obj_tag(v___y_1268_) == 0)
{
lean_dec_ref(v_f_1257_);
return v___y_1268_;
}
else
{
lean_object* v_a_1269_; 
v_a_1269_ = lean_ctor_get(v___y_1268_, 0);
lean_inc(v_a_1269_);
lean_dec_ref_known(v___y_1268_, 1);
v_a_1263_ = v_a_1269_;
goto v___jp_1262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1278_, lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
if (lean_obj_tag(v_x_1279_) == 0)
{
lean_object* v_es_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1294_; 
v_es_1281_ = lean_ctor_get(v_x_1279_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_x_1279_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1283_ = v_x_1279_;
v_isShared_1284_ = v_isSharedCheck_1294_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_es_1281_);
lean_dec(v_x_1279_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1294_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_array_get_size(v_es_1281_);
v___x_1287_ = lean_nat_dec_lt(v___x_1285_, v___x_1286_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1289_; 
lean_dec_ref(v_es_1281_);
lean_dec_ref(v_f_1278_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set_tag(v___x_1283_, 1);
lean_ctor_set(v___x_1283_, 0, v_x_1280_);
v___x_1289_ = v___x_1283_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_x_1280_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
else
{
size_t v___x_1291_; size_t v___x_1292_; lean_object* v___x_1293_; 
lean_del_object(v___x_1283_);
v___x_1291_ = ((size_t)0ULL);
v___x_1292_ = lean_usize_of_nat(v___x_1286_);
v___x_1293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1278_, v_es_1281_, v___x_1291_, v___x_1292_, v_x_1280_);
lean_dec_ref(v_es_1281_);
return v___x_1293_;
}
}
}
else
{
lean_object* v_ks_1295_; lean_object* v_vs_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_ks_1295_ = lean_ctor_get(v_x_1279_, 0);
lean_inc_ref(v_ks_1295_);
v_vs_1296_ = lean_ctor_get(v_x_1279_, 1);
lean_inc_ref(v_vs_1296_);
lean_dec_ref_known(v_x_1279_, 2);
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1278_, v_ks_1295_, v_vs_1296_, v___x_1297_, v_x_1280_);
lean_dec_ref(v_vs_1296_);
lean_dec_ref(v_ks_1295_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1299_, lean_object* v_as_1300_, lean_object* v_i_1301_, lean_object* v_stop_1302_, lean_object* v_b_1303_){
_start:
{
size_t v_i_boxed_1304_; size_t v_stop_boxed_1305_; lean_object* v_res_1306_; 
v_i_boxed_1304_ = lean_unbox_usize(v_i_1301_);
lean_dec(v_i_1301_);
v_stop_boxed_1305_ = lean_unbox_usize(v_stop_1302_);
lean_dec(v_stop_1302_);
v_res_1306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1299_, v_as_1300_, v_i_boxed_1304_, v_stop_boxed_1305_, v_b_1303_);
lean_dec_ref(v_as_1300_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(lean_object* v_map_1307_, lean_object* v_init_1308_, lean_object* v_f_1309_){
_start:
{
lean_object* v___f_1310_; lean_object* v___x_1311_; lean_object* v_a_1312_; 
v___f_1310_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1310_, 0, v_f_1309_);
lean_inc_ref(v_map_1307_);
v___x_1311_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v___f_1310_, v_map_1307_, v_init_1308_);
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref(v___x_1311_);
return v_a_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___boxed(lean_object* v_map_1313_, lean_object* v_init_1314_, lean_object* v_f_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_map_1313_, v_init_1314_, v_f_1315_);
lean_dec_ref(v_map_1313_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(lean_object* v_cs_1318_){
_start:
{
lean_object* v___f_1319_; lean_object* v_r_1320_; lean_object* v___x_1321_; 
v___f_1319_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0));
v_r_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_cs_1318_, v_r_1320_, v___f_1319_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___boxed(lean_object* v_cs_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(v_cs_1322_);
lean_dec_ref(v_cs_1322_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(lean_object* v_00_u03c3_1324_, lean_object* v_00_u03b2_1325_, lean_object* v_map_1326_, lean_object* v_init_1327_, lean_object* v_f_1328_){
_start:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_map_1326_, v_init_1327_, v_f_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___boxed(lean_object* v_00_u03c3_1330_, lean_object* v_00_u03b2_1331_, lean_object* v_map_1332_, lean_object* v_init_1333_, lean_object* v_f_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(v_00_u03c3_1330_, v_00_u03b2_1331_, v_map_1332_, v_init_1333_, v_f_1334_);
lean_dec_ref(v_map_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0___redArg(lean_object* v_map_1336_, lean_object* v_f_1337_, lean_object* v_init_1338_){
_start:
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1337_, v_map_1336_, v_init_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0(lean_object* v_00_u03c3_1340_, lean_object* v_00_u03c3_1341_, lean_object* v_00_u03b2_1342_, lean_object* v_map_1343_, lean_object* v_f_1344_, lean_object* v_init_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1344_, v_map_1343_, v_init_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1347_, lean_object* v_00_u03c3_1348_, lean_object* v_00_u03b1_1349_, lean_object* v_00_u03b2_1350_, lean_object* v_f_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1351_, v_x_1352_, v_x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1355_, lean_object* v_00_u03b2_1356_, lean_object* v_00_u03c3_1357_, lean_object* v_00_u03c3_1358_, lean_object* v_f_1359_, lean_object* v_as_1360_, size_t v_i_1361_, size_t v_stop_1362_, lean_object* v_b_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1359_, v_as_1360_, v_i_1361_, v_stop_1362_, v_b_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1365_, lean_object* v_00_u03b2_1366_, lean_object* v_00_u03c3_1367_, lean_object* v_00_u03c3_1368_, lean_object* v_f_1369_, lean_object* v_as_1370_, lean_object* v_i_1371_, lean_object* v_stop_1372_, lean_object* v_b_1373_){
_start:
{
size_t v_i_boxed_1374_; size_t v_stop_boxed_1375_; lean_object* v_res_1376_; 
v_i_boxed_1374_ = lean_unbox_usize(v_i_1371_);
lean_dec(v_i_1371_);
v_stop_boxed_1375_ = lean_unbox_usize(v_stop_1372_);
lean_dec(v_stop_1372_);
v_res_1376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1365_, v_00_u03b2_1366_, v_00_u03c3_1367_, v_00_u03c3_1368_, v_f_1369_, v_as_1370_, v_i_boxed_1374_, v_stop_boxed_1375_, v_b_1373_);
lean_dec_ref(v_as_1370_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_1377_, lean_object* v_00_u03c3_1378_, lean_object* v_00_u03b1_1379_, lean_object* v_00_u03b2_1380_, lean_object* v_f_1381_, lean_object* v_keys_1382_, lean_object* v_vals_1383_, lean_object* v_heq_1384_, lean_object* v_i_1385_, lean_object* v_acc_1386_){
_start:
{
lean_object* v___x_1387_; 
v___x_1387_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1381_, v_keys_1382_, v_vals_1383_, v_i_1385_, v_acc_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1388_, lean_object* v_00_u03c3_1389_, lean_object* v_00_u03b1_1390_, lean_object* v_00_u03b2_1391_, lean_object* v_f_1392_, lean_object* v_keys_1393_, lean_object* v_vals_1394_, lean_object* v_heq_1395_, lean_object* v_i_1396_, lean_object* v_acc_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_1388_, v_00_u03c3_1389_, v_00_u03b1_1390_, v_00_u03b2_1391_, v_f_1392_, v_keys_1393_, v_vals_1394_, v_heq_1395_, v_i_1396_, v_acc_1397_);
lean_dec_ref(v_vals_1394_);
lean_dec_ref(v_keys_1393_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(lean_object* v_as_1399_, size_t v_i_1400_, size_t v_stop_1401_, lean_object* v_b_1402_){
_start:
{
lean_object* v___y_1404_; uint8_t v___x_1408_; 
v___x_1408_ = lean_usize_dec_eq(v_i_1400_, v_stop_1401_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v_fst_1410_; 
v___x_1409_ = lean_array_uget(v_as_1399_, v_i_1400_);
v_fst_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_fst_1410_);
if (lean_obj_tag(v_fst_1410_) == 0)
{
lean_object* v_snd_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1420_; 
v_snd_1411_ = lean_ctor_get(v___x_1409_, 1);
v_isSharedCheck_1420_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1420_ == 0)
{
lean_object* v_unused_1421_; 
v_unused_1421_ = lean_ctor_get(v___x_1409_, 0);
lean_dec(v_unused_1421_);
v___x_1413_ = v___x_1409_;
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_snd_1411_);
lean_dec(v___x_1409_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1420_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_declName_1415_; lean_object* v___x_1417_; 
v_declName_1415_ = lean_ctor_get(v_fst_1410_, 0);
lean_inc(v_declName_1415_);
lean_dec_ref_known(v_fst_1410_, 1);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 0, v_declName_1415_);
v___x_1417_ = v___x_1413_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_declName_1415_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v_snd_1411_);
v___x_1417_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_array_push(v_b_1402_, v___x_1417_);
v___y_1404_ = v___x_1418_;
goto v___jp_1403_;
}
}
}
else
{
lean_dec(v_fst_1410_);
lean_dec(v___x_1409_);
v___y_1404_ = v_b_1402_;
goto v___jp_1403_;
}
}
else
{
return v_b_1402_;
}
v___jp_1403_:
{
size_t v___x_1405_; size_t v___x_1406_; 
v___x_1405_ = ((size_t)1ULL);
v___x_1406_ = lean_usize_add(v_i_1400_, v___x_1405_);
v_i_1400_ = v___x_1406_;
v_b_1402_ = v___y_1404_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6___boxed(lean_object* v_as_1422_, lean_object* v_i_1423_, lean_object* v_stop_1424_, lean_object* v_b_1425_){
_start:
{
size_t v_i_boxed_1426_; size_t v_stop_boxed_1427_; lean_object* v_res_1428_; 
v_i_boxed_1426_ = lean_unbox_usize(v_i_1423_);
lean_dec(v_i_1423_);
v_stop_boxed_1427_ = lean_unbox_usize(v_stop_1424_);
lean_dec(v_stop_1424_);
v_res_1428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1422_, v_i_boxed_1426_, v_stop_boxed_1427_, v_b_1425_);
lean_dec_ref(v_as_1422_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(lean_object* v_as_1431_, lean_object* v_start_1432_, lean_object* v_stop_1433_){
_start:
{
lean_object* v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0));
v___x_1435_ = lean_nat_dec_lt(v_start_1432_, v_stop_1433_);
if (v___x_1435_ == 0)
{
return v___x_1434_;
}
else
{
lean_object* v___x_1436_; uint8_t v___x_1437_; 
v___x_1436_ = lean_array_get_size(v_as_1431_);
v___x_1437_ = lean_nat_dec_le(v_stop_1433_, v___x_1436_);
if (v___x_1437_ == 0)
{
uint8_t v___x_1438_; 
v___x_1438_ = lean_nat_dec_lt(v_start_1432_, v___x_1436_);
if (v___x_1438_ == 0)
{
return v___x_1434_;
}
else
{
size_t v___x_1439_; size_t v___x_1440_; lean_object* v___x_1441_; 
v___x_1439_ = lean_usize_of_nat(v_start_1432_);
v___x_1440_ = lean_usize_of_nat(v___x_1436_);
v___x_1441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1431_, v___x_1439_, v___x_1440_, v___x_1434_);
return v___x_1441_;
}
}
else
{
size_t v___x_1442_; size_t v___x_1443_; lean_object* v___x_1444_; 
v___x_1442_ = lean_usize_of_nat(v_start_1432_);
v___x_1443_ = lean_usize_of_nat(v_stop_1433_);
v___x_1444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1431_, v___x_1442_, v___x_1443_, v___x_1434_);
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___boxed(lean_object* v_as_1445_, lean_object* v_start_1446_, lean_object* v_stop_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(v_as_1445_, v_start_1446_, v_stop_1447_);
lean_dec(v_stop_1447_);
lean_dec(v_start_1446_);
lean_dec_ref(v_as_1445_);
return v_res_1448_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(lean_object* v_x_1449_, lean_object* v_x_1450_){
_start:
{
lean_object* v_fst_1451_; lean_object* v_snd_1452_; lean_object* v_fst_1453_; lean_object* v_snd_1454_; uint8_t v___x_1455_; 
v_fst_1451_ = lean_ctor_get(v_x_1449_, 0);
v_snd_1452_ = lean_ctor_get(v_x_1449_, 1);
v_fst_1453_ = lean_ctor_get(v_x_1450_, 0);
v_snd_1454_ = lean_ctor_get(v_x_1450_, 1);
v___x_1455_ = lean_nat_dec_eq(v_snd_1452_, v_snd_1454_);
if (v___x_1455_ == 0)
{
uint8_t v___x_1456_; 
v___x_1456_ = lean_nat_dec_lt(v_snd_1454_, v_snd_1452_);
return v___x_1456_;
}
else
{
uint8_t v___x_1457_; 
v___x_1457_ = l_Lean_Name_lt(v_fst_1451_, v_fst_1453_);
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0___boxed(lean_object* v_x_1458_, lean_object* v_x_1459_){
_start:
{
uint8_t v_res_1460_; lean_object* v_r_1461_; 
v_res_1460_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v_x_1458_, v_x_1459_);
lean_dec_ref(v_x_1459_);
lean_dec_ref(v_x_1458_);
v_r_1461_ = lean_box(v_res_1460_);
return v_r_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(lean_object* v_hi_1462_, lean_object* v_pivot_1463_, lean_object* v_as_1464_, lean_object* v_i_1465_, lean_object* v_k_1466_){
_start:
{
uint8_t v___y_1468_; uint8_t v___x_1477_; 
v___x_1477_ = lean_nat_dec_lt(v_k_1466_, v_hi_1462_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec(v_k_1466_);
v___x_1478_ = lean_array_fswap(v_as_1464_, v_i_1465_, v_hi_1462_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_i_1465_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
return v___x_1479_;
}
else
{
lean_object* v___x_1480_; lean_object* v_fst_1481_; lean_object* v_snd_1482_; lean_object* v_fst_1483_; lean_object* v_snd_1484_; uint8_t v___x_1485_; 
v___x_1480_ = lean_array_fget_borrowed(v_as_1464_, v_k_1466_);
v_fst_1481_ = lean_ctor_get(v___x_1480_, 0);
v_snd_1482_ = lean_ctor_get(v___x_1480_, 1);
v_fst_1483_ = lean_ctor_get(v_pivot_1463_, 0);
v_snd_1484_ = lean_ctor_get(v_pivot_1463_, 1);
v___x_1485_ = lean_nat_dec_eq(v_snd_1482_, v_snd_1484_);
if (v___x_1485_ == 0)
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_nat_dec_lt(v_snd_1484_, v_snd_1482_);
v___y_1468_ = v___x_1486_;
goto v___jp_1467_;
}
else
{
uint8_t v___x_1487_; 
v___x_1487_ = l_Lean_Name_lt(v_fst_1481_, v_fst_1483_);
v___y_1468_ = v___x_1487_;
goto v___jp_1467_;
}
}
v___jp_1467_:
{
if (v___y_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1469_ = lean_unsigned_to_nat(1u);
v___x_1470_ = lean_nat_add(v_k_1466_, v___x_1469_);
lean_dec(v_k_1466_);
v_k_1466_ = v___x_1470_;
goto _start;
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1472_ = lean_array_fswap(v_as_1464_, v_i_1465_, v_k_1466_);
v___x_1473_ = lean_unsigned_to_nat(1u);
v___x_1474_ = lean_nat_add(v_i_1465_, v___x_1473_);
lean_dec(v_i_1465_);
v___x_1475_ = lean_nat_add(v_k_1466_, v___x_1473_);
lean_dec(v_k_1466_);
v_as_1464_ = v___x_1472_;
v_i_1465_ = v___x_1474_;
v_k_1466_ = v___x_1475_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg___boxed(lean_object* v_hi_1488_, lean_object* v_pivot_1489_, lean_object* v_as_1490_, lean_object* v_i_1491_, lean_object* v_k_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_1488_, v_pivot_1489_, v_as_1490_, v_i_1491_, v_k_1492_);
lean_dec_ref(v_pivot_1489_);
lean_dec(v_hi_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(lean_object* v_n_1494_, lean_object* v_as_1495_, lean_object* v_lo_1496_, lean_object* v_hi_1497_){
_start:
{
lean_object* v___y_1499_; uint8_t v___x_1509_; 
v___x_1509_ = lean_nat_dec_lt(v_lo_1496_, v_hi_1497_);
if (v___x_1509_ == 0)
{
lean_dec(v_lo_1496_);
return v_as_1495_;
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v_mid_1512_; lean_object* v___y_1514_; lean_object* v___y_1520_; lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1510_ = lean_nat_add(v_lo_1496_, v_hi_1497_);
v___x_1511_ = lean_unsigned_to_nat(1u);
v_mid_1512_ = lean_nat_shiftr(v___x_1510_, v___x_1511_);
lean_dec(v___x_1510_);
v___x_1525_ = lean_array_fget_borrowed(v_as_1495_, v_mid_1512_);
v___x_1526_ = lean_array_fget_borrowed(v_as_1495_, v_lo_1496_);
v___x_1527_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
v___y_1520_ = v_as_1495_;
goto v___jp_1519_;
}
else
{
lean_object* v___x_1528_; 
v___x_1528_ = lean_array_fswap(v_as_1495_, v_lo_1496_, v_mid_1512_);
v___y_1520_ = v___x_1528_;
goto v___jp_1519_;
}
v___jp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v___x_1515_ = lean_array_fget_borrowed(v___y_1514_, v_mid_1512_);
v___x_1516_ = lean_array_fget_borrowed(v___y_1514_, v_hi_1497_);
v___x_1517_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1515_, v___x_1516_);
if (v___x_1517_ == 0)
{
lean_dec(v_mid_1512_);
v___y_1499_ = v___y_1514_;
goto v___jp_1498_;
}
else
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_array_fswap(v___y_1514_, v_mid_1512_, v_hi_1497_);
lean_dec(v_mid_1512_);
v___y_1499_ = v___x_1518_;
goto v___jp_1498_;
}
}
v___jp_1519_:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1521_ = lean_array_fget_borrowed(v___y_1520_, v_hi_1497_);
v___x_1522_ = lean_array_fget_borrowed(v___y_1520_, v_lo_1496_);
v___x_1523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
v___y_1514_ = v___y_1520_;
goto v___jp_1513_;
}
else
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_array_fswap(v___y_1520_, v_lo_1496_, v_hi_1497_);
v___y_1514_ = v___x_1524_;
goto v___jp_1513_;
}
}
}
v___jp_1498_:
{
lean_object* v_pivot_1500_; lean_object* v___x_1501_; lean_object* v_fst_1502_; lean_object* v_snd_1503_; uint8_t v___x_1504_; 
v_pivot_1500_ = lean_array_fget(v___y_1499_, v_hi_1497_);
lean_inc_n(v_lo_1496_, 2);
v___x_1501_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_1497_, v_pivot_1500_, v___y_1499_, v_lo_1496_, v_lo_1496_);
lean_dec(v_pivot_1500_);
v_fst_1502_ = lean_ctor_get(v___x_1501_, 0);
lean_inc(v_fst_1502_);
v_snd_1503_ = lean_ctor_get(v___x_1501_, 1);
lean_inc(v_snd_1503_);
lean_dec_ref(v___x_1501_);
v___x_1504_ = lean_nat_dec_le(v_hi_1497_, v_fst_1502_);
if (v___x_1504_ == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1505_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_1494_, v_snd_1503_, v_lo_1496_, v_fst_1502_);
v___x_1506_ = lean_unsigned_to_nat(1u);
v___x_1507_ = lean_nat_add(v_fst_1502_, v___x_1506_);
lean_dec(v_fst_1502_);
v_as_1495_ = v___x_1505_;
v_lo_1496_ = v___x_1507_;
goto _start;
}
else
{
lean_dec(v_fst_1502_);
lean_dec(v_lo_1496_);
return v_snd_1503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___boxed(lean_object* v_n_1529_, lean_object* v_as_1530_, lean_object* v_lo_1531_, lean_object* v_hi_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_1529_, v_as_1530_, v_lo_1531_, v_hi_1532_);
lean_dec(v_hi_1532_);
lean_dec(v_n_1529_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___lam__0(lean_object* v_ps_1534_, lean_object* v_k_1535_, lean_object* v_v_1536_){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_k_1535_);
lean_ctor_set(v___x_1537_, 1, v_v_1536_);
v___x_1538_ = lean_array_push(v_ps_1534_, v___x_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0(lean_object* v_f_1539_, lean_object* v_x1_1540_, lean_object* v_x2_1541_, lean_object* v_x3_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = lean_apply_3(v_f_1539_, v_x1_1540_, v_x2_1541_, v_x3_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(lean_object* v_f_1544_, lean_object* v_keys_1545_, lean_object* v_vals_1546_, lean_object* v_i_1547_, lean_object* v_acc_1548_){
_start:
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = lean_array_get_size(v_keys_1545_);
v___x_1550_ = lean_nat_dec_lt(v_i_1547_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_dec(v_i_1547_);
lean_dec(v_f_1544_);
return v_acc_1548_;
}
else
{
lean_object* v_k_1551_; lean_object* v_v_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_k_1551_ = lean_array_fget_borrowed(v_keys_1545_, v_i_1547_);
v_v_1552_ = lean_array_fget_borrowed(v_vals_1546_, v_i_1547_);
lean_inc(v_f_1544_);
lean_inc(v_v_1552_);
lean_inc(v_k_1551_);
v___x_1553_ = lean_apply_3(v_f_1544_, v_acc_1548_, v_k_1551_, v_v_1552_);
v___x_1554_ = lean_unsigned_to_nat(1u);
v___x_1555_ = lean_nat_add(v_i_1547_, v___x_1554_);
lean_dec(v_i_1547_);
v_i_1547_ = v___x_1555_;
v_acc_1548_ = v___x_1553_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_f_1557_, lean_object* v_keys_1558_, lean_object* v_vals_1559_, lean_object* v_i_1560_, lean_object* v_acc_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_1557_, v_keys_1558_, v_vals_1559_, v_i_1560_, v_acc_1561_);
lean_dec_ref(v_vals_1559_);
lean_dec_ref(v_keys_1558_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(lean_object* v_f_1563_, lean_object* v_as_1564_, size_t v_i_1565_, size_t v_stop_1566_, lean_object* v_b_1567_){
_start:
{
lean_object* v___y_1569_; uint8_t v___x_1573_; 
v___x_1573_ = lean_usize_dec_eq(v_i_1565_, v_stop_1566_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_array_uget_borrowed(v_as_1564_, v_i_1565_);
switch(lean_obj_tag(v___x_1574_))
{
case 0:
{
lean_object* v_key_1575_; lean_object* v_val_1576_; lean_object* v___x_1577_; 
v_key_1575_ = lean_ctor_get(v___x_1574_, 0);
v_val_1576_ = lean_ctor_get(v___x_1574_, 1);
lean_inc(v_f_1563_);
lean_inc(v_val_1576_);
lean_inc(v_key_1575_);
v___x_1577_ = lean_apply_3(v_f_1563_, v_b_1567_, v_key_1575_, v_val_1576_);
v___y_1569_ = v___x_1577_;
goto v___jp_1568_;
}
case 1:
{
lean_object* v_node_1578_; lean_object* v___x_1579_; 
v_node_1578_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_f_1563_);
v___x_1579_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_1563_, v_node_1578_, v_b_1567_);
v___y_1569_ = v___x_1579_;
goto v___jp_1568_;
}
default: 
{
v___y_1569_ = v_b_1567_;
goto v___jp_1568_;
}
}
}
else
{
lean_dec(v_f_1563_);
return v_b_1567_;
}
v___jp_1568_:
{
size_t v___x_1570_; size_t v___x_1571_; 
v___x_1570_ = ((size_t)1ULL);
v___x_1571_ = lean_usize_add(v_i_1565_, v___x_1570_);
v_i_1565_ = v___x_1571_;
v_b_1567_ = v___y_1569_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_f_1580_, lean_object* v_x_1581_, lean_object* v_x_1582_){
_start:
{
if (lean_obj_tag(v_x_1581_) == 0)
{
lean_object* v_es_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; uint8_t v___x_1586_; 
v_es_1583_ = lean_ctor_get(v_x_1581_, 0);
v___x_1584_ = lean_unsigned_to_nat(0u);
v___x_1585_ = lean_array_get_size(v_es_1583_);
v___x_1586_ = lean_nat_dec_lt(v___x_1584_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_dec(v_f_1580_);
return v_x_1582_;
}
else
{
size_t v___x_1587_; size_t v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = ((size_t)0ULL);
v___x_1588_ = lean_usize_of_nat(v___x_1585_);
v___x_1589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_1580_, v_es_1583_, v___x_1587_, v___x_1588_, v_x_1582_);
return v___x_1589_;
}
}
else
{
lean_object* v_ks_1590_; lean_object* v_vs_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_ks_1590_ = lean_ctor_get(v_x_1581_, 0);
v_vs_1591_ = lean_ctor_get(v_x_1581_, 1);
v___x_1592_ = lean_unsigned_to_nat(0u);
v___x_1593_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_1580_, v_ks_1590_, v_vs_1591_, v___x_1592_, v_x_1582_);
return v___x_1593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_f_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_1594_, v_x_1595_, v_x_1596_);
lean_dec_ref(v_x_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg___boxed(lean_object* v_f_1598_, lean_object* v_as_1599_, lean_object* v_i_1600_, lean_object* v_stop_1601_, lean_object* v_b_1602_){
_start:
{
size_t v_i_boxed_1603_; size_t v_stop_boxed_1604_; lean_object* v_res_1605_; 
v_i_boxed_1603_ = lean_unbox_usize(v_i_1600_);
lean_dec(v_i_1600_);
v_stop_boxed_1604_ = lean_unbox_usize(v_stop_1601_);
lean_dec(v_stop_1601_);
v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_1598_, v_as_1599_, v_i_boxed_1603_, v_stop_boxed_1604_, v_b_1602_);
lean_dec_ref(v_as_1599_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(lean_object* v_map_1606_, lean_object* v_f_1607_, lean_object* v_init_1608_){
_start:
{
lean_object* v___f_1609_; lean_object* v___x_1610_; 
v___f_1609_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1609_, 0, v_f_1607_);
v___x_1610_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v___f_1609_, v_map_1606_, v_init_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___boxed(lean_object* v_map_1611_, lean_object* v_f_1612_, lean_object* v_init_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_map_1611_, v_f_1612_, v_init_1613_);
lean_dec_ref(v_map_1611_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(lean_object* v_m_1618_){
_start:
{
lean_object* v___f_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___f_1619_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0));
v___x_1620_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1));
v___x_1621_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_m_1618_, v___f_1619_, v___x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___boxed(lean_object* v_m_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_m_1622_);
lean_dec_ref(v_m_1622_);
return v_res_1623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6));
v___x_1635_ = l_Lean_stringToMessageData(v___x_1634_);
return v___x_1635_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8));
v___x_1638_ = l_Lean_stringToMessageData(v___x_1637_);
return v___x_1638_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1640_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10));
v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
return v___x_1641_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1643_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12));
v___x_1644_ = l_Lean_stringToMessageData(v___x_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(lean_object* v_msg_1645_, lean_object* v_declHint_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v_env_1651_; uint8_t v___x_1652_; 
v___x_1649_ = lean_box(0);
v___x_1650_ = lean_st_ref_get(v___y_1647_);
v_env_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc_ref(v_env_1651_);
lean_dec(v___x_1650_);
v___x_1652_ = l_Lean_Name_isAnonymous(v_declHint_1646_);
if (v___x_1652_ == 0)
{
uint8_t v_isExporting_1653_; 
v_isExporting_1653_ = lean_ctor_get_uint8(v_env_1651_, sizeof(void*)*13);
if (v_isExporting_1653_ == 0)
{
lean_object* v___x_1654_; 
lean_dec_ref(v_env_1651_);
lean_dec(v_declHint_1646_);
v___x_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1654_, 0, v_msg_1645_);
return v___x_1654_;
}
else
{
lean_object* v___x_1655_; uint8_t v___x_1656_; 
lean_inc_ref(v_env_1651_);
v___x_1655_ = l_Lean_Environment_setExporting(v_env_1651_, v___x_1652_);
lean_inc(v_declHint_1646_);
lean_inc_ref(v___x_1655_);
v___x_1656_ = l_Lean_Environment_contains(v___x_1655_, v_declHint_1646_, v_isExporting_1653_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
lean_dec_ref(v___x_1655_);
lean_dec_ref(v_env_1651_);
lean_dec(v_declHint_1646_);
v___x_1657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1657_, 0, v_msg_1645_);
return v___x_1657_;
}
else
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v_c_1663_; lean_object* v___x_1664_; 
v___x_1658_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2);
v___x_1659_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5);
v___x_1660_ = l_Lean_Options_empty;
lean_inc_ref(v___x_1655_);
v___x_1661_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1655_);
lean_ctor_set(v___x_1661_, 1, v___x_1658_);
lean_ctor_set(v___x_1661_, 2, v___x_1659_);
lean_ctor_set(v___x_1661_, 3, v___x_1660_);
lean_inc(v_declHint_1646_);
v___x_1662_ = l_Lean_MessageData_ofConstName(v_declHint_1646_, v___x_1652_);
v_c_1663_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1663_, 0, v___x_1661_);
lean_ctor_set(v_c_1663_, 1, v___x_1662_);
v___x_1664_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_1655_, v_declHint_1646_);
lean_dec_ref(v___x_1655_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
lean_dec_ref(v_env_1651_);
lean_dec(v_declHint_1646_);
v___x_1665_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v_c_1663_);
v___x_1667_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_1668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
v___x_1669_ = l_Lean_MessageData_note(v___x_1668_);
v___x_1670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1670_, 0, v_msg_1645_);
lean_ctor_set(v___x_1670_, 1, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
else
{
lean_object* v_val_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1706_; 
v_val_1672_ = lean_ctor_get(v___x_1664_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v___x_1664_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1674_ = v___x_1664_;
v_isShared_1675_ = v_isSharedCheck_1706_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_val_1672_);
lean_dec(v___x_1664_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1706_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v_moduleNames_1677_; lean_object* v_mod_1678_; uint8_t v___x_1679_; 
v___x_1676_ = l_Lean_Environment_header(v_env_1651_);
lean_dec_ref(v_env_1651_);
v_moduleNames_1677_ = lean_ctor_get(v___x_1676_, 4);
lean_inc_ref(v_moduleNames_1677_);
lean_dec_ref(v___x_1676_);
v_mod_1678_ = lean_array_get(v___x_1649_, v_moduleNames_1677_, v_val_1672_);
lean_dec(v_val_1672_);
lean_dec_ref(v_moduleNames_1677_);
v___x_1679_ = l_Lean_isPrivateName(v_declHint_1646_);
lean_dec(v_declHint_1646_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1680_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5);
v___x_1681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
lean_ctor_set(v___x_1681_, 1, v_c_1663_);
v___x_1682_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_1683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1681_);
lean_ctor_set(v___x_1683_, 1, v___x_1682_);
v___x_1684_ = l_Lean_MessageData_ofName(v_mod_1678_);
v___x_1685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1685_, 0, v___x_1683_);
lean_ctor_set(v___x_1685_, 1, v___x_1684_);
v___x_1686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9);
v___x_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1685_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = l_Lean_MessageData_note(v___x_1687_);
v___x_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1689_, 0, v_msg_1645_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set_tag(v___x_1674_, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1689_);
v___x_1691_ = v___x_1674_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
return v___x_1691_;
}
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1704_; 
v___x_1693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v_c_1663_);
v___x_1695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = l_Lean_MessageData_ofName(v_mod_1678_);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1696_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
v___x_1699_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13);
v___x_1700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1700_, 0, v___x_1698_);
lean_ctor_set(v___x_1700_, 1, v___x_1699_);
v___x_1701_ = l_Lean_MessageData_note(v___x_1700_);
v___x_1702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1702_, 0, v_msg_1645_);
lean_ctor_set(v___x_1702_, 1, v___x_1701_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set_tag(v___x_1674_, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1702_);
v___x_1704_ = v___x_1674_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1702_);
v___x_1704_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
return v___x_1704_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1707_; 
lean_dec_ref(v_env_1651_);
lean_dec(v_declHint_1646_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_msg_1645_);
return v___x_1707_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___boxed(lean_object* v_msg_1708_, lean_object* v_declHint_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_1708_, v_declHint_1709_, v___y_1710_);
lean_dec(v___y_1710_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(lean_object* v_msg_1713_, lean_object* v_declHint_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1730_; 
v___x_1720_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_1713_, v_declHint_1714_, v___y_1718_);
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1723_ = v___x_1720_;
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1720_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1725_ = l_Lean_unknownIdentifierMessageTag;
v___x_1726_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v_a_1721_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1726_);
v___x_1728_ = v___x_1723_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16___boxed(lean_object* v_msg_1731_, lean_object* v_declHint_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(v_msg_1731_, v_declHint_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
lean_dec(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(lean_object* v_msg_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v_ref_1745_; lean_object* v___x_1746_; lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1755_; 
v_ref_1745_ = lean_ctor_get(v___y_1742_, 2);
v___x_1746_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(v_msg_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1749_ = v___x_1746_;
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1746_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
lean_inc(v_ref_1745_);
v___x_1751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1751_, 0, v_ref_1745_);
lean_ctor_set(v___x_1751_, 1, v_a_1747_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set_tag(v___x_1749_, 1);
lean_ctor_set(v___x_1749_, 0, v___x_1751_);
v___x_1753_ = v___x_1749_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_msg_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(lean_object* v_ref_1763_, lean_object* v_msg_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v_toCold_1770_; lean_object* v_currRecDepth_1771_; lean_object* v_ref_1772_; uint16_t v_optionFlags_1773_; uint8_t v_suppressElabErrors_1774_; uint8_t v_checkDeprecated_1775_; uint8_t v_isRecordingDeps_1776_; lean_object* v_ref_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v_toCold_1770_ = lean_ctor_get(v___y_1767_, 0);
v_currRecDepth_1771_ = lean_ctor_get(v___y_1767_, 1);
v_ref_1772_ = lean_ctor_get(v___y_1767_, 2);
v_optionFlags_1773_ = lean_ctor_get_uint16(v___y_1767_, sizeof(void*)*3);
v_suppressElabErrors_1774_ = lean_ctor_get_uint8(v___y_1767_, sizeof(void*)*3 + 2);
v_checkDeprecated_1775_ = lean_ctor_get_uint8(v___y_1767_, sizeof(void*)*3 + 3);
v_isRecordingDeps_1776_ = lean_ctor_get_uint8(v___y_1767_, sizeof(void*)*3 + 4);
v_ref_1777_ = l_Lean_replaceRef(v_ref_1763_, v_ref_1772_);
lean_inc(v_currRecDepth_1771_);
lean_inc_ref(v_toCold_1770_);
v___x_1778_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_1778_, 0, v_toCold_1770_);
lean_ctor_set(v___x_1778_, 1, v_currRecDepth_1771_);
lean_ctor_set(v___x_1778_, 2, v_ref_1777_);
lean_ctor_set_uint16(v___x_1778_, sizeof(void*)*3, v_optionFlags_1773_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*3 + 2, v_suppressElabErrors_1774_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*3 + 3, v_checkDeprecated_1775_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*3 + 4, v_isRecordingDeps_1776_);
v___x_1779_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_1764_, v___y_1765_, v___y_1766_, v___x_1778_, v___y_1768_);
lean_dec_ref_known(v___x_1778_, 3);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg___boxed(lean_object* v_ref_1780_, lean_object* v_msg_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_1780_, v_msg_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v_ref_1780_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(lean_object* v_ref_1788_, lean_object* v_msg_1789_, lean_object* v_declHint_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; lean_object* v_a_1797_; lean_object* v___x_1798_; 
v___x_1796_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(v_msg_1789_, v_declHint_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref(v___x_1796_);
v___x_1798_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_1788_, v_a_1797_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg___boxed(lean_object* v_ref_1799_, lean_object* v_msg_1800_, lean_object* v_declHint_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v_res_1807_; 
v_res_1807_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_1799_, v_msg_1800_, v_declHint_1801_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
lean_dec(v___y_1805_);
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
lean_dec_ref(v___y_1802_);
lean_dec(v_ref_1799_);
return v_res_1807_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0));
v___x_1810_ = l_Lean_stringToMessageData(v___x_1809_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(lean_object* v_ref_1811_, lean_object* v_constName_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_){
_start:
{
lean_object* v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1818_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1);
v___x_1819_ = 0;
lean_inc(v_constName_1812_);
v___x_1820_ = l_Lean_MessageData_ofConstName(v_constName_1812_, v___x_1819_);
v___x_1821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1818_);
lean_ctor_set(v___x_1821_, 1, v___x_1820_);
v___x_1822_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
v___x_1823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1821_);
lean_ctor_set(v___x_1823_, 1, v___x_1822_);
v___x_1824_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_1811_, v___x_1823_, v_constName_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_ref_1825_, lean_object* v_constName_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_1825_, v_constName_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec(v___y_1828_);
lean_dec_ref(v___y_1827_);
lean_dec(v_ref_1825_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(lean_object* v_constName_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_ref_1839_; lean_object* v___x_1840_; 
v_ref_1839_ = lean_ctor_get(v___y_1836_, 2);
v___x_1840_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_1839_, v_constName_1833_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_constName_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(lean_object* v_constName_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___x_1854_; lean_object* v_env_1855_; uint8_t v___x_1856_; lean_object* v___x_1857_; 
v___x_1854_ = lean_st_ref_get(v___y_1852_);
v_env_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc_ref(v_env_1855_);
lean_dec(v___x_1854_);
v___x_1856_ = 0;
lean_inc(v_constName_1848_);
v___x_1857_ = l_Lean_Environment_findConstVal_x3f(v_env_1855_, v_constName_1848_, v___x_1856_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
return v___x_1858_;
}
else
{
lean_object* v_val_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1866_; 
lean_dec(v_constName_1848_);
v_val_1859_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1866_ == 0)
{
v___x_1861_ = v___x_1857_;
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_val_1859_);
lean_dec(v___x_1857_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1866_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set_tag(v___x_1861_, 0);
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_val_1859_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2___boxed(lean_object* v_constName_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(v_constName_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec_ref(v___y_1868_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(lean_object* v_a_1874_, lean_object* v_a_1875_){
_start:
{
if (lean_obj_tag(v_a_1874_) == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = l_List_reverse___redArg(v_a_1875_);
return v___x_1876_;
}
else
{
lean_object* v_head_1877_; lean_object* v_tail_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1887_; 
v_head_1877_ = lean_ctor_get(v_a_1874_, 0);
v_tail_1878_ = lean_ctor_get(v_a_1874_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_a_1874_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1880_ = v_a_1874_;
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_tail_1878_);
lean_inc(v_head_1877_);
lean_dec(v_a_1874_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1887_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; lean_object* v___x_1884_; 
v___x_1882_ = l_Lean_mkLevelParam(v_head_1877_);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 1, v_a_1875_);
lean_ctor_set(v___x_1880_, 0, v___x_1882_);
v___x_1884_ = v___x_1880_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_a_1875_);
v___x_1884_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
v_a_1874_ = v_tail_1878_;
v_a_1875_ = v___x_1884_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(lean_object* v_constName_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v___x_1894_; 
lean_inc(v_constName_1888_);
v___x_1894_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(v_constName_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1906_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1906_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1906_ == 0)
{
v___x_1897_ = v___x_1894_;
v_isShared_1898_ = v_isSharedCheck_1906_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1894_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1906_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_levelParams_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
v_levelParams_1899_ = lean_ctor_get(v_a_1895_, 1);
lean_inc(v_levelParams_1899_);
lean_dec(v_a_1895_);
v___x_1900_ = lean_box(0);
v___x_1901_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(v_levelParams_1899_, v___x_1900_);
v___x_1902_ = l_Lean_mkConst(v_constName_1888_, v___x_1901_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 0, v___x_1902_);
v___x_1904_ = v___x_1897_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
}
else
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1914_; 
lean_dec(v_constName_1888_);
v_a_1907_ = lean_ctor_get(v___x_1894_, 0);
v_isSharedCheck_1914_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1914_ == 0)
{
v___x_1909_ = v___x_1894_;
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1894_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1914_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1912_; 
if (v_isShared_1910_ == 0)
{
v___x_1912_ = v___x_1909_;
goto v_reusejp_1911_;
}
else
{
lean_object* v_reuseFailAlloc_1913_; 
v_reuseFailAlloc_1913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_a_1907_);
v___x_1912_ = v_reuseFailAlloc_1913_;
goto v_reusejp_1911_;
}
v_reusejp_1911_:
{
return v___x_1912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1___boxed(lean_object* v_constName_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(v_constName_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
lean_dec(v___y_1919_);
lean_dec_ref(v___y_1918_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
return v_res_1921_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1925_; double v___x_1926_; 
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = lean_float_of_nat(v___x_1925_);
return v___x_1926_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4));
v___x_1930_ = l_Lean_stringToMessageData(v___x_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(size_t v_sz_1933_, size_t v_i_1934_, lean_object* v_bs_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
uint8_t v___x_1941_; 
v___x_1941_ = lean_usize_dec_lt(v_i_1934_, v_sz_1933_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1942_, 0, v_bs_1935_);
return v___x_1942_;
}
else
{
lean_object* v_v_1943_; lean_object* v_fst_1944_; lean_object* v_snd_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1981_; 
v_v_1943_ = lean_array_uget(v_bs_1935_, v_i_1934_);
v_fst_1944_ = lean_ctor_get(v_v_1943_, 0);
v_snd_1945_ = lean_ctor_get(v_v_1943_, 1);
v_isSharedCheck_1981_ = !lean_is_exclusive(v_v_1943_);
if (v_isSharedCheck_1981_ == 0)
{
v___x_1947_ = v_v_1943_;
v_isShared_1948_ = v_isSharedCheck_1981_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_snd_1945_);
lean_inc(v_fst_1944_);
lean_dec(v_v_1943_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1981_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v_bs_x27_1950_; lean_object* v___x_1951_; 
v___x_1949_ = lean_unsigned_to_nat(0u);
v_bs_x27_1950_ = lean_array_uset(v_bs_1935_, v_i_1934_, v___x_1949_);
v___x_1951_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(v_fst_1944_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; double v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1));
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2);
v___x_1956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
v___x_1957_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1957_, 0, v___x_1953_);
lean_ctor_set(v___x_1957_, 1, v___x_1954_);
lean_ctor_set(v___x_1957_, 2, v___x_1956_);
lean_ctor_set_float(v___x_1957_, sizeof(void*)*3, v___x_1955_);
lean_ctor_set_float(v___x_1957_, sizeof(void*)*3 + 8, v___x_1955_);
lean_ctor_set_uint8(v___x_1957_, sizeof(void*)*3 + 16, v___x_1941_);
v___x_1958_ = l_Lean_MessageData_ofConst(v_a_1952_);
v___x_1959_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5);
if (v_isShared_1948_ == 0)
{
lean_ctor_set_tag(v___x_1947_, 7);
lean_ctor_set(v___x_1947_, 1, v___x_1959_);
lean_ctor_set(v___x_1947_, 0, v___x_1958_);
v___x_1961_ = v___x_1947_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1958_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1962_ = l_Nat_reprFast(v_snd_1945_);
v___x_1963_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
v___x_1964_ = l_Lean_MessageData_ofFormat(v___x_1963_);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1961_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6));
v___x_1967_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1957_);
lean_ctor_set(v___x_1967_, 1, v___x_1965_);
lean_ctor_set(v___x_1967_, 2, v___x_1966_);
v___x_1968_ = ((size_t)1ULL);
v___x_1969_ = lean_usize_add(v_i_1934_, v___x_1968_);
v___x_1970_ = lean_array_uset(v_bs_x27_1950_, v_i_1934_, v___x_1967_);
v_i_1934_ = v___x_1969_;
v_bs_1935_ = v___x_1970_;
goto _start;
}
}
else
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1980_; 
lean_dec_ref(v_bs_x27_1950_);
lean_del_object(v___x_1947_);
lean_dec(v_snd_1945_);
v_a_1973_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1980_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1980_ == 0)
{
v___x_1975_ = v___x_1951_;
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1951_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1980_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1978_; 
if (v_isShared_1976_ == 0)
{
v___x_1978_ = v___x_1975_;
goto v_reusejp_1977_;
}
else
{
lean_object* v_reuseFailAlloc_1979_; 
v_reuseFailAlloc_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1979_, 0, v_a_1973_);
v___x_1978_ = v_reuseFailAlloc_1979_;
goto v_reusejp_1977_;
}
v_reusejp_1977_:
{
return v___x_1978_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___boxed(lean_object* v_sz_1982_, lean_object* v_i_1983_, lean_object* v_bs_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
size_t v_sz_boxed_1990_; size_t v_i_boxed_1991_; lean_object* v_res_1992_; 
v_sz_boxed_1990_ = lean_unbox_usize(v_sz_1982_);
lean_dec(v_sz_1982_);
v_i_boxed_1991_ = lean_unbox_usize(v_i_1983_);
lean_dec(v_i_1983_);
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(v_sz_boxed_1990_, v_i_boxed_1991_, v_bs_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_);
lean_dec(v___y_1988_);
lean_dec_ref(v___y_1987_);
lean_dec(v___y_1986_);
lean_dec_ref(v___y_1985_);
return v_res_1992_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0(void){
_start:
{
lean_object* v___x_1993_; uint8_t v___x_1994_; double v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
v___x_1994_ = 1;
v___x_1995_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2);
v___x_1996_ = lean_box(0);
v___x_1997_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1));
v___x_1998_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
lean_ctor_set(v___x_1998_, 1, v___x_1996_);
lean_ctor_set(v___x_1998_, 2, v___x_1993_);
lean_ctor_set_float(v___x_1998_, sizeof(void*)*3, v___x_1995_);
lean_ctor_set_float(v___x_1998_, sizeof(void*)*3 + 8, v___x_1995_);
lean_ctor_set_uint8(v___x_1998_, sizeof(void*)*3 + 16, v___x_1994_);
return v___x_1998_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3(void){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2));
v___x_2003_ = l_Lean_MessageData_ofFormat(v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(lean_object* v_thms_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___y_2013_; lean_object* v___x_2036_; lean_object* v_data_2037_; lean_object* v___x_2038_; lean_object* v___y_2040_; lean_object* v___y_2041_; uint8_t v___x_2043_; 
v___x_2010_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_thms_2004_);
v___x_2011_ = lean_unsigned_to_nat(0u);
v___x_2036_ = lean_array_get_size(v___x_2010_);
v_data_2037_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(v___x_2010_, v___x_2011_, v___x_2036_);
lean_dec_ref(v___x_2010_);
v___x_2038_ = lean_array_get_size(v_data_2037_);
v___x_2043_ = lean_nat_dec_eq(v___x_2038_, v___x_2011_);
if (v___x_2043_ == 0)
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___y_2047_; uint8_t v___x_2049_; 
v___x_2044_ = lean_unsigned_to_nat(1u);
v___x_2045_ = lean_nat_sub(v___x_2038_, v___x_2044_);
v___x_2049_ = lean_nat_dec_le(v___x_2011_, v___x_2045_);
if (v___x_2049_ == 0)
{
lean_inc(v___x_2045_);
v___y_2047_ = v___x_2045_;
goto v___jp_2046_;
}
else
{
v___y_2047_ = v___x_2011_;
goto v___jp_2046_;
}
v___jp_2046_:
{
uint8_t v___x_2048_; 
v___x_2048_ = lean_nat_dec_le(v___y_2047_, v___x_2045_);
if (v___x_2048_ == 0)
{
lean_dec(v___x_2045_);
lean_inc(v___y_2047_);
v___y_2040_ = v___y_2047_;
v___y_2041_ = v___y_2047_;
goto v___jp_2039_;
}
else
{
v___y_2040_ = v___y_2047_;
v___y_2041_ = v___x_2045_;
goto v___jp_2039_;
}
}
}
else
{
v___y_2013_ = v_data_2037_;
goto v___jp_2012_;
}
v___jp_2012_:
{
size_t v_sz_2014_; size_t v___x_2015_; lean_object* v___x_2016_; 
v_sz_2014_ = lean_array_size(v___y_2013_);
v___x_2015_ = ((size_t)0ULL);
v___x_2016_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(v_sz_2014_, v___x_2015_, v___y_2013_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2027_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2019_ = v___x_2016_;
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_dec(v___x_2016_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2027_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2021_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0);
v___x_2022_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3);
v___x_2023_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
lean_ctor_set(v___x_2023_, 2, v_a_2017_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2023_);
v___x_2025_ = v___x_2019_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v_a_2028_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2016_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2016_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
v___jp_2039_:
{
lean_object* v___x_2042_; 
v___x_2042_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v___x_2038_, v_data_2037_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
v___y_2013_ = v___x_2042_;
goto v___jp_2012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___boxed(lean_object* v_thms_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(v_thms_2050_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
lean_dec(v_a_2054_);
lean_dec_ref(v_a_2053_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
lean_dec_ref(v_thms_2050_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(lean_object* v_00_u03b2_2057_, lean_object* v_m_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_m_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___boxed(lean_object* v_00_u03b2_2060_, lean_object* v_m_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(v_00_u03b2_2060_, v_m_2061_);
lean_dec_ref(v_m_2061_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(lean_object* v_n_2063_, lean_object* v_as_2064_, lean_object* v_lo_2065_, lean_object* v_hi_2066_, lean_object* v_w_2067_, lean_object* v_hlo_2068_, lean_object* v_hhi_2069_){
_start:
{
lean_object* v___x_2070_; 
v___x_2070_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_2063_, v_as_2064_, v_lo_2065_, v_hi_2066_);
return v___x_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___boxed(lean_object* v_n_2071_, lean_object* v_as_2072_, lean_object* v_lo_2073_, lean_object* v_hi_2074_, lean_object* v_w_2075_, lean_object* v_hlo_2076_, lean_object* v_hhi_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(v_n_2071_, v_as_2072_, v_lo_2073_, v_hi_2074_, v_w_2075_, v_hlo_2076_, v_hhi_2077_);
lean_dec(v_hi_2074_);
lean_dec(v_n_2071_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(lean_object* v_00_u03c3_2079_, lean_object* v_00_u03b2_2080_, lean_object* v_map_2081_, lean_object* v_f_2082_, lean_object* v_init_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_map_2081_, v_f_2082_, v_init_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2085_, lean_object* v_00_u03b2_2086_, lean_object* v_map_2087_, lean_object* v_f_2088_, lean_object* v_init_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(v_00_u03c3_2085_, v_00_u03b2_2086_, v_map_2087_, v_f_2088_, v_init_2089_);
lean_dec_ref(v_map_2087_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(lean_object* v_n_2091_, lean_object* v_lo_2092_, lean_object* v_hi_2093_, lean_object* v_hhi_2094_, lean_object* v_pivot_2095_, lean_object* v_as_2096_, lean_object* v_i_2097_, lean_object* v_k_2098_, lean_object* v_ilo_2099_, lean_object* v_ik_2100_, lean_object* v_w_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_2093_, v_pivot_2095_, v_as_2096_, v_i_2097_, v_k_2098_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___boxed(lean_object* v_n_2103_, lean_object* v_lo_2104_, lean_object* v_hi_2105_, lean_object* v_hhi_2106_, lean_object* v_pivot_2107_, lean_object* v_as_2108_, lean_object* v_i_2109_, lean_object* v_k_2110_, lean_object* v_ilo_2111_, lean_object* v_ik_2112_, lean_object* v_w_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(v_n_2103_, v_lo_2104_, v_hi_2105_, v_hhi_2106_, v_pivot_2107_, v_as_2108_, v_i_2109_, v_k_2110_, v_ilo_2111_, v_ik_2112_, v_w_2113_);
lean_dec_ref(v_pivot_2107_);
lean_dec(v_hi_2105_);
lean_dec(v_lo_2104_);
lean_dec(v_n_2103_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(lean_object* v_map_2115_, lean_object* v_f_2116_, lean_object* v_init_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2116_, v_map_2115_, v_init_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_2119_, lean_object* v_f_2120_, lean_object* v_init_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(v_map_2119_, v_f_2120_, v_init_2121_);
lean_dec_ref(v_map_2119_);
return v_res_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2123_, lean_object* v_00_u03b2_2124_, lean_object* v_map_2125_, lean_object* v_f_2126_, lean_object* v_init_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2126_, v_map_2125_, v_init_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_2129_, lean_object* v_00_u03b2_2130_, lean_object* v_map_2131_, lean_object* v_f_2132_, lean_object* v_init_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(v_00_u03c3_2129_, v_00_u03b2_2130_, v_map_2131_, v_f_2132_, v_init_2133_);
lean_dec_ref(v_map_2131_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2135_, lean_object* v_constName_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2143_, lean_object* v_constName_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(v_00_u03b1_2143_, v_constName_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03c3_2151_, lean_object* v_00_u03b1_2152_, lean_object* v_00_u03b2_2153_, lean_object* v_f_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2154_, v_x_2155_, v_x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03c3_2158_, lean_object* v_00_u03b1_2159_, lean_object* v_00_u03b2_2160_, lean_object* v_f_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_){
_start:
{
lean_object* v_res_2164_; 
v_res_2164_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(v_00_u03c3_2158_, v_00_u03b1_2159_, v_00_u03b2_2160_, v_f_2161_, v_x_2162_, v_x_2163_);
lean_dec_ref(v_x_2162_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(lean_object* v_00_u03b1_2165_, lean_object* v_ref_2166_, lean_object* v_constName_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v___x_2173_; 
v___x_2173_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_2166_, v_constName_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b1_2174_, lean_object* v_ref_2175_, lean_object* v_constName_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(v_00_u03b1_2174_, v_ref_2175_, v_constName_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v_ref_2175_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(lean_object* v_00_u03b1_2183_, lean_object* v_00_u03b2_2184_, lean_object* v_00_u03c3_2185_, lean_object* v_f_2186_, lean_object* v_as_2187_, size_t v_i_2188_, size_t v_stop_2189_, lean_object* v_b_2190_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_2186_, v_as_2187_, v_i_2188_, v_stop_2189_, v_b_2190_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___boxed(lean_object* v_00_u03b1_2192_, lean_object* v_00_u03b2_2193_, lean_object* v_00_u03c3_2194_, lean_object* v_f_2195_, lean_object* v_as_2196_, lean_object* v_i_2197_, lean_object* v_stop_2198_, lean_object* v_b_2199_){
_start:
{
size_t v_i_boxed_2200_; size_t v_stop_boxed_2201_; lean_object* v_res_2202_; 
v_i_boxed_2200_ = lean_unbox_usize(v_i_2197_);
lean_dec(v_i_2197_);
v_stop_boxed_2201_ = lean_unbox_usize(v_stop_2198_);
lean_dec(v_stop_2198_);
v_res_2202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(v_00_u03b1_2192_, v_00_u03b2_2193_, v_00_u03c3_2194_, v_f_2195_, v_as_2196_, v_i_boxed_2200_, v_stop_boxed_2201_, v_b_2199_);
lean_dec_ref(v_as_2196_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(lean_object* v_00_u03c3_2203_, lean_object* v_00_u03b1_2204_, lean_object* v_00_u03b2_2205_, lean_object* v_f_2206_, lean_object* v_keys_2207_, lean_object* v_vals_2208_, lean_object* v_heq_2209_, lean_object* v_i_2210_, lean_object* v_acc_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_2206_, v_keys_2207_, v_vals_2208_, v_i_2210_, v_acc_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03c3_2213_, lean_object* v_00_u03b1_2214_, lean_object* v_00_u03b2_2215_, lean_object* v_f_2216_, lean_object* v_keys_2217_, lean_object* v_vals_2218_, lean_object* v_heq_2219_, lean_object* v_i_2220_, lean_object* v_acc_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(v_00_u03c3_2213_, v_00_u03b1_2214_, v_00_u03b2_2215_, v_f_2216_, v_keys_2217_, v_vals_2218_, v_heq_2219_, v_i_2220_, v_acc_2221_);
lean_dec_ref(v_vals_2218_);
lean_dec_ref(v_keys_2217_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(lean_object* v_00_u03b1_2223_, lean_object* v_ref_2224_, lean_object* v_msg_2225_, lean_object* v_declHint_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
v___x_2232_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_2224_, v_msg_2225_, v_declHint_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___boxed(lean_object* v_00_u03b1_2233_, lean_object* v_ref_2234_, lean_object* v_msg_2235_, lean_object* v_declHint_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(v_00_u03b1_2233_, v_ref_2234_, v_msg_2235_, v_declHint_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v_ref_2234_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(lean_object* v_msg_2243_, lean_object* v_declHint_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_2243_, v_declHint_2244_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___boxed(lean_object* v_msg_2251_, lean_object* v_declHint_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(v_msg_2251_, v_declHint_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(lean_object* v_00_u03b1_2259_, lean_object* v_ref_2260_, lean_object* v_msg_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_2260_, v_msg_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___boxed(lean_object* v_00_u03b1_2268_, lean_object* v_ref_2269_, lean_object* v_msg_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(v_00_u03b1_2268_, v_ref_2269_, v_msg_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v_ref_2269_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_2277_, lean_object* v_msg_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v___x_2284_; 
v___x_2284_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_2285_, lean_object* v_msg_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(v_00_u03b1_2285_, v_msg_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(lean_object* v_k_2293_, lean_object* v_b_2294_, lean_object* v_c_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; 
lean_inc(v___y_2299_);
lean_inc_ref(v___y_2298_);
lean_inc(v___y_2297_);
lean_inc_ref(v___y_2296_);
v___x_2301_ = lean_apply_7(v_k_2293_, v_b_2294_, v_c_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, lean_box(0));
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed(lean_object* v_k_2302_, lean_object* v_b_2303_, lean_object* v_c_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(v_k_2302_, v_b_2303_, v_c_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(lean_object* v_type_2311_, lean_object* v_k_2312_, uint8_t v_cleanupAnnotations_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___f_2319_; uint8_t v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___f_2319_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2319_, 0, v_k_2312_);
v___x_2320_ = 0;
v___x_2321_ = lean_box(0);
v___x_2322_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2320_, v___x_2321_, v_type_2311_, v___f_2319_, v_cleanupAnnotations_2313_, v___x_2320_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2322_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2322_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
v_a_2331_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2322_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2322_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___boxed(lean_object* v_type_2339_, lean_object* v_k_2340_, lean_object* v_cleanupAnnotations_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2347_; lean_object* v_res_2348_; 
v_cleanupAnnotations_boxed_2347_ = lean_unbox(v_cleanupAnnotations_2341_);
v_res_2348_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v_type_2339_, v_k_2340_, v_cleanupAnnotations_boxed_2347_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(lean_object* v_00_u03b1_2349_, lean_object* v_type_2350_, lean_object* v_k_2351_, uint8_t v_cleanupAnnotations_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v_type_2350_, v_k_2351_, v_cleanupAnnotations_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___boxed(lean_object* v_00_u03b1_2359_, lean_object* v_type_2360_, lean_object* v_k_2361_, lean_object* v_cleanupAnnotations_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2368_; lean_object* v_res_2369_; 
v_cleanupAnnotations_boxed_2368_ = lean_unbox(v_cleanupAnnotations_2362_);
v_res_2369_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(v_00_u03b1_2359_, v_type_2360_, v_k_2361_, v_cleanupAnnotations_boxed_2368_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
return v_res_2369_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = lean_box(0);
v___x_2374_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1));
v___x_2375_ = l_Lean_mkConst(v___x_2374_, v___x_2373_);
return v___x_2375_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2);
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(lean_object* v_x_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2384_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3);
v___x_2385_ = 0;
v___x_2386_ = lean_box(0);
v___x_2387_ = l_Lean_Meta_mkFreshExprMVar(v___x_2384_, v___x_2385_, v___x_2386_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2387_) == 0)
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2396_; 
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2396_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2394_; 
v___x_2392_ = l_Lean_Expr_mvarId_x21(v_a_2388_);
lean_dec(v_a_2388_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2392_);
v___x_2394_ = v___x_2390_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
v_a_2397_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2387_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2387_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___boxed(lean_object* v_x_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(v_x_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec_ref(v_x_2405_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2412_, lean_object* v_b_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___x_2419_; 
lean_inc(v___y_2417_);
lean_inc_ref(v___y_2416_);
lean_inc(v___y_2415_);
lean_inc_ref(v___y_2414_);
v___x_2419_ = lean_apply_6(v_k_2412_, v_b_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, lean_box(0));
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2420_, lean_object* v_b_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(v_k_2420_, v_b_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_name_2428_, uint8_t v_bi_2429_, lean_object* v_type_2430_, lean_object* v_k_2431_, uint8_t v_kind_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
lean_object* v___f_2438_; lean_object* v___x_2439_; 
v___f_2438_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2438_, 0, v_k_2431_);
v___x_2439_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2428_, v_bi_2429_, v_type_2430_, v___f_2438_, v_kind_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2439_) == 0)
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2439_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2439_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
v_a_2448_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2439_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2439_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_name_2456_, lean_object* v_bi_2457_, lean_object* v_type_2458_, lean_object* v_k_2459_, lean_object* v_kind_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
uint8_t v_bi_boxed_2466_; uint8_t v_kind_boxed_2467_; lean_object* v_res_2468_; 
v_bi_boxed_2466_ = lean_unbox(v_bi_2457_);
v_kind_boxed_2467_ = lean_unbox(v_kind_2460_);
v_res_2468_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2456_, v_bi_boxed_2466_, v_type_2458_, v_k_2459_, v_kind_boxed_2467_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(lean_object* v_name_2469_, lean_object* v_type_2470_, lean_object* v_k_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
uint8_t v___x_2477_; uint8_t v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = 0;
v___x_2478_ = 0;
v___x_2479_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2469_, v___x_2477_, v_type_2470_, v_k_2471_, v___x_2478_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg___boxed(lean_object* v_name_2480_, lean_object* v_type_2481_, lean_object* v_k_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v_name_2480_, v_type_2481_, v_k_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(lean_object* v___f_2492_, lean_object* v_x_2493_, lean_object* v_type_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1));
v___x_2501_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v___x_2500_, v_type_2494_, v___f_2492_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___boxed(lean_object* v___f_2502_, lean_object* v_x_2503_, lean_object* v_type_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(v___f_2502_, v_x_2503_, v_type_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec_ref(v_x_2503_);
return v_res_2510_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(uint8_t v_suppressElabErrors_2517_, lean_object* v_x_2518_){
_start:
{
if (lean_obj_tag(v_x_2518_) == 1)
{
lean_object* v_pre_2519_; 
v_pre_2519_ = lean_ctor_get(v_x_2518_, 0);
switch(lean_obj_tag(v_pre_2519_))
{
case 1:
{
lean_object* v_pre_2520_; 
v_pre_2520_ = lean_ctor_get(v_pre_2519_, 0);
switch(lean_obj_tag(v_pre_2520_))
{
case 0:
{
lean_object* v_str_2521_; lean_object* v_str_2522_; lean_object* v___x_2523_; uint8_t v___x_2524_; 
v_str_2521_ = lean_ctor_get(v_x_2518_, 1);
v_str_2522_ = lean_ctor_get(v_pre_2519_, 1);
v___x_2523_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_2524_ = lean_string_dec_eq(v_str_2522_, v___x_2523_);
if (v___x_2524_ == 0)
{
lean_object* v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_2526_ = lean_string_dec_eq(v_str_2522_, v___x_2525_);
if (v___x_2526_ == 0)
{
return v___x_2526_;
}
else
{
lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0));
v___x_2528_ = lean_string_dec_eq(v_str_2521_, v___x_2527_);
if (v___x_2528_ == 0)
{
return v___x_2528_;
}
else
{
return v_suppressElabErrors_2517_;
}
}
}
else
{
lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2529_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1));
v___x_2530_ = lean_string_dec_eq(v_str_2521_, v___x_2529_);
if (v___x_2530_ == 0)
{
return v___x_2530_;
}
else
{
return v_suppressElabErrors_2517_;
}
}
}
case 1:
{
lean_object* v_pre_2531_; 
v_pre_2531_ = lean_ctor_get(v_pre_2520_, 0);
if (lean_obj_tag(v_pre_2531_) == 0)
{
lean_object* v_str_2532_; lean_object* v_str_2533_; lean_object* v_str_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v_str_2532_ = lean_ctor_get(v_x_2518_, 1);
v_str_2533_ = lean_ctor_get(v_pre_2519_, 1);
v_str_2534_ = lean_ctor_get(v_pre_2520_, 1);
v___x_2535_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2));
v___x_2536_ = lean_string_dec_eq(v_str_2534_, v___x_2535_);
if (v___x_2536_ == 0)
{
return v___x_2536_;
}
else
{
lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2537_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3));
v___x_2538_ = lean_string_dec_eq(v_str_2533_, v___x_2537_);
if (v___x_2538_ == 0)
{
return v___x_2538_;
}
else
{
lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2539_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4));
v___x_2540_ = lean_string_dec_eq(v_str_2532_, v___x_2539_);
if (v___x_2540_ == 0)
{
return v___x_2540_;
}
else
{
return v_suppressElabErrors_2517_;
}
}
}
}
else
{
uint8_t v___x_2541_; 
v___x_2541_ = 0;
return v___x_2541_;
}
}
default: 
{
uint8_t v___x_2542_; 
v___x_2542_ = 0;
return v___x_2542_;
}
}
}
case 0:
{
lean_object* v_str_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; 
v_str_2543_ = lean_ctor_get(v_x_2518_, 1);
v___x_2544_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5));
v___x_2545_ = lean_string_dec_eq(v_str_2543_, v___x_2544_);
if (v___x_2545_ == 0)
{
return v___x_2545_;
}
else
{
return v_suppressElabErrors_2517_;
}
}
default: 
{
uint8_t v___x_2546_; 
v___x_2546_ = 0;
return v___x_2546_;
}
}
}
else
{
uint8_t v___x_2547_; 
v___x_2547_ = 0;
return v___x_2547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_2548_, lean_object* v_x_2549_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2550_; uint8_t v_res_2551_; lean_object* v_r_2552_; 
v_suppressElabErrors_boxed_2550_ = lean_unbox(v_suppressElabErrors_2548_);
v_res_2551_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(v_suppressElabErrors_boxed_2550_, v_x_2549_);
lean_dec(v_x_2549_);
v_r_2552_ = lean_box(v_res_2551_);
return v_r_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(lean_object* v_ref_2553_, lean_object* v_msgData_2554_, uint8_t v_severity_2555_, uint8_t v_isSilent_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___y_2563_; lean_object* v___y_2564_; uint8_t v___y_2565_; lean_object* v___y_2566_; uint8_t v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v_toCold_2570_; lean_object* v___y_2571_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; uint8_t v___y_2603_; uint8_t v___y_2604_; uint8_t v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2627_; uint8_t v___y_2628_; lean_object* v___y_2629_; uint8_t v___y_2630_; uint8_t v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; uint8_t v___y_2637_; uint8_t v___y_2638_; uint8_t v___x_2648_; uint8_t v___y_2650_; uint8_t v___x_2656_; 
v___x_2648_ = 2;
v___x_2656_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2555_, v___x_2648_);
if (v___x_2656_ == 0)
{
v___y_2650_ = v___x_2656_;
goto v___jp_2649_;
}
else
{
uint8_t v___x_2657_; 
lean_inc_ref(v_msgData_2554_);
v___x_2657_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2554_);
if (v___x_2657_ == 0)
{
v___y_2650_ = v___x_2657_;
goto v___jp_2649_;
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
lean_dec_ref(v_msgData_2554_);
v___x_2658_ = lean_box(0);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
return v___x_2659_;
}
}
v___jp_2562_:
{
lean_object* v_currNamespace_2572_; lean_object* v_openDecls_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v_env_2578_; lean_object* v_nextMacroScope_2579_; lean_object* v_ngen_2580_; lean_object* v_auxDeclNGen_2581_; lean_object* v_traceState_2582_; lean_object* v_cache_2583_; lean_object* v_recordedDeps_2584_; lean_object* v_messages_2585_; lean_object* v_infoState_2586_; lean_object* v_snapshotTasks_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2598_; 
v_currNamespace_2572_ = lean_ctor_get(v_toCold_2570_, 4);
v_openDecls_2573_ = lean_ctor_get(v_toCold_2570_, 5);
lean_inc(v_openDecls_2573_);
lean_inc(v_currNamespace_2572_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_currNamespace_2572_);
lean_ctor_set(v___x_2574_, 1, v_openDecls_2573_);
v___x_2575_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___y_2569_);
lean_inc_ref(v___y_2568_);
lean_inc_ref(v___y_2563_);
v___x_2576_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2576_, 0, v___y_2563_);
lean_ctor_set(v___x_2576_, 1, v___y_2564_);
lean_ctor_set(v___x_2576_, 2, v___y_2566_);
lean_ctor_set(v___x_2576_, 3, v___y_2568_);
lean_ctor_set(v___x_2576_, 4, v___x_2575_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*5, v___y_2567_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*5 + 1, v___y_2565_);
lean_ctor_set_uint8(v___x_2576_, sizeof(void*)*5 + 2, v_isSilent_2556_);
v___x_2577_ = lean_st_ref_take(v___y_2571_);
v_env_2578_ = lean_ctor_get(v___x_2577_, 0);
v_nextMacroScope_2579_ = lean_ctor_get(v___x_2577_, 1);
v_ngen_2580_ = lean_ctor_get(v___x_2577_, 2);
v_auxDeclNGen_2581_ = lean_ctor_get(v___x_2577_, 3);
v_traceState_2582_ = lean_ctor_get(v___x_2577_, 4);
v_cache_2583_ = lean_ctor_get(v___x_2577_, 5);
v_recordedDeps_2584_ = lean_ctor_get(v___x_2577_, 6);
v_messages_2585_ = lean_ctor_get(v___x_2577_, 7);
v_infoState_2586_ = lean_ctor_get(v___x_2577_, 8);
v_snapshotTasks_2587_ = lean_ctor_get(v___x_2577_, 9);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2589_ = v___x_2577_;
v_isShared_2590_ = v_isSharedCheck_2598_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_snapshotTasks_2587_);
lean_inc(v_infoState_2586_);
lean_inc(v_messages_2585_);
lean_inc(v_recordedDeps_2584_);
lean_inc(v_cache_2583_);
lean_inc(v_traceState_2582_);
lean_inc(v_auxDeclNGen_2581_);
lean_inc(v_ngen_2580_);
lean_inc(v_nextMacroScope_2579_);
lean_inc(v_env_2578_);
lean_dec(v___x_2577_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2598_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2591_ = lean_box(0);
v___x_2592_ = l_Lean_MessageLog_add(v___x_2576_, v_messages_2585_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 7, v___x_2592_);
v___x_2594_ = v___x_2589_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_env_2578_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v_nextMacroScope_2579_);
lean_ctor_set(v_reuseFailAlloc_2597_, 2, v_ngen_2580_);
lean_ctor_set(v_reuseFailAlloc_2597_, 3, v_auxDeclNGen_2581_);
lean_ctor_set(v_reuseFailAlloc_2597_, 4, v_traceState_2582_);
lean_ctor_set(v_reuseFailAlloc_2597_, 5, v_cache_2583_);
lean_ctor_set(v_reuseFailAlloc_2597_, 6, v_recordedDeps_2584_);
lean_ctor_set(v_reuseFailAlloc_2597_, 7, v___x_2592_);
lean_ctor_set(v_reuseFailAlloc_2597_, 8, v_infoState_2586_);
lean_ctor_set(v_reuseFailAlloc_2597_, 9, v_snapshotTasks_2587_);
v___x_2594_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2595_ = lean_st_ref_put(v___y_2571_, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2591_);
return v___x_2596_;
}
}
}
v___jp_2599_:
{
lean_object* v_fileName_2608_; lean_object* v_fileMap_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2625_; 
v_fileName_2608_ = lean_ctor_get(v___y_2606_, 0);
v_fileMap_2609_ = lean_ctor_get(v___y_2606_, 1);
v___x_2610_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2554_);
v___x_2611_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(v___x_2610_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2625_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2625_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_inc_ref_n(v_fileMap_2609_, 2);
v___x_2616_ = l_Lean_FileMap_toPosition(v_fileMap_2609_, v___y_2602_);
lean_dec(v___y_2602_);
v___x_2617_ = l_Lean_FileMap_toPosition(v_fileMap_2609_, v___y_2607_);
lean_dec(v___y_2607_);
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
v___x_2619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
if (v___y_2603_ == 0)
{
lean_del_object(v___x_2614_);
lean_dec_ref(v___y_2600_);
v___y_2563_ = v_fileName_2608_;
v___y_2564_ = v___x_2616_;
v___y_2565_ = v___y_2604_;
v___y_2566_ = v___x_2618_;
v___y_2567_ = v___y_2605_;
v___y_2568_ = v___x_2619_;
v___y_2569_ = v_a_2612_;
v_toCold_2570_ = v___y_2601_;
v___y_2571_ = v___y_2560_;
goto v___jp_2562_;
}
else
{
uint8_t v___x_2620_; 
lean_inc(v_a_2612_);
v___x_2620_ = l_Lean_MessageData_hasTag(v___y_2600_, v_a_2612_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
lean_dec_ref_known(v___x_2618_, 1);
lean_dec_ref(v___x_2616_);
lean_dec(v_a_2612_);
v___x_2621_ = lean_box(0);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v___x_2621_);
v___x_2623_ = v___x_2614_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
else
{
lean_del_object(v___x_2614_);
v___y_2563_ = v_fileName_2608_;
v___y_2564_ = v___x_2616_;
v___y_2565_ = v___y_2604_;
v___y_2566_ = v___x_2618_;
v___y_2567_ = v___y_2605_;
v___y_2568_ = v___x_2619_;
v___y_2569_ = v_a_2612_;
v_toCold_2570_ = v___y_2601_;
v___y_2571_ = v___y_2560_;
goto v___jp_2562_;
}
}
}
}
v___jp_2626_:
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Syntax_getTailPos_x3f(v___y_2632_, v___y_2631_);
lean_dec(v___y_2632_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_inc(v___y_2633_);
v___y_2600_ = v___y_2627_;
v___y_2601_ = v___y_2629_;
v___y_2602_ = v___y_2633_;
v___y_2603_ = v___y_2628_;
v___y_2604_ = v___y_2630_;
v___y_2605_ = v___y_2631_;
v___y_2606_ = v___y_2629_;
v___y_2607_ = v___y_2633_;
goto v___jp_2599_;
}
else
{
lean_object* v_val_2635_; 
v_val_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_val_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v___y_2600_ = v___y_2627_;
v___y_2601_ = v___y_2629_;
v___y_2602_ = v___y_2633_;
v___y_2603_ = v___y_2628_;
v___y_2604_ = v___y_2630_;
v___y_2605_ = v___y_2631_;
v___y_2606_ = v___y_2629_;
v___y_2607_ = v_val_2635_;
goto v___jp_2599_;
}
}
v___jp_2636_:
{
lean_object* v_toCold_2639_; lean_object* v_ref_2640_; uint8_t v_suppressElabErrors_2641_; lean_object* v___x_2642_; lean_object* v___f_2643_; lean_object* v_ref_2644_; lean_object* v___x_2645_; 
v_toCold_2639_ = lean_ctor_get(v___y_2559_, 0);
v_ref_2640_ = lean_ctor_get(v___y_2559_, 2);
v_suppressElabErrors_2641_ = lean_ctor_get_uint8(v___y_2559_, sizeof(void*)*3 + 2);
v___x_2642_ = lean_box(v_suppressElabErrors_2641_);
v___f_2643_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2643_, 0, v___x_2642_);
v_ref_2644_ = l_Lean_replaceRef(v_ref_2553_, v_ref_2640_);
v___x_2645_ = l_Lean_Syntax_getPos_x3f(v_ref_2644_, v___y_2637_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_unsigned_to_nat(0u);
v___y_2627_ = v___f_2643_;
v___y_2628_ = v_suppressElabErrors_2641_;
v___y_2629_ = v_toCold_2639_;
v___y_2630_ = v___y_2638_;
v___y_2631_ = v___y_2637_;
v___y_2632_ = v_ref_2644_;
v___y_2633_ = v___x_2646_;
goto v___jp_2626_;
}
else
{
lean_object* v_val_2647_; 
v_val_2647_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_val_2647_);
lean_dec_ref_known(v___x_2645_, 1);
v___y_2627_ = v___f_2643_;
v___y_2628_ = v_suppressElabErrors_2641_;
v___y_2629_ = v_toCold_2639_;
v___y_2630_ = v___y_2638_;
v___y_2631_ = v___y_2637_;
v___y_2632_ = v_ref_2644_;
v___y_2633_ = v_val_2647_;
goto v___jp_2626_;
}
}
v___jp_2649_:
{
uint8_t v___x_2651_; uint8_t v___x_2652_; 
v___x_2651_ = 1;
v___x_2652_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2555_, v___x_2651_);
if (v___x_2652_ == 0)
{
v___y_2637_ = v___y_2650_;
v___y_2638_ = v_severity_2555_;
goto v___jp_2636_;
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2653_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2559_);
v___x_2654_ = l_Lean_warningAsError;
v___x_2655_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(v___x_2653_, v___x_2654_);
lean_dec_ref(v___x_2653_);
if (v___x_2655_ == 0)
{
v___y_2637_ = v___y_2650_;
v___y_2638_ = v_severity_2555_;
goto v___jp_2636_;
}
else
{
v___y_2637_ = v___y_2650_;
v___y_2638_ = v___x_2648_;
goto v___jp_2636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_ref_2660_, lean_object* v_msgData_2661_, lean_object* v_severity_2662_, lean_object* v_isSilent_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v_severity_boxed_2669_; uint8_t v_isSilent_boxed_2670_; lean_object* v_res_2671_; 
v_severity_boxed_2669_ = lean_unbox(v_severity_2662_);
v_isSilent_boxed_2670_ = lean_unbox(v_isSilent_2663_);
v_res_2671_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(v_ref_2660_, v_msgData_2661_, v_severity_boxed_2669_, v_isSilent_boxed_2670_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v_ref_2660_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(lean_object* v_msgData_2672_, uint8_t v_severity_2673_, uint8_t v_isSilent_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_ref_2680_; lean_object* v___x_2681_; 
v_ref_2680_ = lean_ctor_get(v___y_2677_, 2);
v___x_2681_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(v_ref_2680_, v_msgData_2672_, v_severity_2673_, v_isSilent_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
return v___x_2681_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4___boxed(lean_object* v_msgData_2682_, lean_object* v_severity_2683_, lean_object* v_isSilent_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_){
_start:
{
uint8_t v_severity_boxed_2690_; uint8_t v_isSilent_boxed_2691_; lean_object* v_res_2692_; 
v_severity_boxed_2690_ = lean_unbox(v_severity_2683_);
v_isSilent_boxed_2691_ = lean_unbox(v_isSilent_2684_);
v_res_2692_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(v_msgData_2682_, v_severity_boxed_2690_, v_isSilent_boxed_2691_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(lean_object* v_msgData_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
uint8_t v___x_2699_; uint8_t v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = 0;
v___x_2700_ = 0;
v___x_2701_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(v_msgData_2693_, v___x_2699_, v___x_2700_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3___boxed(lean_object* v_msgData_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v_msgData_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v___y_2703_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(lean_object* v_constName_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; lean_object* v_env_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; 
v___x_2715_ = lean_st_ref_get(v___y_2713_);
v_env_2716_ = lean_ctor_get(v___x_2715_, 0);
lean_inc_ref(v_env_2716_);
lean_dec(v___x_2715_);
v___x_2717_ = 0;
lean_inc(v_constName_2709_);
v___x_2718_ = l_Lean_Environment_find_x3f(v_env_2716_, v_constName_2709_, v___x_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
return v___x_2719_;
}
else
{
lean_object* v_val_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v_constName_2709_);
v_val_2720_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2718_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_val_2720_);
lean_dec(v___x_2718_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
lean_ctor_set_tag(v___x_2722_, 0);
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_val_2720_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1___boxed(lean_object* v_constName_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(v_constName_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2734_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v___x_2740_ = l_Lean_stringToMessageData(v___x_2739_);
return v___x_2740_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4));
v___x_2743_ = l_Lean_stringToMessageData(v___x_2742_);
return v___x_2743_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6));
v___x_2746_ = l_Lean_stringToMessageData(v___x_2745_);
return v___x_2746_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8));
v___x_2749_ = l_Lean_stringToMessageData(v___x_2748_);
return v___x_2749_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10));
v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(lean_object* v_declName_2753_, lean_object* v_params_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_, lean_object* v_a_2757_, lean_object* v_a_2758_){
_start:
{
lean_object* v___f_2760_; lean_object* v___x_2761_; 
v___f_2760_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1));
lean_inc(v_declName_2753_);
v___x_2761_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(v_declName_2753_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; lean_object* v___x_2765_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
v___x_2763_ = l_Lean_ConstantInfo_type(v_a_2762_);
lean_dec(v_a_2762_);
v___x_2764_ = 0;
v___x_2765_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v___x_2763_, v___f_2760_, v___x_2764_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2767_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
lean_inc_ref(v_params_2754_);
v___x_2767_ = l_Lean_Meta_Grind_main(v_a_2766_, v_params_2754_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2856_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2770_ = v___x_2767_;
v_isShared_2771_ = v_isSharedCheck_2856_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2767_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2856_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v_counters_2772_; lean_object* v_config_2773_; lean_object* v_thm_2774_; lean_object* v_instances_2775_; lean_object* v_min_2776_; lean_object* v_detailed_2777_; lean_object* v___x_2778_; lean_object* v___y_2786_; lean_object* v___y_2787_; lean_object* v___y_2788_; lean_object* v___y_2789_; uint8_t v___x_2814_; 
v_counters_2772_ = lean_ctor_get(v_a_2768_, 4);
lean_inc_ref(v_counters_2772_);
lean_dec(v_a_2768_);
v_config_2773_ = lean_ctor_get(v_params_2754_, 0);
lean_inc_ref(v_config_2773_);
lean_dec_ref(v_params_2754_);
v_thm_2774_ = lean_ctor_get(v_counters_2772_, 0);
lean_inc_ref(v_thm_2774_);
lean_dec_ref(v_counters_2772_);
v_instances_2775_ = lean_ctor_get(v_config_2773_, 4);
lean_inc(v_instances_2775_);
v_min_2776_ = lean_ctor_get(v_config_2773_, 14);
lean_inc(v_min_2776_);
v_detailed_2777_ = lean_ctor_get(v_config_2773_, 15);
lean_inc(v_detailed_2777_);
lean_dec_ref(v_config_2773_);
v___x_2778_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(v_thm_2774_);
v___x_2814_ = lean_nat_dec_lt(v_min_2776_, v___x_2778_);
if (v___x_2814_ == 0)
{
lean_dec(v_instances_2775_);
v___y_2786_ = v_a_2755_;
v___y_2787_ = v_a_2756_;
v___y_2788_ = v_a_2757_;
v___y_2789_ = v_a_2758_;
goto v___jp_2785_;
}
else
{
uint8_t v___x_2815_; 
v___x_2815_ = lean_nat_dec_le(v_instances_2775_, v___x_2778_);
lean_dec(v_instances_2775_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2816_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5);
lean_inc(v_declName_2753_);
v___x_2817_ = l_Lean_MessageData_ofName(v_declName_2753_);
v___x_2818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2816_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7);
v___x_2820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2818_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
lean_inc(v___x_2778_);
v___x_2821_ = l_Nat_reprFast(v___x_2778_);
v___x_2822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2821_);
v___x_2823_ = l_Lean_MessageData_ofFormat(v___x_2822_);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2820_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2824_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2826_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_dec_ref_known(v___x_2827_, 1);
v___y_2786_ = v_a_2755_;
v___y_2787_ = v_a_2756_;
v___y_2788_ = v_a_2757_;
v___y_2789_ = v_a_2758_;
goto v___jp_2785_;
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v___x_2778_);
lean_dec(v_detailed_2777_);
lean_dec(v_min_2776_);
lean_dec_ref(v_thm_2774_);
lean_del_object(v___x_2770_);
lean_dec(v_declName_2753_);
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
if (v_isShared_2831_ == 0)
{
v___x_2833_ = v___x_2830_;
goto v_reusejp_2832_;
}
else
{
lean_object* v_reuseFailAlloc_2834_; 
v_reuseFailAlloc_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_a_2828_);
v___x_2833_ = v_reuseFailAlloc_2834_;
goto v_reusejp_2832_;
}
v_reusejp_2832_:
{
return v___x_2833_;
}
}
}
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2836_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5);
lean_inc(v_declName_2753_);
v___x_2837_ = l_Lean_MessageData_ofName(v_declName_2753_);
v___x_2838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11);
v___x_2840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
lean_inc(v___x_2778_);
v___x_2841_ = l_Nat_reprFast(v___x_2778_);
v___x_2842_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
v___x_2843_ = l_Lean_MessageData_ofFormat(v___x_2842_);
v___x_2844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2840_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
v___x_2845_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9);
v___x_2846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2846_, 0, v___x_2844_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
v___x_2847_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2846_, v_a_2755_, v_a_2756_, v_a_2757_, v_a_2758_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_dec_ref_known(v___x_2847_, 1);
v___y_2786_ = v_a_2755_;
v___y_2787_ = v_a_2756_;
v___y_2788_ = v_a_2757_;
v___y_2789_ = v_a_2758_;
goto v___jp_2785_;
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v___x_2778_);
lean_dec(v_detailed_2777_);
lean_dec(v_min_2776_);
lean_dec_ref(v_thm_2774_);
lean_del_object(v___x_2770_);
lean_dec(v_declName_2753_);
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
}
v___jp_2779_:
{
uint8_t v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2783_; 
v___x_2780_ = lean_nat_dec_lt(v_min_2776_, v___x_2778_);
lean_dec(v___x_2778_);
lean_dec(v_min_2776_);
v___x_2781_ = lean_box(v___x_2780_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 0, v___x_2781_);
v___x_2783_ = v___x_2770_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2781_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
v___jp_2785_:
{
uint8_t v___x_2790_; 
v___x_2790_ = lean_nat_dec_lt(v_detailed_2777_, v___x_2778_);
lean_dec(v_detailed_2777_);
if (v___x_2790_ == 0)
{
lean_dec_ref(v_thm_2774_);
lean_dec(v_declName_2753_);
goto v___jp_2779_;
}
else
{
lean_object* v___x_2791_; 
v___x_2791_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(v_thm_2774_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
lean_dec_ref(v_thm_2774_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2793_ = l_Lean_MessageData_ofName(v_declName_2753_);
v___x_2794_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3);
v___x_2795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v_a_2792_);
v___x_2797_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2796_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_dec_ref_known(v___x_2797_, 1);
goto v___jp_2779_;
}
else
{
lean_object* v_a_2798_; lean_object* v___x_2800_; uint8_t v_isShared_2801_; uint8_t v_isSharedCheck_2805_; 
lean_dec(v___x_2778_);
lean_dec(v_min_2776_);
lean_del_object(v___x_2770_);
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2800_ = v___x_2797_;
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
else
{
lean_inc(v_a_2798_);
lean_dec(v___x_2797_);
v___x_2800_ = lean_box(0);
v_isShared_2801_ = v_isSharedCheck_2805_;
goto v_resetjp_2799_;
}
v_resetjp_2799_:
{
lean_object* v___x_2803_; 
if (v_isShared_2801_ == 0)
{
v___x_2803_ = v___x_2800_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec(v___x_2778_);
lean_dec(v_min_2776_);
lean_del_object(v___x_2770_);
lean_dec(v_declName_2753_);
v_a_2806_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2791_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2791_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
if (v_isShared_2809_ == 0)
{
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
return v___x_2811_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec_ref(v_params_2754_);
lean_dec(v_declName_2753_);
v_a_2857_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2767_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2767_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec_ref(v_params_2754_);
lean_dec(v_declName_2753_);
v_a_2865_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2765_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2765_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_dec_ref(v_params_2754_);
lean_dec(v_declName_2753_);
v_a_2873_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2761_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2761_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___boxed(lean_object* v_declName_2881_, lean_object* v_params_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v_res_2888_; 
v_res_2888_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_declName_2881_, v_params_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
lean_dec(v_a_2886_);
lean_dec_ref(v_a_2885_);
lean_dec(v_a_2884_);
lean_dec_ref(v_a_2883_);
return v_res_2888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_2889_, lean_object* v_name_2890_, uint8_t v_bi_2891_, lean_object* v_type_2892_, lean_object* v_k_2893_, uint8_t v_kind_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2890_, v_bi_2891_, v_type_2892_, v_k_2893_, v_kind_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2901_, lean_object* v_name_2902_, lean_object* v_bi_2903_, lean_object* v_type_2904_, lean_object* v_k_2905_, lean_object* v_kind_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
uint8_t v_bi_boxed_2912_; uint8_t v_kind_boxed_2913_; lean_object* v_res_2914_; 
v_bi_boxed_2912_ = lean_unbox(v_bi_2903_);
v_kind_boxed_2913_ = lean_unbox(v_kind_2906_);
v_res_2914_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(v_00_u03b1_2901_, v_name_2902_, v_bi_boxed_2912_, v_type_2904_, v_k_2905_, v_kind_boxed_2913_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(lean_object* v_00_u03b1_2915_, lean_object* v_name_2916_, lean_object* v_type_2917_, lean_object* v_k_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v_name_2916_, v_type_2917_, v_k_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___boxed(lean_object* v_00_u03b1_2925_, lean_object* v_name_2926_, lean_object* v_type_2927_, lean_object* v_k_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(v_00_u03b1_2925_, v_name_2926_, v_type_2927_, v_k_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg(){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__4___redArg___closed__0);
v___x_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg___boxed(lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(lean_object* v_00_u03b1_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___boxed(lean_object* v_00_u03b1_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(v_00_u03b1_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(lean_object* v_a_2958_, lean_object* v_as_2959_, size_t v_sz_2960_, size_t v_i_2961_, uint8_t v_b_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
uint8_t v_a_2969_; uint8_t v_addCodeAction_2973_; 
v_addCodeAction_2973_ = lean_usize_dec_lt(v_i_2961_, v_sz_2960_);
if (v_addCodeAction_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_dec_ref(v_a_2958_);
v___x_2974_ = lean_box(v_b_2962_);
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
return v___x_2975_;
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_a_2976_ = lean_array_uget_borrowed(v_as_2959_, v_i_2961_);
v___x_2977_ = lean_box(0);
lean_inc(v_a_2976_);
v___x_2978_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_2976_, v___x_2977_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
lean_inc_ref(v_a_2958_);
v___x_2980_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_a_2979_, v_a_2958_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; uint8_t v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = lean_unbox(v_a_2981_);
lean_dec(v_a_2981_);
if (v___x_2982_ == 0)
{
v_a_2969_ = v_b_2962_;
goto v___jp_2968_;
}
else
{
v_a_2969_ = v_addCodeAction_2973_;
goto v___jp_2968_;
}
}
else
{
lean_dec_ref(v_a_2958_);
return v___x_2980_;
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v_a_2958_);
v_a_2983_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2978_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2978_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
}
v___jp_2968_:
{
size_t v___x_2970_; size_t v___x_2971_; 
v___x_2970_ = ((size_t)1ULL);
v___x_2971_ = lean_usize_add(v_i_2961_, v___x_2970_);
v_i_2961_ = v___x_2971_;
v_b_2962_ = v_a_2969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg___boxed(lean_object* v_a_2991_, lean_object* v_as_2992_, lean_object* v_sz_2993_, lean_object* v_i_2994_, lean_object* v_b_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
size_t v_sz_boxed_3001_; size_t v_i_boxed_3002_; uint8_t v_b_boxed_3003_; lean_object* v_res_3004_; 
v_sz_boxed_3001_ = lean_unbox_usize(v_sz_2993_);
lean_dec(v_sz_2993_);
v_i_boxed_3002_ = lean_unbox_usize(v_i_2994_);
lean_dec(v_i_2994_);
v_b_boxed_3003_ = lean_unbox(v_b_2995_);
v_res_3004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_2991_, v_as_2992_, v_sz_boxed_3001_, v_i_boxed_3002_, v_b_boxed_3003_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v_as_2992_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(size_t v_sz_3012_, size_t v_i_3013_, lean_object* v_bs_3014_){
_start:
{
uint8_t v___x_3015_; 
v___x_3015_ = lean_usize_dec_lt(v_i_3013_, v_sz_3012_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3016_, 0, v_bs_3014_);
return v___x_3016_;
}
else
{
lean_object* v_v_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v_v_3017_ = lean_array_uget(v_bs_3014_, v_i_3013_);
v___x_3018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2));
lean_inc(v_v_3017_);
v___x_3019_ = l_Lean_Syntax_isOfKind(v_v_3017_, v___x_3018_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; 
lean_dec(v_v_3017_);
lean_dec_ref(v_bs_3014_);
v___x_3020_ = lean_box(0);
return v___x_3020_;
}
else
{
lean_object* v___x_3021_; lean_object* v_bs_x27_3022_; size_t v___x_3023_; size_t v___x_3024_; lean_object* v___x_3025_; 
v___x_3021_ = lean_unsigned_to_nat(0u);
v_bs_x27_3022_ = lean_array_uset(v_bs_3014_, v_i_3013_, v___x_3021_);
v___x_3023_ = ((size_t)1ULL);
v___x_3024_ = lean_usize_add(v_i_3013_, v___x_3023_);
v___x_3025_ = lean_array_uset(v_bs_x27_3022_, v_i_3013_, v_v_3017_);
v_i_3013_ = v___x_3024_;
v_bs_3014_ = v___x_3025_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___boxed(lean_object* v_sz_3027_, lean_object* v_i_3028_, lean_object* v_bs_3029_){
_start:
{
size_t v_sz_boxed_3030_; size_t v_i_boxed_3031_; lean_object* v_res_3032_; 
v_sz_boxed_3030_ = lean_unbox_usize(v_sz_3027_);
lean_dec(v_sz_3027_);
v_i_boxed_3031_ = lean_unbox_usize(v_i_3028_);
lean_dec(v_i_3028_);
v_res_3032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_boxed_3030_, v_i_boxed_3031_, v_bs_3029_);
return v_res_3032_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9));
v___x_3049_ = l_String_toRawSubstring_x27(v___x_3048_);
return v___x_3049_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13(void){
_start:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Array_mkArray0___redArg();
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(uint8_t v___x_3056_, lean_object* v_stx_3057_, lean_object* v___x_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_){
_start:
{
if (v___x_3056_ == 0)
{
lean_object* v___x_3066_; 
lean_dec_ref(v___x_3058_);
lean_dec(v_stx_3057_);
v___x_3066_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3066_;
}
else
{
lean_object* v_toCold_3067_; lean_object* v_currRecDepth_3068_; lean_object* v_ref_3069_; uint16_t v_optionFlags_3070_; uint8_t v_suppressElabErrors_3071_; uint8_t v_checkDeprecated_3072_; uint8_t v_isRecordingDeps_3073_; lean_object* v_fileName_3074_; lean_object* v_fileMap_3075_; lean_object* v_options_3076_; lean_object* v_maxRecDepth_3077_; lean_object* v_currNamespace_3078_; lean_object* v_openDecls_3079_; lean_object* v_initHeartbeats_3080_; lean_object* v_quotContext_3081_; lean_object* v_currMacroScope_3082_; lean_object* v_cancelTk_x3f_3083_; lean_object* v_inheritedTraceOptions_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; size_t v_sz_3088_; size_t v___x_3089_; lean_object* v___x_3090_; 
v_toCold_3067_ = lean_ctor_get(v___y_3063_, 0);
v_currRecDepth_3068_ = lean_ctor_get(v___y_3063_, 1);
v_ref_3069_ = lean_ctor_get(v___y_3063_, 2);
v_optionFlags_3070_ = lean_ctor_get_uint16(v___y_3063_, sizeof(void*)*3);
v_suppressElabErrors_3071_ = lean_ctor_get_uint8(v___y_3063_, sizeof(void*)*3 + 2);
v_checkDeprecated_3072_ = lean_ctor_get_uint8(v___y_3063_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3073_ = lean_ctor_get_uint8(v___y_3063_, sizeof(void*)*3 + 4);
v_fileName_3074_ = lean_ctor_get(v_toCold_3067_, 0);
v_fileMap_3075_ = lean_ctor_get(v_toCold_3067_, 1);
v_options_3076_ = lean_ctor_get(v_toCold_3067_, 2);
v_maxRecDepth_3077_ = lean_ctor_get(v_toCold_3067_, 3);
v_currNamespace_3078_ = lean_ctor_get(v_toCold_3067_, 4);
v_openDecls_3079_ = lean_ctor_get(v_toCold_3067_, 5);
v_initHeartbeats_3080_ = lean_ctor_get(v_toCold_3067_, 6);
v_quotContext_3081_ = lean_ctor_get(v_toCold_3067_, 8);
v_currMacroScope_3082_ = lean_ctor_get(v_toCold_3067_, 9);
v_cancelTk_x3f_3083_ = lean_ctor_get(v_toCold_3067_, 10);
v_inheritedTraceOptions_3084_ = lean_ctor_get(v_toCold_3067_, 11);
v___x_3085_ = lean_unsigned_to_nat(2u);
v___x_3086_ = l_Lean_Syntax_getArg(v_stx_3057_, v___x_3085_);
v___x_3087_ = l_Lean_Syntax_getArgs(v___x_3086_);
lean_dec(v___x_3086_);
v_sz_3088_ = lean_array_size(v___x_3087_);
v___x_3089_ = ((size_t)0ULL);
v___x_3090_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_3088_, v___x_3089_, v___x_3087_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v___x_3091_; 
lean_dec_ref(v___x_3058_);
lean_dec(v_stx_3057_);
v___x_3091_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3091_;
}
else
{
lean_object* v_val_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v_ids_3098_; lean_object* v___x_3099_; 
v_val_3092_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v___x_3090_, 1);
v___x_3093_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inheritedTraceOptions_3084_);
lean_inc(v_cancelTk_x3f_3083_);
lean_inc(v_currMacroScope_3082_);
lean_inc(v_quotContext_3081_);
lean_inc(v_initHeartbeats_3080_);
lean_inc(v_openDecls_3079_);
lean_inc(v_currNamespace_3078_);
lean_inc(v_maxRecDepth_3077_);
lean_inc_ref(v_options_3076_);
lean_inc_ref(v_fileMap_3075_);
lean_inc_ref(v_fileName_3074_);
v___x_3094_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3094_, 0, v_fileName_3074_);
lean_ctor_set(v___x_3094_, 1, v_fileMap_3075_);
lean_ctor_set(v___x_3094_, 2, v_options_3076_);
lean_ctor_set(v___x_3094_, 3, v_maxRecDepth_3077_);
lean_ctor_set(v___x_3094_, 4, v_currNamespace_3078_);
lean_ctor_set(v___x_3094_, 5, v_openDecls_3079_);
lean_ctor_set(v___x_3094_, 6, v_initHeartbeats_3080_);
lean_ctor_set(v___x_3094_, 7, v___x_3093_);
lean_ctor_set(v___x_3094_, 8, v_quotContext_3081_);
lean_ctor_set(v___x_3094_, 9, v_currMacroScope_3082_);
lean_ctor_set(v___x_3094_, 10, v_cancelTk_x3f_3083_);
lean_ctor_set(v___x_3094_, 11, v_inheritedTraceOptions_3084_);
lean_inc(v_ref_3069_);
lean_inc(v_currRecDepth_3068_);
v___x_3095_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v_currRecDepth_3068_);
lean_ctor_set(v___x_3095_, 2, v_ref_3069_);
lean_ctor_set_uint16(v___x_3095_, sizeof(void*)*3, v_optionFlags_3070_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*3 + 2, v_suppressElabErrors_3071_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*3 + 3, v_checkDeprecated_3072_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*3 + 4, v_isRecordingDeps_3073_);
v___x_3096_ = lean_unsigned_to_nat(3u);
v___x_3097_ = l_Lean_Syntax_getArg(v_stx_3057_, v___x_3096_);
v_ids_3098_ = l_Lean_Syntax_getArgs(v___x_3097_);
lean_dec(v___x_3097_);
v___x_3099_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_val_3092_, v___y_3059_, v___x_3095_, v___y_3064_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3101_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3099_, 1);
v___x_3101_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_a_3100_, v___y_3061_, v___y_3062_, v___x_3095_, v___y_3064_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_a_3102_; uint8_t v___x_3103_; size_t v_sz_3104_; lean_object* v___x_3105_; 
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_a_3102_);
lean_dec_ref_known(v___x_3101_, 1);
v___x_3103_ = 0;
v_sz_3104_ = lean_array_size(v_ids_3098_);
v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_3102_, v_ids_3098_, v_sz_3104_, v___x_3089_, v___x_3103_, v___y_3061_, v___y_3062_, v___x_3095_, v___y_3064_);
lean_dec_ref(v_ids_3098_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3154_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3154_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3154_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
uint8_t v___x_3110_; 
v___x_3110_ = lean_unbox(v_a_3106_);
lean_dec(v_a_3106_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
lean_dec_ref_known(v___x_3095_, 3);
lean_dec_ref(v___x_3058_);
lean_dec(v_stx_3057_);
v___x_3111_ = lean_box(0);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v___x_3111_);
v___x_3113_ = v___x_3108_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
else
{
lean_object* v___x_3115_; lean_object* v_map_3116_; lean_object* v___x_3117_; uint8_t v___y_3119_; lean_object* v___x_3147_; 
v___x_3115_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___x_3095_);
v_map_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_map_3116_);
lean_dec_ref(v___x_3115_);
v___x_3117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3));
v___x_3147_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3116_, v___x_3117_);
lean_dec(v_map_3116_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_del_object(v___x_3108_);
v___y_3119_ = v___x_3103_;
goto v___jp_3118_;
}
else
{
lean_object* v_val_3148_; 
v_val_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_val_3148_);
lean_dec_ref_known(v___x_3147_, 1);
if (lean_obj_tag(v_val_3148_) == 1)
{
uint8_t v_v_3149_; 
v_v_3149_ = lean_ctor_get_uint8(v_val_3148_, 0);
lean_dec_ref_known(v_val_3148_, 0);
if (v_v_3149_ == 0)
{
lean_del_object(v___x_3108_);
v___y_3119_ = v_v_3149_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3152_; 
lean_dec_ref_known(v___x_3095_, 3);
lean_dec_ref(v___x_3058_);
lean_dec(v_stx_3057_);
v___x_3150_ = lean_box(0);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v___x_3150_);
v___x_3152_ = v___x_3108_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v___x_3150_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
else
{
lean_dec(v_val_3148_);
lean_del_object(v___x_3108_);
v___y_3119_ = v___x_3103_;
goto v___jp_3118_;
}
}
v___jp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3120_ = l_Lean_SourceInfo_fromRef(v_ref_3069_, v___y_3119_);
v___x_3121_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5));
v___x_3122_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0));
v___x_3123_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6));
v___x_3124_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7));
lean_inc_ref(v___x_3058_);
v___x_3125_ = l_Lean_Name_mkStr4(v___x_3058_, v___x_3122_, v___x_3123_, v___x_3124_);
v___x_3126_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8));
v___x_3127_ = l_Lean_Name_mkStr4(v___x_3058_, v___x_3122_, v___x_3123_, v___x_3126_);
lean_inc_n(v___x_3120_, 6);
v___x_3128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3120_);
lean_ctor_set(v___x_3128_, 1, v___x_3126_);
v___x_3129_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10);
v___x_3130_ = lean_box(0);
v___x_3131_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3120_);
lean_ctor_set(v___x_3131_, 1, v___x_3129_);
lean_ctor_set(v___x_3131_, 2, v___x_3117_);
lean_ctor_set(v___x_3131_, 3, v___x_3130_);
v___x_3132_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12));
v___x_3133_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13);
v___x_3134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3120_);
lean_ctor_set(v___x_3134_, 1, v___x_3132_);
lean_ctor_set(v___x_3134_, 2, v___x_3133_);
v___x_3135_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14));
v___x_3136_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3136_, 0, v___x_3120_);
lean_ctor_set(v___x_3136_, 1, v___x_3135_);
v___x_3137_ = l_Lean_Syntax_node4(v___x_3120_, v___x_3127_, v___x_3128_, v___x_3131_, v___x_3134_, v___x_3136_);
v___x_3138_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3120_);
lean_ctor_set(v___x_3138_, 1, v___x_3124_);
lean_inc(v_stx_3057_);
v___x_3139_ = l_Lean_Syntax_node3(v___x_3120_, v___x_3125_, v___x_3137_, v___x_3138_, v_stx_3057_);
v___x_3140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3140_, 0, v___x_3121_);
lean_ctor_set(v___x_3140_, 1, v___x_3139_);
v___x_3141_ = lean_box(0);
v___x_3142_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
lean_ctor_set(v___x_3142_, 2, v___x_3141_);
lean_ctor_set(v___x_3142_, 3, v___x_3141_);
lean_ctor_set(v___x_3142_, 4, v___x_3141_);
lean_ctor_set(v___x_3142_, 5, v___x_3141_);
v___x_3143_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15));
v___x_3144_ = 4;
v___x_3145_ = l_Lean_MessageData_nil;
v___x_3146_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_3057_, v___x_3142_, v___x_3141_, v___x_3143_, v___x_3141_, v___x_3144_, v___x_3145_, v___x_3095_, v___y_3064_);
lean_dec_ref_known(v___x_3095_, 3);
return v___x_3146_;
}
}
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec_ref_known(v___x_3095_, 3);
lean_dec_ref(v___x_3058_);
lean_dec(v_stx_3057_);
v_a_3155_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3105_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3105_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
else
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
lean_dec_ref(v_ids_3098_);
lean_dec_ref_known(v___x_3095_, 3);
lean_dec_ref(v___x_3058_);
lean_dec(v_stx_3057_);
v_a_3163_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3165_ = v___x_3101_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v___x_3101_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref(v_ids_3098_);
lean_dec_ref_known(v___x_3095_, 3);
lean_dec_ref(v___x_3058_);
lean_dec(v_stx_3057_);
v_a_3171_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3099_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3099_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3176_; 
if (v_isShared_3174_ == 0)
{
v___x_3176_ = v___x_3173_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_a_3171_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed(lean_object* v___x_3179_, lean_object* v_stx_3180_, lean_object* v___x_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
uint8_t v___x_5625__boxed_3189_; lean_object* v_res_3190_; 
v___x_5625__boxed_3189_ = lean_unbox(v___x_3179_);
v_res_3190_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(v___x_5625__boxed_3189_, v_stx_3180_, v___x_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(lean_object* v_stx_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; lean_object* v___x_3203_; lean_object* v___f_3204_; lean_object* v___x_3205_; 
v___x_3200_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_3201_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1));
lean_inc(v_stx_3196_);
v___x_3202_ = l_Lean_Syntax_isOfKind(v_stx_3196_, v___x_3201_);
v___x_3203_ = lean_box(v___x_3202_);
v___f_3204_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3204_, 0, v___x_3203_);
lean_closure_set(v___f_3204_, 1, v_stx_3196_);
lean_closure_set(v___f_3204_, 2, v___x_3200_);
v___x_3205_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3204_, v_a_3197_, v_a_3198_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed(lean_object* v_stx_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(v_stx_3206_, v_a_3207_, v_a_3208_);
lean_dec(v_a_3208_);
lean_dec_ref(v_a_3207_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(lean_object* v_a_3211_, lean_object* v_as_3212_, size_t v_sz_3213_, size_t v_i_3214_, uint8_t v_b_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___x_3223_; 
v___x_3223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_3211_, v_as_3212_, v_sz_3213_, v_i_3214_, v_b_3215_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___boxed(lean_object* v_a_3224_, lean_object* v_as_3225_, lean_object* v_sz_3226_, lean_object* v_i_3227_, lean_object* v_b_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
size_t v_sz_boxed_3236_; size_t v_i_boxed_3237_; uint8_t v_b_boxed_3238_; lean_object* v_res_3239_; 
v_sz_boxed_3236_ = lean_unbox_usize(v_sz_3226_);
lean_dec(v_sz_3226_);
v_i_boxed_3237_ = lean_unbox_usize(v_i_3227_);
lean_dec(v_i_3227_);
v_b_boxed_3238_ = lean_unbox(v_b_3228_);
v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(v_a_3224_, v_as_3225_, v_sz_boxed_3236_, v_i_boxed_3237_, v_b_boxed_3238_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v_as_3225_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1(){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3245_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3246_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1));
v___x_3247_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1));
v___x_3248_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed), 4, 0);
v___x_3249_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3245_, v___x_3246_, v___x_3247_, v___x_3248_);
return v___x_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___boxed(lean_object* v_a_3250_){
_start:
{
lean_object* v_res_3251_; 
v_res_3251_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1();
return v_res_3251_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(lean_object* v_name_3252_, lean_object* v_suff_3253_){
_start:
{
if (lean_obj_tag(v_name_3252_) == 1)
{
lean_object* v_str_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v_str_3254_ = lean_ctor_get(v_name_3252_, 1);
v___x_3255_ = 1;
v___x_3256_ = l_Lean_Name_toString(v_suff_3253_, v___x_3255_);
v___x_3257_ = lean_string_utf8_byte_size(v_str_3254_);
v___x_3258_ = lean_string_utf8_byte_size(v___x_3256_);
v___x_3259_ = lean_nat_dec_le(v___x_3258_, v___x_3257_);
if (v___x_3259_ == 0)
{
lean_dec_ref(v___x_3256_);
return v___x_3259_;
}
else
{
lean_object* v___x_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v___x_3260_ = lean_unsigned_to_nat(0u);
v___x_3261_ = lean_nat_sub(v___x_3257_, v___x_3258_);
v___x_3262_ = lean_string_memcmp(v_str_3254_, v___x_3256_, v___x_3261_, v___x_3260_, v___x_3258_);
lean_dec(v___x_3261_);
lean_dec_ref(v___x_3256_);
return v___x_3262_;
}
}
else
{
uint8_t v___x_3263_; 
lean_dec(v_suff_3253_);
v___x_3263_ = 0;
return v___x_3263_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix___boxed(lean_object* v_name_3264_, lean_object* v_suff_3265_){
_start:
{
uint8_t v_res_3266_; lean_object* v_r_3267_; 
v_res_3266_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(v_name_3264_, v_suff_3265_);
lean_dec(v_name_3264_);
v_r_3267_ = lean_box(v_res_3266_);
return v_r_3267_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(lean_object* v___x_3268_, lean_object* v_as_3269_, size_t v_i_3270_, size_t v_stop_3271_){
_start:
{
uint8_t v___x_3272_; 
v___x_3272_ = lean_usize_dec_eq(v_i_3270_, v_stop_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3273_ = lean_array_uget_borrowed(v_as_3269_, v_i_3270_);
v___x_3274_ = l_Lean_Name_isPrefixOf(v___x_3273_, v___x_3268_);
if (v___x_3274_ == 0)
{
size_t v___x_3275_; size_t v___x_3276_; 
v___x_3275_ = ((size_t)1ULL);
v___x_3276_ = lean_usize_add(v_i_3270_, v___x_3275_);
v_i_3270_ = v___x_3276_;
goto _start;
}
else
{
return v___x_3274_;
}
}
else
{
uint8_t v___x_3278_; 
v___x_3278_ = 0;
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1___boxed(lean_object* v___x_3279_, lean_object* v_as_3280_, lean_object* v_i_3281_, lean_object* v_stop_3282_){
_start:
{
size_t v_i_boxed_3283_; size_t v_stop_boxed_3284_; uint8_t v_res_3285_; lean_object* v_r_3286_; 
v_i_boxed_3283_ = lean_unbox_usize(v_i_3281_);
lean_dec(v_i_3281_);
v_stop_boxed_3284_ = lean_unbox_usize(v_stop_3282_);
lean_dec(v_stop_3282_);
v_res_3285_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(v___x_3279_, v_as_3280_, v_i_boxed_3283_, v_stop_boxed_3284_);
lean_dec_ref(v_as_3280_);
lean_dec(v___x_3279_);
v_r_3286_ = lean_box(v_res_3285_);
return v_r_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(lean_object* v_declName_3290_, lean_object* v_init_3291_, lean_object* v_x_3292_){
_start:
{
if (lean_obj_tag(v_x_3292_) == 0)
{
lean_object* v_k_3293_; lean_object* v_l_3294_; lean_object* v_r_3295_; lean_object* v___x_3296_; 
v_k_3293_ = lean_ctor_get(v_x_3292_, 1);
lean_inc(v_k_3293_);
v_l_3294_ = lean_ctor_get(v_x_3292_, 3);
lean_inc(v_l_3294_);
v_r_3295_ = lean_ctor_get(v_x_3292_, 4);
lean_inc(v_r_3295_);
lean_dec_ref_known(v_x_3292_, 5);
v___x_3296_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3290_, v_init_3291_, v_l_3294_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_dec(v_r_3295_);
lean_dec(v_k_3293_);
return v___x_3296_;
}
else
{
lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3310_; 
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3310_ == 0)
{
lean_object* v_unused_3311_; 
v_unused_3311_ = lean_ctor_get(v___x_3296_, 0);
lean_dec(v_unused_3311_);
v___x_3298_ = v___x_3296_;
v_isShared_3299_ = v_isSharedCheck_3310_;
goto v_resetjp_3297_;
}
else
{
lean_dec(v___x_3296_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3310_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3300_; uint8_t v___x_3301_; 
v___x_3300_ = lean_box(0);
v___x_3301_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(v_declName_3290_, v_k_3293_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; 
lean_del_object(v___x_3298_);
v___x_3302_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0));
v_init_3291_ = v___x_3302_;
v_x_3292_ = v_r_3295_;
goto _start;
}
else
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
lean_dec(v_r_3295_);
v___x_3304_ = lean_box(v___x_3301_);
v___x_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3305_);
lean_ctor_set(v___x_3306_, 1, v___x_3300_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set_tag(v___x_3298_, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3306_);
v___x_3308_ = v___x_3298_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
}
else
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3312_, 0, v_init_3291_);
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___boxed(lean_object* v_declName_3313_, lean_object* v_init_3314_, lean_object* v_x_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3313_, v_init_3314_, v_x_3315_);
lean_dec(v_declName_3313_);
return v_res_3316_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(lean_object* v_declName_3320_, lean_object* v_as_3321_, size_t v_i_3322_, size_t v_stop_3323_){
_start:
{
uint8_t v___x_3324_; 
v___x_3324_ = lean_usize_dec_eq(v_i_3322_, v_stop_3323_);
if (v___x_3324_ == 0)
{
uint8_t v___x_3325_; uint8_t v___y_3327_; lean_object* v___x_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3325_ = 1;
v___x_3331_ = lean_array_uget_borrowed(v_as_3321_, v_i_3322_);
v___x_3332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1));
v___x_3333_ = lean_name_eq(v___x_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
uint8_t v___x_3334_; 
v___x_3334_ = l_Lean_Name_isPrefixOf(v___x_3331_, v_declName_3320_);
v___y_3327_ = v___x_3334_;
goto v___jp_3326_;
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
lean_inc(v_declName_3320_);
v___x_3335_ = l_Lean_Name_components(v_declName_3320_);
v___x_3336_ = l_List_lengthTR___redArg(v___x_3335_);
lean_dec(v___x_3335_);
v___x_3337_ = lean_unsigned_to_nat(1u);
v___x_3338_ = lean_nat_dec_eq(v___x_3336_, v___x_3337_);
lean_dec(v___x_3336_);
v___y_3327_ = v___x_3338_;
goto v___jp_3326_;
}
v___jp_3326_:
{
if (v___y_3327_ == 0)
{
size_t v___x_3328_; size_t v___x_3329_; 
v___x_3328_ = ((size_t)1ULL);
v___x_3329_ = lean_usize_add(v_i_3322_, v___x_3328_);
v_i_3322_ = v___x_3329_;
goto _start;
}
else
{
lean_dec(v_declName_3320_);
return v___x_3325_;
}
}
}
else
{
uint8_t v___x_3339_; 
lean_dec(v_declName_3320_);
v___x_3339_ = 0;
return v___x_3339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___boxed(lean_object* v_declName_3340_, lean_object* v_as_3341_, lean_object* v_i_3342_, lean_object* v_stop_3343_){
_start:
{
size_t v_i_boxed_3344_; size_t v_stop_boxed_3345_; uint8_t v_res_3346_; lean_object* v_r_3347_; 
v_i_boxed_3344_ = lean_unbox_usize(v_i_3342_);
lean_dec(v_i_3342_);
v_stop_boxed_3345_ = lean_unbox_usize(v_stop_3343_);
lean_dec(v_stop_3343_);
v_res_3346_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(v_declName_3340_, v_as_3341_, v_i_boxed_3344_, v_stop_boxed_3345_);
lean_dec_ref(v_as_3341_);
v_r_3347_ = lean_box(v_res_3346_);
return v_r_3347_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(lean_object* v_prefixes_x3f_3348_, uint8_t v_inModule_3349_, lean_object* v___x_3350_, lean_object* v___x_3351_, lean_object* v___x_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_){
_start:
{
if (lean_obj_tag(v_a_3353_) == 0)
{
lean_object* v___x_3355_; 
lean_dec(v___x_3352_);
v___x_3355_ = lean_array_to_list(v_a_3354_);
return v___x_3355_;
}
else
{
lean_object* v_head_3356_; lean_object* v_tail_3357_; lean_object* v_val_3359_; 
v_head_3356_ = lean_ctor_get(v_a_3353_, 0);
lean_inc(v_head_3356_);
v_tail_3357_ = lean_ctor_get(v_a_3353_, 1);
lean_inc(v_tail_3357_);
lean_dec_ref_known(v_a_3353_, 2);
if (lean_obj_tag(v_head_3356_) == 0)
{
lean_object* v_declName_3362_; uint8_t v___x_3363_; 
v_declName_3362_ = lean_ctor_get(v_head_3356_, 0);
lean_inc(v_declName_3362_);
lean_dec_ref_known(v_head_3356_, 1);
v___x_3363_ = l_Lean_NameSet_contains(v___x_3351_, v_declName_3362_);
if (v___x_3363_ == 0)
{
lean_object* v___x_3364_; lean_object* v___y_3393_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v_a_3400_; 
v___x_3364_ = lean_box(0);
v___x_3398_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0));
lean_inc(v___x_3352_);
v___x_3399_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3362_, v___x_3398_, v___x_3352_);
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
lean_inc(v_a_3400_);
lean_dec_ref(v___x_3399_);
v___y_3393_ = v_a_3400_;
goto v___jp_3392_;
v___jp_3365_:
{
if (lean_obj_tag(v_prefixes_x3f_3348_) == 1)
{
if (v_inModule_3349_ == 0)
{
lean_object* v_val_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v_val_3366_ = lean_ctor_get(v_prefixes_x3f_3348_, 0);
v___x_3367_ = lean_unsigned_to_nat(0u);
v___x_3368_ = lean_array_get_size(v_val_3366_);
v___x_3369_ = lean_nat_dec_lt(v___x_3367_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_dec(v_declName_3362_);
v_a_3353_ = v_tail_3357_;
goto _start;
}
else
{
if (v___x_3369_ == 0)
{
lean_dec(v_declName_3362_);
v_a_3353_ = v_tail_3357_;
goto _start;
}
else
{
size_t v___x_3372_; size_t v___x_3373_; uint8_t v___x_3374_; 
v___x_3372_ = ((size_t)0ULL);
v___x_3373_ = lean_usize_of_nat(v___x_3368_);
lean_inc(v_declName_3362_);
v___x_3374_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(v_declName_3362_, v_val_3366_, v___x_3372_, v___x_3373_);
if (v___x_3374_ == 0)
{
lean_dec(v_declName_3362_);
v_a_3353_ = v_tail_3357_;
goto _start;
}
else
{
v_val_3359_ = v_declName_3362_;
goto v___jp_3358_;
}
}
}
}
else
{
lean_object* v_val_3376_; lean_object* v___x_3377_; 
v_val_3376_ = lean_ctor_get(v_prefixes_x3f_3348_, 0);
v___x_3377_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3350_, v_declName_3362_);
if (lean_obj_tag(v___x_3377_) == 1)
{
lean_object* v_val_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v_val_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_val_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v___x_3379_ = lean_unsigned_to_nat(0u);
v___x_3380_ = lean_array_get_size(v_val_3376_);
v___x_3381_ = lean_nat_dec_lt(v___x_3379_, v___x_3380_);
if (v___x_3381_ == 0)
{
lean_dec(v_val_3378_);
lean_dec(v_declName_3362_);
v_a_3353_ = v_tail_3357_;
goto _start;
}
else
{
lean_object* v___x_3383_; 
v___x_3383_ = l_Lean_Environment_header(v___x_3350_);
if (v___x_3381_ == 0)
{
lean_dec_ref(v___x_3383_);
lean_dec(v_val_3378_);
lean_dec(v_declName_3362_);
v_a_3353_ = v_tail_3357_;
goto _start;
}
else
{
lean_object* v_moduleNames_3385_; lean_object* v___x_3386_; size_t v___x_3387_; size_t v___x_3388_; uint8_t v___x_3389_; 
v_moduleNames_3385_ = lean_ctor_get(v___x_3383_, 4);
lean_inc_ref(v_moduleNames_3385_);
lean_dec_ref(v___x_3383_);
v___x_3386_ = lean_array_get(v___x_3364_, v_moduleNames_3385_, v_val_3378_);
lean_dec(v_val_3378_);
lean_dec_ref(v_moduleNames_3385_);
v___x_3387_ = ((size_t)0ULL);
v___x_3388_ = lean_usize_of_nat(v___x_3380_);
v___x_3389_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(v___x_3386_, v_val_3376_, v___x_3387_, v___x_3388_);
lean_dec(v___x_3386_);
if (v___x_3389_ == 0)
{
lean_dec(v_declName_3362_);
v_a_3353_ = v_tail_3357_;
goto _start;
}
else
{
v_val_3359_ = v_declName_3362_;
goto v___jp_3358_;
}
}
}
}
else
{
lean_dec(v___x_3377_);
lean_dec(v_declName_3362_);
v_a_3353_ = v_tail_3357_;
goto _start;
}
}
}
else
{
v_val_3359_ = v_declName_3362_;
goto v___jp_3358_;
}
}
v___jp_3392_:
{
lean_object* v_fst_3394_; 
v_fst_3394_ = lean_ctor_get(v___y_3393_, 0);
lean_inc(v_fst_3394_);
lean_dec_ref(v___y_3393_);
if (lean_obj_tag(v_fst_3394_) == 0)
{
goto v___jp_3365_;
}
else
{
lean_object* v_val_3395_; uint8_t v___x_3396_; 
v_val_3395_ = lean_ctor_get(v_fst_3394_, 0);
lean_inc(v_val_3395_);
lean_dec_ref_known(v_fst_3394_, 1);
v___x_3396_ = lean_unbox(v_val_3395_);
lean_dec(v_val_3395_);
if (v___x_3396_ == 0)
{
goto v___jp_3365_;
}
else
{
lean_dec(v_declName_3362_);
v_a_3353_ = v_tail_3357_;
goto _start;
}
}
}
}
else
{
lean_dec(v_declName_3362_);
v_a_3353_ = v_tail_3357_;
goto _start;
}
}
else
{
lean_dec(v_head_3356_);
v_a_3353_ = v_tail_3357_;
goto _start;
}
v___jp_3358_:
{
lean_object* v___x_3360_; 
v___x_3360_ = lean_array_push(v_a_3354_, v_val_3359_);
v_a_3353_ = v_tail_3357_;
v_a_3354_ = v___x_3360_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3___boxed(lean_object* v_prefixes_x3f_3403_, lean_object* v_inModule_3404_, lean_object* v___x_3405_, lean_object* v___x_3406_, lean_object* v___x_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
uint8_t v_inModule_boxed_3410_; lean_object* v_res_3411_; 
v_inModule_boxed_3410_ = lean_unbox(v_inModule_3404_);
v_res_3411_ = l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(v_prefixes_x3f_3403_, v_inModule_boxed_3410_, v___x_3405_, v___x_3406_, v___x_3407_, v_a_3408_, v_a_3409_);
lean_dec(v___x_3406_);
lean_dec_ref(v___x_3405_);
lean_dec(v_prefixes_x3f_3403_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(lean_object* v_prefixes_x3f_3414_, uint8_t v_inModule_3415_, lean_object* v_a_3416_){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v_env_3420_; lean_object* v___x_3421_; lean_object* v_toEnvExtension_3422_; lean_object* v_asyncMode_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v_env_3427_; lean_object* v___x_3428_; lean_object* v_toEnvExtension_3429_; lean_object* v_asyncMode_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3418_ = lean_box(1);
v___x_3419_ = lean_st_ref_get(v_a_3416_);
v_env_3420_ = lean_ctor_get(v___x_3419_, 0);
lean_inc_ref(v_env_3420_);
lean_dec(v___x_3419_);
v___x_3421_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_3422_ = lean_ctor_get(v___x_3421_, 0);
v_asyncMode_3423_ = lean_ctor_get(v_toEnvExtension_3422_, 2);
v___x_3424_ = lean_box(0);
v___x_3425_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3418_, v___x_3421_, v_env_3420_, v_asyncMode_3423_, v___x_3424_);
v___x_3426_ = lean_st_ref_get(v_a_3416_);
v_env_3427_ = lean_ctor_get(v___x_3426_, 0);
lean_inc_ref(v_env_3427_);
lean_dec(v___x_3426_);
v___x_3428_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_3429_ = lean_ctor_get(v___x_3428_, 0);
v_asyncMode_3430_ = lean_ctor_get(v_toEnvExtension_3429_, 2);
v___x_3431_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3418_, v___x_3428_, v_env_3427_, v_asyncMode_3430_, v___x_3424_);
v___x_3432_ = l_Lean_Meta_Grind_grindExt;
v___x_3433_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3432_, v_a_3416_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3446_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3446_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3446_ == 0)
{
v___x_3436_ = v___x_3433_;
v_isShared_3437_ = v_isSharedCheck_3446_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3433_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3446_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v_env_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3444_; 
v___x_3438_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_a_3434_);
lean_dec(v_a_3434_);
v___x_3439_ = lean_st_ref_get(v_a_3416_);
v_env_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc_ref(v_env_3440_);
lean_dec(v___x_3439_);
v___x_3441_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0));
v___x_3442_ = l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(v_prefixes_x3f_3414_, v_inModule_3415_, v_env_3440_, v___x_3425_, v___x_3431_, v___x_3438_, v___x_3441_);
lean_dec(v___x_3425_);
lean_dec_ref(v_env_3440_);
if (v_isShared_3437_ == 0)
{
lean_ctor_set(v___x_3436_, 0, v___x_3442_);
v___x_3444_ = v___x_3436_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3445_; 
v_reuseFailAlloc_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3445_, 0, v___x_3442_);
v___x_3444_ = v_reuseFailAlloc_3445_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
return v___x_3444_;
}
}
}
else
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3454_; 
lean_dec(v___x_3431_);
lean_dec(v___x_3425_);
v_a_3447_ = lean_ctor_get(v___x_3433_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3449_ = v___x_3433_;
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3433_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3454_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3450_ == 0)
{
v___x_3452_ = v___x_3449_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
return v___x_3452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___boxed(lean_object* v_prefixes_x3f_3455_, lean_object* v_inModule_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
uint8_t v_inModule_boxed_3459_; lean_object* v_res_3460_; 
v_inModule_boxed_3459_ = lean_unbox(v_inModule_3456_);
v_res_3460_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v_prefixes_x3f_3455_, v_inModule_boxed_3459_, v_a_3457_);
lean_dec(v_a_3457_);
lean_dec(v_prefixes_x3f_3455_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(lean_object* v_prefixes_x3f_3461_, uint8_t v_inModule_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v_prefixes_x3f_3461_, v_inModule_3462_, v_a_3464_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___boxed(lean_object* v_prefixes_x3f_3467_, lean_object* v_inModule_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_){
_start:
{
uint8_t v_inModule_boxed_3472_; lean_object* v_res_3473_; 
v_inModule_boxed_3472_ = lean_unbox(v_inModule_3468_);
v_res_3473_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(v_prefixes_x3f_3467_, v_inModule_boxed_3472_, v_a_3469_, v_a_3470_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
lean_dec(v_prefixes_x3f_3467_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(size_t v_sz_3474_, size_t v_i_3475_, lean_object* v_bs_3476_){
_start:
{
uint8_t v___x_3477_; 
v___x_3477_ = lean_usize_dec_lt(v_i_3475_, v_sz_3474_);
if (v___x_3477_ == 0)
{
return v_bs_3476_;
}
else
{
lean_object* v_v_3478_; lean_object* v___x_3479_; lean_object* v_bs_x27_3480_; lean_object* v___x_3481_; size_t v___x_3482_; size_t v___x_3483_; lean_object* v___x_3484_; 
v_v_3478_ = lean_array_uget(v_bs_3476_, v_i_3475_);
v___x_3479_ = lean_unsigned_to_nat(0u);
v_bs_x27_3480_ = lean_array_uset(v_bs_3476_, v_i_3475_, v___x_3479_);
v___x_3481_ = l_Lean_TSyntax_getId(v_v_3478_);
lean_dec(v_v_3478_);
v___x_3482_ = ((size_t)1ULL);
v___x_3483_ = lean_usize_add(v_i_3475_, v___x_3482_);
v___x_3484_ = lean_array_uset(v_bs_x27_3480_, v_i_3475_, v___x_3481_);
v_i_3475_ = v___x_3483_;
v_bs_3476_ = v___x_3484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4___boxed(lean_object* v_sz_3486_, lean_object* v_i_3487_, lean_object* v_bs_3488_){
_start:
{
size_t v_sz_boxed_3489_; size_t v_i_boxed_3490_; lean_object* v_res_3491_; 
v_sz_boxed_3489_ = lean_unbox_usize(v_sz_3486_);
lean_dec(v_sz_3486_);
v_i_boxed_3490_ = lean_unbox_usize(v_i_3487_);
lean_dec(v_i_3487_);
v_res_3491_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(v_sz_boxed_3489_, v_i_boxed_3490_, v_bs_3488_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(lean_object* v_hi_3492_, lean_object* v_pivot_3493_, lean_object* v_as_3494_, lean_object* v_i_3495_, lean_object* v_k_3496_){
_start:
{
uint8_t v___x_3497_; 
v___x_3497_ = lean_nat_dec_lt(v_k_3496_, v_hi_3492_);
if (v___x_3497_ == 0)
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec(v_k_3496_);
v___x_3498_ = lean_array_fswap(v_as_3494_, v_i_3495_, v_hi_3492_);
v___x_3499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3499_, 0, v_i_3495_);
lean_ctor_set(v___x_3499_, 1, v___x_3498_);
return v___x_3499_;
}
else
{
lean_object* v___x_3500_; uint8_t v___x_3501_; 
v___x_3500_ = lean_array_fget_borrowed(v_as_3494_, v_k_3496_);
v___x_3501_ = l_Lean_Name_lt(v___x_3500_, v_pivot_3493_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = lean_unsigned_to_nat(1u);
v___x_3503_ = lean_nat_add(v_k_3496_, v___x_3502_);
lean_dec(v_k_3496_);
v_k_3496_ = v___x_3503_;
goto _start;
}
else
{
lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3505_ = lean_array_fswap(v_as_3494_, v_i_3495_, v_k_3496_);
v___x_3506_ = lean_unsigned_to_nat(1u);
v___x_3507_ = lean_nat_add(v_i_3495_, v___x_3506_);
lean_dec(v_i_3495_);
v___x_3508_ = lean_nat_add(v_k_3496_, v___x_3506_);
lean_dec(v_k_3496_);
v_as_3494_ = v___x_3505_;
v_i_3495_ = v___x_3507_;
v_k_3496_ = v___x_3508_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg___boxed(lean_object* v_hi_3510_, lean_object* v_pivot_3511_, lean_object* v_as_3512_, lean_object* v_i_3513_, lean_object* v_k_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_3510_, v_pivot_3511_, v_as_3512_, v_i_3513_, v_k_3514_);
lean_dec(v_pivot_3511_);
lean_dec(v_hi_3510_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(lean_object* v_n_3516_, lean_object* v_as_3517_, lean_object* v_lo_3518_, lean_object* v_hi_3519_){
_start:
{
lean_object* v___y_3521_; uint8_t v___x_3531_; 
v___x_3531_ = lean_nat_dec_lt(v_lo_3518_, v_hi_3519_);
if (v___x_3531_ == 0)
{
lean_dec(v_lo_3518_);
return v_as_3517_;
}
else
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v_mid_3534_; lean_object* v___y_3536_; lean_object* v___y_3542_; lean_object* v___x_3547_; lean_object* v___x_3548_; uint8_t v___x_3549_; 
v___x_3532_ = lean_nat_add(v_lo_3518_, v_hi_3519_);
v___x_3533_ = lean_unsigned_to_nat(1u);
v_mid_3534_ = lean_nat_shiftr(v___x_3532_, v___x_3533_);
lean_dec(v___x_3532_);
v___x_3547_ = lean_array_fget_borrowed(v_as_3517_, v_mid_3534_);
v___x_3548_ = lean_array_fget_borrowed(v_as_3517_, v_lo_3518_);
v___x_3549_ = l_Lean_Name_lt(v___x_3547_, v___x_3548_);
if (v___x_3549_ == 0)
{
v___y_3542_ = v_as_3517_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_array_fswap(v_as_3517_, v_lo_3518_, v_mid_3534_);
v___y_3542_ = v___x_3550_;
goto v___jp_3541_;
}
v___jp_3535_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v___x_3537_ = lean_array_fget_borrowed(v___y_3536_, v_mid_3534_);
v___x_3538_ = lean_array_fget_borrowed(v___y_3536_, v_hi_3519_);
v___x_3539_ = l_Lean_Name_lt(v___x_3537_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_dec(v_mid_3534_);
v___y_3521_ = v___y_3536_;
goto v___jp_3520_;
}
else
{
lean_object* v___x_3540_; 
v___x_3540_ = lean_array_fswap(v___y_3536_, v_mid_3534_, v_hi_3519_);
lean_dec(v_mid_3534_);
v___y_3521_ = v___x_3540_;
goto v___jp_3520_;
}
}
v___jp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v___x_3543_ = lean_array_fget_borrowed(v___y_3542_, v_hi_3519_);
v___x_3544_ = lean_array_fget_borrowed(v___y_3542_, v_lo_3518_);
v___x_3545_ = l_Lean_Name_lt(v___x_3543_, v___x_3544_);
if (v___x_3545_ == 0)
{
v___y_3536_ = v___y_3542_;
goto v___jp_3535_;
}
else
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_array_fswap(v___y_3542_, v_lo_3518_, v_hi_3519_);
v___y_3536_ = v___x_3546_;
goto v___jp_3535_;
}
}
}
v___jp_3520_:
{
lean_object* v_pivot_3522_; lean_object* v___x_3523_; lean_object* v_fst_3524_; lean_object* v_snd_3525_; uint8_t v___x_3526_; 
v_pivot_3522_ = lean_array_fget(v___y_3521_, v_hi_3519_);
lean_inc_n(v_lo_3518_, 2);
v___x_3523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_3519_, v_pivot_3522_, v___y_3521_, v_lo_3518_, v_lo_3518_);
lean_dec(v_pivot_3522_);
v_fst_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_fst_3524_);
v_snd_3525_ = lean_ctor_get(v___x_3523_, 1);
lean_inc(v_snd_3525_);
lean_dec_ref(v___x_3523_);
v___x_3526_ = lean_nat_dec_le(v_hi_3519_, v_fst_3524_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3527_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_3516_, v_snd_3525_, v_lo_3518_, v_fst_3524_);
v___x_3528_ = lean_unsigned_to_nat(1u);
v___x_3529_ = lean_nat_add(v_fst_3524_, v___x_3528_);
lean_dec(v_fst_3524_);
v_as_3517_ = v___x_3527_;
v_lo_3518_ = v___x_3529_;
goto _start;
}
else
{
lean_dec(v_fst_3524_);
lean_dec(v_lo_3518_);
return v_snd_3525_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg___boxed(lean_object* v_n_3551_, lean_object* v_as_3552_, lean_object* v_lo_3553_, lean_object* v_hi_3554_){
_start:
{
lean_object* v_res_3555_; 
v_res_3555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_3551_, v_as_3552_, v_lo_3553_, v_hi_3554_);
lean_dec(v_hi_3554_);
lean_dec(v_n_3551_);
return v_res_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3556_, lean_object* v_msgData_3557_, uint8_t v_severity_3558_, uint8_t v_isSilent_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v___y_3566_; uint8_t v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; uint8_t v___y_3571_; lean_object* v___y_3572_; lean_object* v_toCold_3573_; lean_object* v___y_3574_; lean_object* v___y_3603_; lean_object* v___y_3604_; uint8_t v___y_3605_; lean_object* v___y_3606_; uint8_t v___y_3607_; uint8_t v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3630_; lean_object* v___y_3631_; uint8_t v___y_3632_; lean_object* v___y_3633_; uint8_t v___y_3634_; uint8_t v___y_3635_; lean_object* v___y_3636_; uint8_t v___y_3640_; uint8_t v___y_3641_; uint8_t v___x_3651_; uint8_t v___y_3653_; uint8_t v___x_3659_; 
v___x_3651_ = 2;
v___x_3659_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3558_, v___x_3651_);
if (v___x_3659_ == 0)
{
v___y_3653_ = v___x_3659_;
goto v___jp_3652_;
}
else
{
uint8_t v___x_3660_; 
lean_inc_ref(v_msgData_3557_);
v___x_3660_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3557_);
if (v___x_3660_ == 0)
{
v___y_3653_ = v___x_3660_;
goto v___jp_3652_;
}
else
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
lean_dec_ref(v_msgData_3557_);
v___x_3661_ = lean_box(0);
v___x_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
return v___x_3662_;
}
}
v___jp_3565_:
{
lean_object* v_currNamespace_3575_; lean_object* v_openDecls_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v_env_3581_; lean_object* v_nextMacroScope_3582_; lean_object* v_ngen_3583_; lean_object* v_auxDeclNGen_3584_; lean_object* v_traceState_3585_; lean_object* v_cache_3586_; lean_object* v_recordedDeps_3587_; lean_object* v_messages_3588_; lean_object* v_infoState_3589_; lean_object* v_snapshotTasks_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3601_; 
v_currNamespace_3575_ = lean_ctor_get(v_toCold_3573_, 4);
v_openDecls_3576_ = lean_ctor_get(v_toCold_3573_, 5);
lean_inc(v_openDecls_3576_);
lean_inc(v_currNamespace_3575_);
v___x_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3577_, 0, v_currNamespace_3575_);
lean_ctor_set(v___x_3577_, 1, v_openDecls_3576_);
v___x_3578_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v___y_3568_);
lean_inc_ref(v___y_3570_);
lean_inc_ref(v___y_3572_);
v___x_3579_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3579_, 0, v___y_3572_);
lean_ctor_set(v___x_3579_, 1, v___y_3566_);
lean_ctor_set(v___x_3579_, 2, v___y_3569_);
lean_ctor_set(v___x_3579_, 3, v___y_3570_);
lean_ctor_set(v___x_3579_, 4, v___x_3578_);
lean_ctor_set_uint8(v___x_3579_, sizeof(void*)*5, v___y_3567_);
lean_ctor_set_uint8(v___x_3579_, sizeof(void*)*5 + 1, v___y_3571_);
lean_ctor_set_uint8(v___x_3579_, sizeof(void*)*5 + 2, v_isSilent_3559_);
v___x_3580_ = lean_st_ref_take(v___y_3574_);
v_env_3581_ = lean_ctor_get(v___x_3580_, 0);
v_nextMacroScope_3582_ = lean_ctor_get(v___x_3580_, 1);
v_ngen_3583_ = lean_ctor_get(v___x_3580_, 2);
v_auxDeclNGen_3584_ = lean_ctor_get(v___x_3580_, 3);
v_traceState_3585_ = lean_ctor_get(v___x_3580_, 4);
v_cache_3586_ = lean_ctor_get(v___x_3580_, 5);
v_recordedDeps_3587_ = lean_ctor_get(v___x_3580_, 6);
v_messages_3588_ = lean_ctor_get(v___x_3580_, 7);
v_infoState_3589_ = lean_ctor_get(v___x_3580_, 8);
v_snapshotTasks_3590_ = lean_ctor_get(v___x_3580_, 9);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3592_ = v___x_3580_;
v_isShared_3593_ = v_isSharedCheck_3601_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_snapshotTasks_3590_);
lean_inc(v_infoState_3589_);
lean_inc(v_messages_3588_);
lean_inc(v_recordedDeps_3587_);
lean_inc(v_cache_3586_);
lean_inc(v_traceState_3585_);
lean_inc(v_auxDeclNGen_3584_);
lean_inc(v_ngen_3583_);
lean_inc(v_nextMacroScope_3582_);
lean_inc(v_env_3581_);
lean_dec(v___x_3580_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3601_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3597_; 
v___x_3594_ = lean_box(0);
v___x_3595_ = l_Lean_MessageLog_add(v___x_3579_, v_messages_3588_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 7, v___x_3595_);
v___x_3597_ = v___x_3592_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_env_3581_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_nextMacroScope_3582_);
lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_ngen_3583_);
lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_auxDeclNGen_3584_);
lean_ctor_set(v_reuseFailAlloc_3600_, 4, v_traceState_3585_);
lean_ctor_set(v_reuseFailAlloc_3600_, 5, v_cache_3586_);
lean_ctor_set(v_reuseFailAlloc_3600_, 6, v_recordedDeps_3587_);
lean_ctor_set(v_reuseFailAlloc_3600_, 7, v___x_3595_);
lean_ctor_set(v_reuseFailAlloc_3600_, 8, v_infoState_3589_);
lean_ctor_set(v_reuseFailAlloc_3600_, 9, v_snapshotTasks_3590_);
v___x_3597_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = lean_st_ref_put(v___y_3574_, v___x_3597_);
v___x_3599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3599_, 0, v___x_3594_);
return v___x_3599_;
}
}
}
v___jp_3602_:
{
lean_object* v_fileName_3611_; lean_object* v_fileMap_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3628_; 
v_fileName_3611_ = lean_ctor_get(v___y_3606_, 0);
v_fileMap_3612_ = lean_ctor_get(v___y_3606_, 1);
v___x_3613_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3557_);
v___x_3614_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__2(v___x_3613_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3617_ = v___x_3614_;
v_isShared_3618_ = v_isSharedCheck_3628_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3614_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3628_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
lean_inc_ref_n(v_fileMap_3612_, 2);
v___x_3619_ = l_Lean_FileMap_toPosition(v_fileMap_3612_, v___y_3609_);
lean_dec(v___y_3609_);
v___x_3620_ = l_Lean_FileMap_toPosition(v_fileMap_3612_, v___y_3610_);
lean_dec(v___y_3610_);
v___x_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
v___x_3622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
if (v___y_3607_ == 0)
{
lean_del_object(v___x_3617_);
lean_dec_ref(v___y_3603_);
v___y_3566_ = v___x_3619_;
v___y_3567_ = v___y_3605_;
v___y_3568_ = v_a_3615_;
v___y_3569_ = v___x_3621_;
v___y_3570_ = v___x_3622_;
v___y_3571_ = v___y_3608_;
v___y_3572_ = v_fileName_3611_;
v_toCold_3573_ = v___y_3604_;
v___y_3574_ = v___y_3563_;
goto v___jp_3565_;
}
else
{
uint8_t v___x_3623_; 
lean_inc(v_a_3615_);
v___x_3623_ = l_Lean_MessageData_hasTag(v___y_3603_, v_a_3615_);
if (v___x_3623_ == 0)
{
lean_object* v___x_3624_; lean_object* v___x_3626_; 
lean_dec_ref_known(v___x_3621_, 1);
lean_dec_ref(v___x_3619_);
lean_dec(v_a_3615_);
v___x_3624_ = lean_box(0);
if (v_isShared_3618_ == 0)
{
lean_ctor_set(v___x_3617_, 0, v___x_3624_);
v___x_3626_ = v___x_3617_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
else
{
lean_del_object(v___x_3617_);
v___y_3566_ = v___x_3619_;
v___y_3567_ = v___y_3605_;
v___y_3568_ = v_a_3615_;
v___y_3569_ = v___x_3621_;
v___y_3570_ = v___x_3622_;
v___y_3571_ = v___y_3608_;
v___y_3572_ = v_fileName_3611_;
v_toCold_3573_ = v___y_3604_;
v___y_3574_ = v___y_3563_;
goto v___jp_3565_;
}
}
}
}
v___jp_3629_:
{
lean_object* v___x_3637_; 
v___x_3637_ = l_Lean_Syntax_getTailPos_x3f(v___y_3633_, v___y_3634_);
lean_dec(v___y_3633_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_inc(v___y_3636_);
v___y_3603_ = v___y_3630_;
v___y_3604_ = v___y_3631_;
v___y_3605_ = v___y_3634_;
v___y_3606_ = v___y_3631_;
v___y_3607_ = v___y_3632_;
v___y_3608_ = v___y_3635_;
v___y_3609_ = v___y_3636_;
v___y_3610_ = v___y_3636_;
goto v___jp_3602_;
}
else
{
lean_object* v_val_3638_; 
v_val_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_val_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v___y_3603_ = v___y_3630_;
v___y_3604_ = v___y_3631_;
v___y_3605_ = v___y_3634_;
v___y_3606_ = v___y_3631_;
v___y_3607_ = v___y_3632_;
v___y_3608_ = v___y_3635_;
v___y_3609_ = v___y_3636_;
v___y_3610_ = v_val_3638_;
goto v___jp_3602_;
}
}
v___jp_3639_:
{
lean_object* v_toCold_3642_; lean_object* v_ref_3643_; uint8_t v_suppressElabErrors_3644_; lean_object* v___x_3645_; lean_object* v___f_3646_; lean_object* v_ref_3647_; lean_object* v___x_3648_; 
v_toCold_3642_ = lean_ctor_get(v___y_3562_, 0);
v_ref_3643_ = lean_ctor_get(v___y_3562_, 2);
v_suppressElabErrors_3644_ = lean_ctor_get_uint8(v___y_3562_, sizeof(void*)*3 + 2);
v___x_3645_ = lean_box(v_suppressElabErrors_3644_);
v___f_3646_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3646_, 0, v___x_3645_);
v_ref_3647_ = l_Lean_replaceRef(v_ref_3556_, v_ref_3643_);
v___x_3648_ = l_Lean_Syntax_getPos_x3f(v_ref_3647_, v___y_3640_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_unsigned_to_nat(0u);
v___y_3630_ = v___f_3646_;
v___y_3631_ = v_toCold_3642_;
v___y_3632_ = v_suppressElabErrors_3644_;
v___y_3633_ = v_ref_3647_;
v___y_3634_ = v___y_3640_;
v___y_3635_ = v___y_3641_;
v___y_3636_ = v___x_3649_;
goto v___jp_3629_;
}
else
{
lean_object* v_val_3650_; 
v_val_3650_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_val_3650_);
lean_dec_ref_known(v___x_3648_, 1);
v___y_3630_ = v___f_3646_;
v___y_3631_ = v_toCold_3642_;
v___y_3632_ = v_suppressElabErrors_3644_;
v___y_3633_ = v_ref_3647_;
v___y_3634_ = v___y_3640_;
v___y_3635_ = v___y_3641_;
v___y_3636_ = v_val_3650_;
goto v___jp_3629_;
}
}
v___jp_3652_:
{
uint8_t v___x_3654_; uint8_t v___x_3655_; 
v___x_3654_ = 1;
v___x_3655_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3558_, v___x_3654_);
if (v___x_3655_ == 0)
{
v___y_3640_ = v___y_3653_;
v___y_3641_ = v_severity_3558_;
goto v___jp_3639_;
}
else
{
lean_object* v___x_3656_; lean_object* v___x_3657_; uint8_t v___x_3658_; 
v___x_3656_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3562_);
v___x_3657_ = l_Lean_warningAsError;
v___x_3658_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1_spec__3_spec__5(v___x_3656_, v___x_3657_);
lean_dec_ref(v___x_3656_);
if (v___x_3658_ == 0)
{
v___y_3640_ = v___y_3653_;
v___y_3641_ = v_severity_3558_;
goto v___jp_3639_;
}
else
{
v___y_3640_ = v___y_3653_;
v___y_3641_ = v___x_3651_;
goto v___jp_3639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3663_, lean_object* v_msgData_3664_, lean_object* v_severity_3665_, lean_object* v_isSilent_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
uint8_t v_severity_boxed_3672_; uint8_t v_isSilent_boxed_3673_; lean_object* v_res_3674_; 
v_severity_boxed_3672_ = lean_unbox(v_severity_3665_);
v_isSilent_boxed_3673_ = lean_unbox(v_isSilent_3666_);
v_res_3674_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_3663_, v_msgData_3664_, v_severity_boxed_3672_, v_isSilent_boxed_3673_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v_ref_3663_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(lean_object* v_msgData_3675_, uint8_t v_severity_3676_, uint8_t v_isSilent_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_){
_start:
{
lean_object* v_ref_3685_; lean_object* v___x_3686_; 
v_ref_3685_ = lean_ctor_get(v___y_3682_, 2);
v___x_3686_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_3685_, v_msgData_3675_, v_severity_3676_, v_isSilent_3677_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
return v___x_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0___boxed(lean_object* v_msgData_3687_, lean_object* v_severity_3688_, lean_object* v_isSilent_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
uint8_t v_severity_boxed_3697_; uint8_t v_isSilent_boxed_3698_; lean_object* v_res_3699_; 
v_severity_boxed_3697_ = lean_unbox(v_severity_3688_);
v_isSilent_boxed_3698_ = lean_unbox(v_isSilent_3689_);
v_res_3699_ = l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(v_msgData_3687_, v_severity_boxed_3697_, v_isSilent_boxed_3698_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_, v___y_3695_);
lean_dec(v___y_3695_);
lean_dec_ref(v___y_3694_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
return v_res_3699_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(lean_object* v_msgData_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
uint8_t v___x_3708_; uint8_t v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = 2;
v___x_3709_ = 0;
v___x_3710_ = l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(v_msgData_3700_, v___x_3708_, v___x_3709_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0___boxed(lean_object* v_msgData_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(v_msgData_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
return v_res_3719_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0));
v___x_3722_ = l_Lean_stringToMessageData(v___x_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(lean_object* v_a_3723_, lean_object* v_as_3724_, size_t v_sz_3725_, size_t v_i_3726_, lean_object* v_b_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v_snd_3736_; uint8_t v___x_3740_; 
v___x_3740_ = lean_usize_dec_lt(v_i_3726_, v_sz_3725_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec_ref(v_a_3723_);
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_b_3727_);
return v___x_3741_;
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3743_; 
v_a_3742_ = lean_array_uget_borrowed(v_as_3724_, v_i_3726_);
lean_inc_ref(v_a_3723_);
lean_inc(v_a_3742_);
v___x_3743_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_a_3742_, v_a_3723_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; uint8_t v___x_3745_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
v___x_3745_ = lean_unbox(v_a_3744_);
lean_dec(v_a_3744_);
if (v___x_3745_ == 0)
{
v_snd_3736_ = v_b_3727_;
goto v___jp_3735_;
}
else
{
lean_object* v___x_3746_; 
lean_inc(v_a_3742_);
v___x_3746_ = lean_array_push(v_b_3727_, v_a_3742_);
v_snd_3736_ = v___x_3746_;
goto v___jp_3735_;
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3773_; 
v_a_3747_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3749_ = v___x_3743_;
v_isShared_3750_ = v_isSharedCheck_3773_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3743_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3773_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
uint8_t v___x_3751_; 
v___x_3751_ = l_Lean_Exception_isInterrupt(v_a_3747_);
if (v___x_3751_ == 0)
{
uint8_t v___x_3752_; 
lean_inc(v_a_3747_);
v___x_3752_ = l_Lean_Exception_isRuntime(v_a_3747_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
lean_del_object(v___x_3749_);
lean_inc(v_a_3742_);
v___x_3753_ = l_Lean_MessageData_ofName(v_a_3742_);
v___x_3754_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1);
v___x_3755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3753_);
lean_ctor_set(v___x_3755_, 1, v___x_3754_);
v___x_3756_ = l_Lean_Exception_toMessageData(v_a_3747_);
v___x_3757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3757_, 0, v___x_3755_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(v___x_3757_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_dec_ref_known(v___x_3758_, 1);
v_snd_3736_ = v_b_3727_;
goto v___jp_3735_;
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_dec_ref(v_b_3727_);
lean_dec_ref(v_a_3723_);
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3758_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3758_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
else
{
lean_object* v___x_3768_; 
lean_dec_ref(v_b_3727_);
lean_dec_ref(v_a_3723_);
if (v_isShared_3750_ == 0)
{
v___x_3768_ = v___x_3749_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3747_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
else
{
lean_object* v___x_3771_; 
lean_dec_ref(v_b_3727_);
lean_dec_ref(v_a_3723_);
if (v_isShared_3750_ == 0)
{
v___x_3771_ = v___x_3749_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3747_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
v___jp_3735_:
{
size_t v___x_3737_; size_t v___x_3738_; 
v___x_3737_ = ((size_t)1ULL);
v___x_3738_ = lean_usize_add(v_i_3726_, v___x_3737_);
v_i_3726_ = v___x_3738_;
v_b_3727_ = v_snd_3736_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___boxed(lean_object* v_a_3774_, lean_object* v_as_3775_, lean_object* v_sz_3776_, lean_object* v_i_3777_, lean_object* v_b_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
size_t v_sz_boxed_3786_; size_t v_i_boxed_3787_; lean_object* v_res_3788_; 
v_sz_boxed_3786_ = lean_unbox_usize(v_sz_3776_);
lean_dec(v_sz_3776_);
v_i_boxed_3787_ = lean_unbox_usize(v_i_3777_);
lean_dec(v_i_3777_);
v_res_3788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(v_a_3774_, v_as_3775_, v_sz_boxed_3786_, v_i_boxed_3787_, v_b_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec_ref(v_as_3775_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(uint8_t v___x_3790_, lean_object* v_as_3791_, size_t v_sz_3792_, size_t v_i_3793_, lean_object* v_b_3794_){
_start:
{
uint8_t v___x_3796_; 
v___x_3796_ = lean_usize_dec_lt(v_i_3793_, v_sz_3792_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; 
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v_b_3794_);
return v___x_3797_;
}
else
{
lean_object* v___x_3798_; lean_object* v_a_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; size_t v___x_3805_; size_t v___x_3806_; 
v___x_3798_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v_a_3799_ = lean_array_uget_borrowed(v_as_3791_, v_i_3793_);
v___x_3800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0));
lean_inc(v_a_3799_);
v___x_3801_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_3799_, v___x_3790_);
v___x_3802_ = lean_string_append(v___x_3800_, v___x_3801_);
lean_dec_ref(v___x_3801_);
v___x_3803_ = lean_string_append(v___x_3802_, v___x_3798_);
v___x_3804_ = lean_string_append(v_b_3794_, v___x_3803_);
lean_dec_ref(v___x_3803_);
v___x_3805_ = ((size_t)1ULL);
v___x_3806_ = lean_usize_add(v_i_3793_, v___x_3805_);
v_i_3793_ = v___x_3806_;
v_b_3794_ = v___x_3804_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___boxed(lean_object* v___x_3808_, lean_object* v_as_3809_, lean_object* v_sz_3810_, lean_object* v_i_3811_, lean_object* v_b_3812_, lean_object* v___y_3813_){
_start:
{
uint8_t v___x_10644__boxed_3814_; size_t v_sz_boxed_3815_; size_t v_i_boxed_3816_; lean_object* v_res_3817_; 
v___x_10644__boxed_3814_ = lean_unbox(v___x_3808_);
v_sz_boxed_3815_ = lean_unbox_usize(v_sz_3810_);
lean_dec(v_sz_3810_);
v_i_boxed_3816_ = lean_unbox_usize(v_i_3811_);
lean_dec(v_i_3811_);
v_res_3817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v___x_10644__boxed_3814_, v_as_3809_, v_sz_boxed_3815_, v_i_boxed_3816_, v_b_3812_);
lean_dec_ref(v_as_3809_);
return v_res_3817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(uint8_t v___x_3819_, lean_object* v_stx_3820_, uint8_t v___x_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
if (v___x_3819_ == 0)
{
lean_object* v___x_3829_; 
lean_dec(v_stx_3820_);
v___x_3829_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3829_;
}
else
{
lean_object* v_toCold_3830_; lean_object* v_currRecDepth_3831_; lean_object* v_ref_3832_; uint16_t v_optionFlags_3833_; uint8_t v_suppressElabErrors_3834_; uint8_t v_checkDeprecated_3835_; uint8_t v_isRecordingDeps_3836_; lean_object* v_fileName_3837_; lean_object* v_fileMap_3838_; lean_object* v_options_3839_; lean_object* v_maxRecDepth_3840_; lean_object* v_currNamespace_3841_; lean_object* v_openDecls_3842_; lean_object* v_initHeartbeats_3843_; lean_object* v_quotContext_3844_; lean_object* v_currMacroScope_3845_; lean_object* v_cancelTk_x3f_3846_; lean_object* v_inheritedTraceOptions_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; size_t v_sz_3851_; size_t v___x_3852_; lean_object* v___x_3853_; 
v_toCold_3830_ = lean_ctor_get(v___y_3826_, 0);
v_currRecDepth_3831_ = lean_ctor_get(v___y_3826_, 1);
v_ref_3832_ = lean_ctor_get(v___y_3826_, 2);
v_optionFlags_3833_ = lean_ctor_get_uint16(v___y_3826_, sizeof(void*)*3);
v_suppressElabErrors_3834_ = lean_ctor_get_uint8(v___y_3826_, sizeof(void*)*3 + 2);
v_checkDeprecated_3835_ = lean_ctor_get_uint8(v___y_3826_, sizeof(void*)*3 + 3);
v_isRecordingDeps_3836_ = lean_ctor_get_uint8(v___y_3826_, sizeof(void*)*3 + 4);
v_fileName_3837_ = lean_ctor_get(v_toCold_3830_, 0);
v_fileMap_3838_ = lean_ctor_get(v_toCold_3830_, 1);
v_options_3839_ = lean_ctor_get(v_toCold_3830_, 2);
v_maxRecDepth_3840_ = lean_ctor_get(v_toCold_3830_, 3);
v_currNamespace_3841_ = lean_ctor_get(v_toCold_3830_, 4);
v_openDecls_3842_ = lean_ctor_get(v_toCold_3830_, 5);
v_initHeartbeats_3843_ = lean_ctor_get(v_toCold_3830_, 6);
v_quotContext_3844_ = lean_ctor_get(v_toCold_3830_, 8);
v_currMacroScope_3845_ = lean_ctor_get(v_toCold_3830_, 9);
v_cancelTk_x3f_3846_ = lean_ctor_get(v_toCold_3830_, 10);
v_inheritedTraceOptions_3847_ = lean_ctor_get(v_toCold_3830_, 11);
v___x_3848_ = lean_unsigned_to_nat(2u);
v___x_3849_ = l_Lean_Syntax_getArg(v_stx_3820_, v___x_3848_);
v___x_3850_ = l_Lean_Syntax_getArgs(v___x_3849_);
lean_dec(v___x_3849_);
v_sz_3851_ = lean_array_size(v___x_3850_);
v___x_3852_ = ((size_t)0ULL);
v___x_3853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_3851_, v___x_3852_, v___x_3850_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v___x_3854_; 
lean_dec(v_stx_3820_);
v___x_3854_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3854_;
}
else
{
lean_object* v_val_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_4067_; 
v_val_3855_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_3857_ = v___x_3853_;
v_isShared_3858_ = v_isSharedCheck_4067_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_val_3855_);
lean_dec(v___x_3853_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_4067_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3859_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3925_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; uint8_t v___y_3962_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v_m_x3f_4000_; lean_object* v_ids_x3f_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v_m_x3f_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; uint8_t v___x_4056_; 
v___x_3859_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inheritedTraceOptions_3847_);
lean_inc(v_cancelTk_x3f_3846_);
lean_inc(v_currMacroScope_3845_);
lean_inc(v_quotContext_3844_);
lean_inc(v_initHeartbeats_3843_);
lean_inc(v_openDecls_3842_);
lean_inc(v_currNamespace_3841_);
lean_inc(v_maxRecDepth_3840_);
lean_inc_ref(v_options_3839_);
lean_inc_ref(v_fileMap_3838_);
lean_inc_ref(v_fileName_3837_);
v___x_3950_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3950_, 0, v_fileName_3837_);
lean_ctor_set(v___x_3950_, 1, v_fileMap_3838_);
lean_ctor_set(v___x_3950_, 2, v_options_3839_);
lean_ctor_set(v___x_3950_, 3, v_maxRecDepth_3840_);
lean_ctor_set(v___x_3950_, 4, v_currNamespace_3841_);
lean_ctor_set(v___x_3950_, 5, v_openDecls_3842_);
lean_ctor_set(v___x_3950_, 6, v_initHeartbeats_3843_);
lean_ctor_set(v___x_3950_, 7, v___x_3859_);
lean_ctor_set(v___x_3950_, 8, v_quotContext_3844_);
lean_ctor_set(v___x_3950_, 9, v_currMacroScope_3845_);
lean_ctor_set(v___x_3950_, 10, v_cancelTk_x3f_3846_);
lean_ctor_set(v___x_3950_, 11, v_inheritedTraceOptions_3847_);
lean_inc(v_ref_3832_);
lean_inc(v_currRecDepth_3831_);
v___x_3951_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_3951_, 0, v___x_3950_);
lean_ctor_set(v___x_3951_, 1, v_currRecDepth_3831_);
lean_ctor_set(v___x_3951_, 2, v_ref_3832_);
lean_ctor_set_uint16(v___x_3951_, sizeof(void*)*3, v_optionFlags_3833_);
lean_ctor_set_uint8(v___x_3951_, sizeof(void*)*3 + 2, v_suppressElabErrors_3834_);
lean_ctor_set_uint8(v___x_3951_, sizeof(void*)*3 + 3, v_checkDeprecated_3835_);
lean_ctor_set_uint8(v___x_3951_, sizeof(void*)*3 + 4, v_isRecordingDeps_3836_);
v___x_3952_ = lean_unsigned_to_nat(1u);
v___x_4040_ = lean_unsigned_to_nat(3u);
v___x_4041_ = l_Lean_Syntax_getArg(v_stx_3820_, v___x_4040_);
v___x_4056_ = l_Lean_Syntax_isNone(v___x_4041_);
if (v___x_4056_ == 0)
{
uint8_t v___x_4057_; 
lean_inc(v___x_4041_);
v___x_4057_ = l_Lean_Syntax_matchesNull(v___x_4041_, v___x_4040_);
if (v___x_4057_ == 0)
{
lean_object* v___x_4058_; 
lean_dec(v___x_4041_);
lean_dec_ref_known(v___x_3951_, 3);
lean_del_object(v___x_3857_);
lean_dec(v_val_3855_);
lean_dec(v_stx_3820_);
v___x_4058_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_4058_;
}
else
{
lean_object* v___x_4059_; uint8_t v___x_4060_; 
v___x_4059_ = l_Lean_Syntax_getArg(v___x_4041_, v___x_3952_);
v___x_4060_ = l_Lean_Syntax_isNone(v___x_4059_);
if (v___x_4060_ == 0)
{
uint8_t v___x_4061_; 
lean_inc(v___x_4059_);
v___x_4061_ = l_Lean_Syntax_matchesNull(v___x_4059_, v___x_3952_);
if (v___x_4061_ == 0)
{
lean_object* v___x_4062_; 
lean_dec(v___x_4059_);
lean_dec(v___x_4041_);
lean_dec_ref_known(v___x_3951_, 3);
lean_del_object(v___x_3857_);
lean_dec(v_val_3855_);
lean_dec(v_stx_3820_);
v___x_4062_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_4062_;
}
else
{
lean_object* v_m_x3f_4063_; lean_object* v___x_4064_; 
v_m_x3f_4063_ = l_Lean_Syntax_getArg(v___x_4059_, v___x_3859_);
lean_dec(v___x_4059_);
v___x_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4064_, 0, v_m_x3f_4063_);
v_m_x3f_4043_ = v___x_4064_;
v___y_4044_ = v___y_3822_;
v___y_4045_ = v___y_3823_;
v___y_4046_ = v___y_3824_;
v___y_4047_ = v___y_3825_;
v___y_4048_ = v___x_3951_;
v___y_4049_ = v___y_3827_;
goto v___jp_4042_;
}
}
else
{
lean_object* v___x_4065_; 
lean_dec(v___x_4059_);
v___x_4065_ = lean_box(0);
v_m_x3f_4043_ = v___x_4065_;
v___y_4044_ = v___y_3822_;
v___y_4045_ = v___y_3823_;
v___y_4046_ = v___y_3824_;
v___y_4047_ = v___y_3825_;
v___y_4048_ = v___x_3951_;
v___y_4049_ = v___y_3827_;
goto v___jp_4042_;
}
}
}
else
{
lean_object* v___x_4066_; 
lean_dec(v___x_4041_);
lean_del_object(v___x_3857_);
v___x_4066_ = lean_box(0);
v_m_x3f_4000_ = v___x_4066_;
v_ids_x3f_4001_ = v___x_4066_;
v___y_4002_ = v___y_3822_;
v___y_4003_ = v___y_3823_;
v___y_4004_ = v___y_3824_;
v___y_4005_ = v___y_3825_;
v___y_4006_ = v___x_3951_;
v___y_4007_ = v___y_3827_;
goto v___jp_3999_;
}
v___jp_3860_:
{
lean_object* v___x_3869_; size_t v_sz_3870_; lean_object* v___x_3871_; 
v___x_3869_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0));
v_sz_3870_ = lean_array_size(v___y_3868_);
v___x_3871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(v___y_3863_, v___y_3868_, v_sz_3870_, v___x_3852_, v___x_3869_, v___y_3864_, v___y_3867_, v___y_3866_, v___y_3865_, v___y_3862_, v___y_3861_);
lean_dec_ref(v___y_3868_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3915_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3874_ = v___x_3871_;
v_isShared_3875_ = v_isSharedCheck_3915_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3871_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3915_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v___x_3876_; uint8_t v___x_3877_; 
v___x_3876_ = lean_array_get_size(v_a_3872_);
v___x_3877_ = lean_nat_dec_eq(v___x_3876_, v___x_3859_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
lean_del_object(v___x_3874_);
v___x_3878_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5));
lean_inc(v_stx_3820_);
v___x_3879_ = l_Lean_PrettyPrinter_ppCategory(v___x_3878_, v_stx_3820_, v___y_3862_, v___y_3861_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; size_t v_sz_3885_; lean_object* v___x_3886_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___x_3881_ = l_Std_Format_defWidth;
v___x_3882_ = l_Std_Format_pretty(v_a_3880_, v___x_3881_, v___x_3859_, v___x_3859_);
v___x_3883_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v___x_3884_ = lean_string_append(v___x_3882_, v___x_3883_);
v_sz_3885_ = lean_array_size(v_a_3872_);
v___x_3886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v___x_3819_, v_a_3872_, v_sz_3885_, v___x_3852_, v___x_3884_);
lean_dec(v_a_3872_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; uint8_t v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3888_, 0, v_a_3887_);
v___x_3889_ = lean_box(0);
v___x_3890_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
lean_ctor_set(v___x_3890_, 2, v___x_3889_);
lean_ctor_set(v___x_3890_, 3, v___x_3889_);
lean_ctor_set(v___x_3890_, 4, v___x_3889_);
lean_ctor_set(v___x_3890_, 5, v___x_3889_);
v___x_3891_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0));
v___x_3892_ = 4;
v___x_3893_ = l_Lean_MessageData_nil;
v___x_3894_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_3820_, v___x_3890_, v___x_3889_, v___x_3891_, v___x_3889_, v___x_3892_, v___x_3893_, v___y_3862_, v___y_3861_);
lean_dec_ref(v___y_3862_);
return v___x_3894_;
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_dec_ref(v___y_3862_);
lean_dec(v_stx_3820_);
v_a_3895_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3886_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3886_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec(v_a_3872_);
lean_dec_ref(v___y_3862_);
lean_dec(v_stx_3820_);
v_a_3903_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3879_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3879_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
else
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
lean_dec(v_a_3872_);
lean_dec_ref(v___y_3862_);
lean_dec(v_stx_3820_);
v___x_3911_ = lean_box(0);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 0, v___x_3911_);
v___x_3913_ = v___x_3874_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec_ref(v___y_3862_);
lean_dec(v_stx_3820_);
v_a_3916_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3871_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3871_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
v___jp_3924_:
{
lean_object* v___x_3936_; 
v___x_3936_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v___y_3934_, v___y_3933_, v___y_3932_, v___y_3935_);
lean_dec(v___y_3935_);
lean_dec(v___y_3934_);
v___y_3861_ = v___y_3926_;
v___y_3862_ = v___y_3925_;
v___y_3863_ = v___y_3927_;
v___y_3864_ = v___y_3928_;
v___y_3865_ = v___y_3929_;
v___y_3866_ = v___y_3930_;
v___y_3867_ = v___y_3931_;
v___y_3868_ = v___x_3936_;
goto v___jp_3860_;
}
v___jp_3937_:
{
uint8_t v___x_3949_; 
v___x_3949_ = lean_nat_dec_le(v___y_3948_, v___y_3940_);
if (v___x_3949_ == 0)
{
lean_dec(v___y_3940_);
lean_inc(v___y_3948_);
v___y_3925_ = v___y_3939_;
v___y_3926_ = v___y_3938_;
v___y_3927_ = v___y_3941_;
v___y_3928_ = v___y_3942_;
v___y_3929_ = v___y_3943_;
v___y_3930_ = v___y_3944_;
v___y_3931_ = v___y_3946_;
v___y_3932_ = v___y_3948_;
v___y_3933_ = v___y_3945_;
v___y_3934_ = v___y_3947_;
v___y_3935_ = v___y_3948_;
goto v___jp_3924_;
}
else
{
v___y_3925_ = v___y_3939_;
v___y_3926_ = v___y_3938_;
v___y_3927_ = v___y_3941_;
v___y_3928_ = v___y_3942_;
v___y_3929_ = v___y_3943_;
v___y_3930_ = v___y_3944_;
v___y_3931_ = v___y_3946_;
v___y_3932_ = v___y_3948_;
v___y_3933_ = v___y_3945_;
v___y_3934_ = v___y_3947_;
v___y_3935_ = v___y_3940_;
goto v___jp_3924_;
}
}
v___jp_3953_:
{
lean_object* v___x_3963_; 
v___x_3963_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v___y_3954_, v___y_3962_, v___y_3956_);
lean_dec(v___y_3954_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; uint8_t v___x_3967_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3965_ = lean_array_mk(v_a_3964_);
v___x_3966_ = lean_array_get_size(v___x_3965_);
v___x_3967_ = lean_nat_dec_eq(v___x_3966_, v___x_3859_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; uint8_t v___x_3969_; 
v___x_3968_ = lean_nat_sub(v___x_3966_, v___x_3952_);
v___x_3969_ = lean_nat_dec_le(v___x_3859_, v___x_3968_);
if (v___x_3969_ == 0)
{
lean_inc(v___x_3968_);
v___y_3938_ = v___y_3956_;
v___y_3939_ = v___y_3955_;
v___y_3940_ = v___x_3968_;
v___y_3941_ = v___y_3957_;
v___y_3942_ = v___y_3958_;
v___y_3943_ = v___y_3959_;
v___y_3944_ = v___y_3960_;
v___y_3945_ = v___x_3965_;
v___y_3946_ = v___y_3961_;
v___y_3947_ = v___x_3966_;
v___y_3948_ = v___x_3968_;
goto v___jp_3937_;
}
else
{
v___y_3938_ = v___y_3956_;
v___y_3939_ = v___y_3955_;
v___y_3940_ = v___x_3968_;
v___y_3941_ = v___y_3957_;
v___y_3942_ = v___y_3958_;
v___y_3943_ = v___y_3959_;
v___y_3944_ = v___y_3960_;
v___y_3945_ = v___x_3965_;
v___y_3946_ = v___y_3961_;
v___y_3947_ = v___x_3966_;
v___y_3948_ = v___x_3859_;
goto v___jp_3937_;
}
}
else
{
v___y_3861_ = v___y_3956_;
v___y_3862_ = v___y_3955_;
v___y_3863_ = v___y_3957_;
v___y_3864_ = v___y_3958_;
v___y_3865_ = v___y_3959_;
v___y_3866_ = v___y_3960_;
v___y_3867_ = v___y_3961_;
v___y_3868_ = v___x_3965_;
goto v___jp_3860_;
}
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec_ref(v___y_3957_);
lean_dec_ref(v___y_3955_);
lean_dec(v_stx_3820_);
v_a_3970_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3963_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3963_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
v___jp_3978_:
{
uint8_t v___x_3987_; 
v___x_3987_ = 0;
v___y_3954_ = v___y_3979_;
v___y_3955_ = v___y_3981_;
v___y_3956_ = v___y_3980_;
v___y_3957_ = v___y_3982_;
v___y_3958_ = v___y_3983_;
v___y_3959_ = v___y_3984_;
v___y_3960_ = v___y_3985_;
v___y_3961_ = v___y_3986_;
v___y_3962_ = v___x_3987_;
goto v___jp_3953_;
}
v___jp_3988_:
{
if (lean_obj_tag(v___y_3991_) == 1)
{
lean_object* v_val_3998_; 
v_val_3998_ = lean_ctor_get(v___y_3991_, 0);
lean_inc(v_val_3998_);
lean_dec_ref_known(v___y_3991_, 1);
if (lean_obj_tag(v_val_3998_) == 1)
{
lean_dec_ref_known(v_val_3998_, 1);
v___y_3954_ = v___y_3997_;
v___y_3955_ = v___y_3990_;
v___y_3956_ = v___y_3989_;
v___y_3957_ = v___y_3992_;
v___y_3958_ = v___y_3993_;
v___y_3959_ = v___y_3994_;
v___y_3960_ = v___y_3995_;
v___y_3961_ = v___y_3996_;
v___y_3962_ = v___x_3821_;
goto v___jp_3953_;
}
else
{
lean_dec(v_val_3998_);
v___y_3979_ = v___y_3997_;
v___y_3980_ = v___y_3989_;
v___y_3981_ = v___y_3990_;
v___y_3982_ = v___y_3992_;
v___y_3983_ = v___y_3993_;
v___y_3984_ = v___y_3994_;
v___y_3985_ = v___y_3995_;
v___y_3986_ = v___y_3996_;
goto v___jp_3978_;
}
}
else
{
lean_dec(v___y_3991_);
v___y_3979_ = v___y_3997_;
v___y_3980_ = v___y_3989_;
v___y_3981_ = v___y_3990_;
v___y_3982_ = v___y_3992_;
v___y_3983_ = v___y_3993_;
v___y_3984_ = v___y_3994_;
v___y_3985_ = v___y_3995_;
v___y_3986_ = v___y_3996_;
goto v___jp_3978_;
}
}
v___jp_3999_:
{
lean_object* v___x_4008_; 
v___x_4008_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_val_3855_, v___y_4002_, v___y_4006_, v___y_4007_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; lean_object* v___x_4010_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v___x_4010_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_a_4009_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
if (lean_obj_tag(v___x_4010_) == 0)
{
if (lean_obj_tag(v_ids_x3f_4001_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4012_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v___x_4012_ = lean_box(0);
v___y_3989_ = v___y_4007_;
v___y_3990_ = v___y_4006_;
v___y_3991_ = v_m_x3f_4000_;
v___y_3992_ = v_a_4011_;
v___y_3993_ = v___y_4002_;
v___y_3994_ = v___y_4005_;
v___y_3995_ = v___y_4004_;
v___y_3996_ = v___y_4003_;
v___y_3997_ = v___x_4012_;
goto v___jp_3988_;
}
else
{
lean_object* v_a_4013_; lean_object* v_val_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4023_; 
v_a_4013_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4013_);
lean_dec_ref_known(v___x_4010_, 1);
v_val_4014_ = lean_ctor_get(v_ids_x3f_4001_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v_ids_x3f_4001_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4016_ = v_ids_x3f_4001_;
v_isShared_4017_ = v_isSharedCheck_4023_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_val_4014_);
lean_dec(v_ids_x3f_4001_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4023_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
size_t v_sz_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; 
v_sz_4018_ = lean_array_size(v_val_4014_);
v___x_4019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(v_sz_4018_, v___x_3852_, v_val_4014_);
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 0, v___x_4019_);
v___x_4021_ = v___x_4016_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v___x_4019_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
v___y_3989_ = v___y_4007_;
v___y_3990_ = v___y_4006_;
v___y_3991_ = v_m_x3f_4000_;
v___y_3992_ = v_a_4013_;
v___y_3993_ = v___y_4002_;
v___y_3994_ = v___y_4005_;
v___y_3995_ = v___y_4004_;
v___y_3996_ = v___y_4003_;
v___y_3997_ = v___x_4021_;
goto v___jp_3988_;
}
}
}
}
else
{
lean_object* v_a_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4031_; 
lean_dec_ref(v___y_4006_);
lean_dec(v_ids_x3f_4001_);
lean_dec(v_m_x3f_4000_);
lean_dec(v_stx_3820_);
v_a_4024_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4031_ == 0)
{
v___x_4026_ = v___x_4010_;
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_a_4024_);
lean_dec(v___x_4010_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4031_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
lean_object* v___x_4029_; 
if (v_isShared_4027_ == 0)
{
v___x_4029_ = v___x_4026_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_a_4024_);
v___x_4029_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
return v___x_4029_;
}
}
}
}
else
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4039_; 
lean_dec_ref(v___y_4006_);
lean_dec(v_ids_x3f_4001_);
lean_dec(v_m_x3f_4000_);
lean_dec(v_stx_3820_);
v_a_4032_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4039_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4039_ == 0)
{
v___x_4034_ = v___x_4008_;
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4008_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4039_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4037_; 
if (v_isShared_4035_ == 0)
{
v___x_4037_ = v___x_4034_;
goto v_reusejp_4036_;
}
else
{
lean_object* v_reuseFailAlloc_4038_; 
v_reuseFailAlloc_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4038_, 0, v_a_4032_);
v___x_4037_ = v_reuseFailAlloc_4038_;
goto v_reusejp_4036_;
}
v_reusejp_4036_:
{
return v___x_4037_;
}
}
}
}
v___jp_4042_:
{
lean_object* v___x_4050_; lean_object* v_ids_x3f_4051_; lean_object* v___x_4053_; 
v___x_4050_ = l_Lean_Syntax_getArg(v___x_4041_, v___x_3848_);
lean_dec(v___x_4041_);
v_ids_x3f_4051_ = l_Lean_Syntax_getArgs(v___x_4050_);
lean_dec(v___x_4050_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v_m_x3f_4043_);
v___x_4053_ = v___x_3857_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_m_x3f_4043_);
v___x_4053_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
lean_object* v___x_4054_; 
v___x_4054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4054_, 0, v_ids_x3f_4051_);
v_m_x3f_4000_ = v___x_4053_;
v_ids_x3f_4001_ = v___x_4054_;
v___y_4002_ = v___y_4044_;
v___y_4003_ = v___y_4045_;
v___y_4004_ = v___y_4046_;
v___y_4005_ = v___y_4047_;
v___y_4006_ = v___y_4048_;
v___y_4007_ = v___y_4049_;
goto v___jp_3999_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed(lean_object* v___x_4068_, lean_object* v_stx_4069_, lean_object* v___x_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
uint8_t v___x_10681__boxed_4078_; uint8_t v___x_10682__boxed_4079_; lean_object* v_res_4080_; 
v___x_10681__boxed_4078_ = lean_unbox(v___x_4068_);
v___x_10682__boxed_4079_ = lean_unbox(v___x_4070_);
v_res_4080_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(v___x_10681__boxed_4078_, v_stx_4069_, v___x_10682__boxed_4079_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(lean_object* v_stx_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_){
_start:
{
lean_object* v___x_4090_; uint8_t v___x_4091_; uint8_t v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___f_4095_; lean_object* v___x_4096_; 
v___x_4090_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1));
lean_inc(v_stx_4086_);
v___x_4091_ = l_Lean_Syntax_isOfKind(v_stx_4086_, v___x_4090_);
v___x_4092_ = 1;
v___x_4093_ = lean_box(v___x_4091_);
v___x_4094_ = lean_box(v___x_4092_);
v___f_4095_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4095_, 0, v___x_4093_);
lean_closure_set(v___f_4095_, 1, v_stx_4086_);
lean_closure_set(v___f_4095_, 2, v___x_4094_);
v___x_4096_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_4095_, v_a_4087_, v_a_4088_);
return v___x_4096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed(lean_object* v_stx_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(v_stx_4097_, v_a_4098_, v_a_4099_);
lean_dec(v_a_4099_);
lean_dec_ref(v_a_4098_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(uint8_t v___x_4102_, lean_object* v_as_4103_, size_t v_sz_4104_, size_t v_i_4105_, lean_object* v_b_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_){
_start:
{
lean_object* v___x_4114_; 
v___x_4114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v___x_4102_, v_as_4103_, v_sz_4104_, v_i_4105_, v_b_4106_);
return v___x_4114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___boxed(lean_object* v___x_4115_, lean_object* v_as_4116_, lean_object* v_sz_4117_, lean_object* v_i_4118_, lean_object* v_b_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
uint8_t v___x_11168__boxed_4127_; size_t v_sz_boxed_4128_; size_t v_i_boxed_4129_; lean_object* v_res_4130_; 
v___x_11168__boxed_4127_ = lean_unbox(v___x_4115_);
v_sz_boxed_4128_ = lean_unbox_usize(v_sz_4117_);
lean_dec(v_sz_4117_);
v_i_boxed_4129_ = lean_unbox_usize(v_i_4118_);
lean_dec(v_i_4118_);
v_res_4130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(v___x_11168__boxed_4127_, v_as_4116_, v_sz_boxed_4128_, v_i_boxed_4129_, v_b_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec_ref(v_as_4116_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(lean_object* v_n_4131_, lean_object* v_as_4132_, lean_object* v_lo_4133_, lean_object* v_hi_4134_, lean_object* v_w_4135_, lean_object* v_hlo_4136_, lean_object* v_hhi_4137_){
_start:
{
lean_object* v___x_4138_; 
v___x_4138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_4131_, v_as_4132_, v_lo_4133_, v_hi_4134_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___boxed(lean_object* v_n_4139_, lean_object* v_as_4140_, lean_object* v_lo_4141_, lean_object* v_hi_4142_, lean_object* v_w_4143_, lean_object* v_hlo_4144_, lean_object* v_hhi_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(v_n_4139_, v_as_4140_, v_lo_4141_, v_hi_4142_, v_w_4143_, v_hlo_4144_, v_hhi_4145_);
lean_dec(v_hi_4142_);
lean_dec(v_n_4139_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(lean_object* v_n_4147_, lean_object* v_lo_4148_, lean_object* v_hi_4149_, lean_object* v_hhi_4150_, lean_object* v_pivot_4151_, lean_object* v_as_4152_, lean_object* v_i_4153_, lean_object* v_k_4154_, lean_object* v_ilo_4155_, lean_object* v_ik_4156_, lean_object* v_w_4157_){
_start:
{
lean_object* v___x_4158_; 
v___x_4158_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_4149_, v_pivot_4151_, v_as_4152_, v_i_4153_, v_k_4154_);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___boxed(lean_object* v_n_4159_, lean_object* v_lo_4160_, lean_object* v_hi_4161_, lean_object* v_hhi_4162_, lean_object* v_pivot_4163_, lean_object* v_as_4164_, lean_object* v_i_4165_, lean_object* v_k_4166_, lean_object* v_ilo_4167_, lean_object* v_ik_4168_, lean_object* v_w_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(v_n_4159_, v_lo_4160_, v_hi_4161_, v_hhi_4162_, v_pivot_4163_, v_as_4164_, v_i_4165_, v_k_4166_, v_ilo_4167_, v_ik_4168_, v_w_4169_);
lean_dec(v_pivot_4163_);
lean_dec(v_hi_4161_);
lean_dec(v_lo_4160_);
lean_dec(v_n_4159_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(lean_object* v_ref_4171_, lean_object* v_msgData_4172_, uint8_t v_severity_4173_, uint8_t v_isSilent_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v___x_4182_; 
v___x_4182_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_4171_, v_msgData_4172_, v_severity_4173_, v_isSilent_4174_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
return v___x_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4183_, lean_object* v_msgData_4184_, lean_object* v_severity_4185_, lean_object* v_isSilent_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
uint8_t v_severity_boxed_4194_; uint8_t v_isSilent_boxed_4195_; lean_object* v_res_4196_; 
v_severity_boxed_4194_ = lean_unbox(v_severity_4185_);
v_isSilent_boxed_4195_ = lean_unbox(v_isSilent_4186_);
v_res_4196_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(v_ref_4183_, v_msgData_4184_, v_severity_boxed_4194_, v_isSilent_boxed_4195_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v___y_4188_);
lean_dec_ref(v___y_4187_);
lean_dec(v_ref_4183_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1(){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4202_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4203_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1));
v___x_4204_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1));
v___x_4205_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed), 4, 0);
v___x_4206_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4202_, v___x_4203_, v___x_4204_, v___x_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___boxed(lean_object* v_a_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1();
return v_res_4208_;
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
