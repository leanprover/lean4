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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
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
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` is already in the `#grind_lint` skip set"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` is already in the `#grind_lint` skip suffix set"};
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*14 + 40, .m_other = 14, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(10000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__21;
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0(void){
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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg(){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_266_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0);
v___x_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_267_, 0, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___boxed(lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(lean_object* v_00_u03b1_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___boxed(lean_object* v_00_u03b1_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(v_00_u03b1_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___lam__0(lean_object* v___x_280_, lean_object* v_a_281_, lean_object* v_s_282_){
_start:
{
lean_object* v_addEntryFn_283_; lean_object* v_importedEntries_284_; lean_object* v_state_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_293_; 
v_addEntryFn_283_ = lean_ctor_get(v___x_280_, 3);
lean_inc(v_addEntryFn_283_);
lean_dec_ref(v___x_280_);
v_importedEntries_284_ = lean_ctor_get(v_s_282_, 0);
v_state_285_ = lean_ctor_get(v_s_282_, 1);
v_isSharedCheck_293_ = !lean_is_exclusive(v_s_282_);
if (v_isSharedCheck_293_ == 0)
{
v___x_287_ = v_s_282_;
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_state_285_);
lean_inc(v_importedEntries_284_);
lean_dec(v_s_282_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_293_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v_state_289_; lean_object* v___x_291_; 
v_state_289_ = lean_apply_2(v_addEntryFn_283_, v_state_285_, v_a_281_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v_state_289_);
v___x_291_ = v___x_287_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v_importedEntries_284_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_state_289_);
v___x_291_ = v_reuseFailAlloc_292_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(lean_object* v_msgData_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; lean_object* v_env_301_; uint8_t v___x_302_; lean_object* v_env_303_; lean_object* v___x_304_; lean_object* v_toCold_305_; lean_object* v_mctx_306_; lean_object* v_lctx_307_; lean_object* v_options_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_300_ = lean_st_ref_get(v___y_298_);
v_env_301_ = lean_ctor_get(v___x_300_, 0);
lean_inc_ref(v_env_301_);
lean_dec(v___x_300_);
v___x_302_ = 0;
v_env_303_ = l_Lean_Environment_setRecordingDeps(v_env_301_, v___x_302_);
v___x_304_ = lean_st_ref_get(v___y_296_);
v_toCold_305_ = lean_ctor_get(v___y_297_, 0);
v_mctx_306_ = lean_ctor_get(v___x_304_, 0);
lean_inc_ref(v_mctx_306_);
lean_dec(v___x_304_);
v_lctx_307_ = lean_ctor_get(v___y_295_, 2);
v_options_308_ = lean_ctor_get(v_toCold_305_, 2);
lean_inc_ref(v_options_308_);
lean_inc_ref(v_lctx_307_);
v___x_309_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_309_, 0, v_env_303_);
lean_ctor_set(v___x_309_, 1, v_mctx_306_);
lean_ctor_set(v___x_309_, 2, v_lctx_307_);
lean_ctor_set(v___x_309_, 3, v_options_308_);
v___x_310_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
lean_ctor_set(v___x_310_, 1, v_msgData_294_);
v___x_311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___boxed(lean_object* v_msgData_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v_msgData_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
return v_res_318_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(lean_object* v_opts_319_, lean_object* v_opt_320_){
_start:
{
lean_object* v_name_321_; lean_object* v_defValue_322_; lean_object* v_map_323_; lean_object* v___x_324_; 
v_name_321_ = lean_ctor_get(v_opt_320_, 0);
v_defValue_322_ = lean_ctor_get(v_opt_320_, 1);
v_map_323_ = lean_ctor_get(v_opts_319_, 0);
v___x_324_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_323_, v_name_321_);
if (lean_obj_tag(v___x_324_) == 0)
{
uint8_t v___x_325_; 
v___x_325_ = lean_unbox(v_defValue_322_);
return v___x_325_;
}
else
{
lean_object* v_val_326_; 
v_val_326_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_val_326_);
lean_dec_ref_known(v___x_324_, 1);
if (lean_obj_tag(v_val_326_) == 1)
{
uint8_t v_v_327_; 
v_v_327_ = lean_ctor_get_uint8(v_val_326_, 0);
lean_dec_ref_known(v_val_326_, 0);
return v_v_327_;
}
else
{
uint8_t v___x_328_; 
lean_dec(v_val_326_);
v___x_328_ = lean_unbox(v_defValue_322_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_329_, lean_object* v_opt_330_){
_start:
{
uint8_t v_res_331_; lean_object* v_r_332_; 
v_res_331_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v_opts_329_, v_opt_330_);
lean_dec_ref(v_opt_330_);
lean_dec_ref(v_opts_329_);
v_r_332_ = lean_box(v_res_331_);
return v_r_332_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_333_ = lean_box(1);
v___x_334_ = l_Lean_MessageData_ofFormat(v___x_333_);
return v___x_334_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__2));
v___x_339_ = l_Lean_MessageData_ofFormat(v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4(lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
return v_x_340_;
}
else
{
lean_object* v_head_342_; lean_object* v_tail_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_365_; 
v_head_342_ = lean_ctor_get(v_x_341_, 0);
v_tail_343_ = lean_ctor_get(v_x_341_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_x_341_);
if (v_isSharedCheck_365_ == 0)
{
v___x_345_ = v_x_341_;
v_isShared_346_ = v_isSharedCheck_365_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_tail_343_);
lean_inc(v_head_342_);
lean_dec(v_x_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_365_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_before_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_363_; 
v_before_347_ = lean_ctor_get(v_head_342_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v_head_342_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; 
v_unused_364_ = lean_ctor_get(v_head_342_, 1);
lean_dec(v_unused_364_);
v___x_349_ = v_head_342_;
v_isShared_350_ = v_isSharedCheck_363_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_before_347_);
lean_dec(v_head_342_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_363_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_353_; 
v___x_351_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_350_ == 0)
{
lean_ctor_set_tag(v___x_349_, 7);
lean_ctor_set(v___x_349_, 1, v___x_351_);
lean_ctor_set(v___x_349_, 0, v_x_340_);
v___x_353_ = v___x_349_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_x_340_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_362_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3);
if (v_isShared_346_ == 0)
{
lean_ctor_set_tag(v___x_345_, 7);
lean_ctor_set(v___x_345_, 1, v___x_354_);
lean_ctor_set(v___x_345_, 0, v___x_353_);
v___x_356_ = v___x_345_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_353_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_354_);
v___x_356_ = v_reuseFailAlloc_361_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_357_ = l_Lean_MessageData_ofSyntax(v_before_347_);
v___x_358_ = l_Lean_indentD(v___x_357_);
v___x_359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_356_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v_x_340_ = v___x_359_;
v_x_341_ = v_tail_343_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__1));
v___x_370_ = l_Lean_MessageData_ofFormat(v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(lean_object* v_msgData_371_, lean_object* v_macroStack_372_, lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_373_);
v___x_376_ = l_Lean_Elab_pp_macroStack;
v___x_377_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v___x_375_, v___x_376_);
lean_dec_ref(v___x_375_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_dec(v_macroStack_372_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v_msgData_371_);
return v___x_378_;
}
else
{
if (lean_obj_tag(v_macroStack_372_) == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v_msgData_371_);
return v___x_379_;
}
else
{
lean_object* v_head_380_; lean_object* v_after_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_396_; 
v_head_380_ = lean_ctor_get(v_macroStack_372_, 0);
lean_inc(v_head_380_);
v_after_381_ = lean_ctor_get(v_head_380_, 1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_head_380_);
if (v_isSharedCheck_396_ == 0)
{
lean_object* v_unused_397_; 
v_unused_397_ = lean_ctor_get(v_head_380_, 0);
lean_dec(v_unused_397_);
v___x_383_ = v_head_380_;
v_isShared_384_ = v_isSharedCheck_396_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_after_381_);
lean_dec(v_head_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_396_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_385_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_384_ == 0)
{
lean_ctor_set_tag(v___x_383_, 7);
lean_ctor_set(v___x_383_, 1, v___x_385_);
lean_ctor_set(v___x_383_, 0, v_msgData_371_);
v___x_387_ = v___x_383_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_msgData_371_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v___x_385_);
v___x_387_ = v_reuseFailAlloc_395_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_msgData_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_388_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_MessageData_ofSyntax(v_after_381_);
v___x_391_ = l_Lean_indentD(v___x_390_);
v_msgData_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_392_, 0, v___x_389_);
lean_ctor_set(v_msgData_392_, 1, v___x_391_);
v___x_393_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4(v_msgData_392_, v_macroStack_372_);
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
return v___x_394_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_398_, lean_object* v_macroStack_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(v_msgData_398_, v_macroStack_399_, v___y_400_);
lean_dec_ref(v___y_400_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(lean_object* v_msg_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_){
_start:
{
lean_object* v_ref_411_; lean_object* v_macroStack_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_425_; 
v_ref_411_ = lean_ctor_get(v___y_408_, 2);
v_macroStack_412_ = lean_ctor_get(v___y_404_, 1);
v___x_413_ = l_Lean_Elab_getBetterRef(v_ref_411_, v_macroStack_412_);
v___x_414_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v_msg_403_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
v_a_415_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_a_415_);
lean_dec_ref(v___x_414_);
lean_inc(v_macroStack_412_);
v___x_416_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(v_a_415_, v_macroStack_412_, v___y_408_);
v_a_417_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_425_ == 0)
{
v___x_419_ = v___x_416_;
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_425_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_423_; 
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_413_);
lean_ctor_set(v___x_421_, 1, v_a_417_);
if (v_isShared_420_ == 0)
{
lean_ctor_set_tag(v___x_419_, 1);
lean_ctor_set(v___x_419_, 0, v___x_421_);
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg___boxed(lean_object* v_msg_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v_msg_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
return v_res_434_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0);
v___x_440_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
lean_ctor_set(v___x_440_, 2, v___x_439_);
lean_ctor_set(v___x_440_, 3, v___x_439_);
lean_ctor_set(v___x_440_, 4, v___x_439_);
lean_ctor_set(v___x_440_, 5, v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3));
v___x_443_ = l_Lean_stringToMessageData(v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(uint8_t v___x_444_, lean_object* v_as_445_, size_t v_sz_446_, size_t v_i_447_, lean_object* v_b_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = lean_usize_dec_lt(v_i_447_, v_sz_446_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_b_448_);
return v___x_457_;
}
else
{
lean_object* v___x_458_; lean_object* v___y_460_; lean_object* v_nextMacroScope_461_; lean_object* v_ngen_462_; lean_object* v_auxDeclNGen_463_; lean_object* v_traceState_464_; lean_object* v_recordedDeps_465_; lean_object* v_messages_466_; lean_object* v_infoState_467_; lean_object* v_snapshotTasks_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___x_492_; lean_object* v_a_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_458_ = lean_box(0);
v___x_492_ = lean_box(1);
v_a_493_ = lean_array_uget_borrowed(v_as_445_, v_i_447_);
v___x_494_ = lean_box(0);
lean_inc(v_a_493_);
v___x_495_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_493_, v___x_494_, v___y_453_, v___y_454_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v_a_496_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___x_519_; 
v_a_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc_n(v_a_496_, 2);
lean_dec_ref_known(v___x_495_, 1);
v___x_519_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_a_496_, v___y_453_, v___y_454_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v___x_520_; lean_object* v_env_521_; lean_object* v___x_522_; lean_object* v_toEnvExtension_523_; lean_object* v_asyncMode_524_; lean_object* v___x_525_; lean_object* v___x_526_; uint8_t v___x_527_; 
lean_dec_ref_known(v___x_519_, 1);
v___x_520_ = lean_st_ref_get(v___y_454_);
v_env_521_ = lean_ctor_get(v___x_520_, 0);
lean_inc_ref(v_env_521_);
lean_dec(v___x_520_);
v___x_522_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_523_ = lean_ctor_get(v___x_522_, 0);
v_asyncMode_524_ = lean_ctor_get(v_toEnvExtension_523_, 2);
v___x_525_ = lean_box(0);
v___x_526_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_492_, v___x_522_, v_env_521_, v_asyncMode_524_, v___x_525_);
v___x_527_ = l_Lean_NameSet_contains(v___x_526_, v_a_496_);
lean_dec(v___x_526_);
if (v___x_527_ == 0)
{
v___y_498_ = v___y_452_;
v___y_499_ = v___y_454_;
goto v___jp_497_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_528_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v_a_496_);
v___x_529_ = l_Lean_MessageData_ofName(v_a_496_);
v___x_530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4);
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_530_);
lean_ctor_set(v___x_532_, 1, v___x_531_);
v___x_533_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v___x_532_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_dec_ref_known(v___x_533_, 1);
v___y_498_ = v___y_452_;
v___y_499_ = v___y_454_;
goto v___jp_497_;
}
else
{
lean_dec(v_a_496_);
return v___x_533_;
}
}
}
else
{
lean_dec(v_a_496_);
return v___x_519_;
}
v___jp_497_:
{
lean_object* v___x_500_; lean_object* v_env_501_; lean_object* v_nextMacroScope_502_; lean_object* v_ngen_503_; lean_object* v_auxDeclNGen_504_; lean_object* v_traceState_505_; lean_object* v_recordedDeps_506_; lean_object* v_messages_507_; lean_object* v_infoState_508_; lean_object* v_snapshotTasks_509_; lean_object* v___x_510_; lean_object* v_toEnvExtension_511_; lean_object* v_asyncMode_512_; uint8_t v_logWrites_513_; lean_object* v___f_514_; lean_object* v___x_515_; 
v___x_500_ = lean_st_ref_take(v___y_499_);
v_env_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc_ref(v_env_501_);
v_nextMacroScope_502_ = lean_ctor_get(v___x_500_, 1);
lean_inc(v_nextMacroScope_502_);
v_ngen_503_ = lean_ctor_get(v___x_500_, 2);
lean_inc_ref(v_ngen_503_);
v_auxDeclNGen_504_ = lean_ctor_get(v___x_500_, 3);
lean_inc_ref(v_auxDeclNGen_504_);
v_traceState_505_ = lean_ctor_get(v___x_500_, 4);
lean_inc_ref(v_traceState_505_);
v_recordedDeps_506_ = lean_ctor_get(v___x_500_, 6);
lean_inc_ref(v_recordedDeps_506_);
v_messages_507_ = lean_ctor_get(v___x_500_, 7);
lean_inc_ref(v_messages_507_);
v_infoState_508_ = lean_ctor_get(v___x_500_, 8);
lean_inc_ref(v_infoState_508_);
v_snapshotTasks_509_ = lean_ctor_get(v___x_500_, 9);
lean_inc_ref(v_snapshotTasks_509_);
lean_dec(v___x_500_);
v___x_510_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_511_ = lean_ctor_get(v___x_510_, 0);
v_asyncMode_512_ = lean_ctor_get(v_toEnvExtension_511_, 2);
v_logWrites_513_ = lean_ctor_get_uint8(v_toEnvExtension_511_, sizeof(void*)*6);
v___f_514_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_514_, 0, v___x_510_);
lean_closure_set(v___f_514_, 1, v_a_496_);
v___x_515_ = lean_box(0);
if (v_logWrites_513_ == 0)
{
lean_object* v___x_516_; 
lean_inc_ref(v_toEnvExtension_511_);
v___x_516_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_511_, v_env_501_, v___f_514_, v_asyncMode_512_, v___x_515_, v___x_444_);
v___y_460_ = v___y_499_;
v_nextMacroScope_461_ = v_nextMacroScope_502_;
v_ngen_462_ = v_ngen_503_;
v_auxDeclNGen_463_ = v_auxDeclNGen_504_;
v_traceState_464_ = v_traceState_505_;
v_recordedDeps_465_ = v_recordedDeps_506_;
v_messages_466_ = v_messages_507_;
v_infoState_467_ = v_infoState_508_;
v_snapshotTasks_468_ = v_snapshotTasks_509_;
v___y_469_ = v___y_498_;
v___y_470_ = v___x_516_;
goto v___jp_459_;
}
else
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_inc_ref_n(v_toEnvExtension_511_, 2);
v___x_517_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_511_, v_env_501_);
lean_dec_ref(v_env_501_);
v___x_518_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_511_, v___x_517_, v___f_514_, v_asyncMode_512_, v___x_515_, v___x_444_);
v___y_460_ = v___y_499_;
v_nextMacroScope_461_ = v_nextMacroScope_502_;
v_ngen_462_ = v_ngen_503_;
v_auxDeclNGen_463_ = v_auxDeclNGen_504_;
v_traceState_464_ = v_traceState_505_;
v_recordedDeps_465_ = v_recordedDeps_506_;
v_messages_466_ = v_messages_507_;
v_infoState_467_ = v_infoState_508_;
v_snapshotTasks_468_ = v_snapshotTasks_509_;
v___y_469_ = v___y_498_;
v___y_470_ = v___x_518_;
goto v___jp_459_;
}
}
}
else
{
lean_object* v_a_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_541_; 
v_a_534_ = lean_ctor_get(v___x_495_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_495_);
if (v_isSharedCheck_541_ == 0)
{
v___x_536_ = v___x_495_;
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_a_534_);
lean_dec(v___x_495_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_541_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_539_; 
if (v_isShared_537_ == 0)
{
v___x_539_ = v___x_536_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
v___jp_459_:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_mctx_475_; lean_object* v_zetaDeltaFVarIds_476_; lean_object* v_postponed_477_; lean_object* v_diag_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_490_; 
v___x_471_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1);
v___x_472_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_472_, 0, v___y_470_);
lean_ctor_set(v___x_472_, 1, v_nextMacroScope_461_);
lean_ctor_set(v___x_472_, 2, v_ngen_462_);
lean_ctor_set(v___x_472_, 3, v_auxDeclNGen_463_);
lean_ctor_set(v___x_472_, 4, v_traceState_464_);
lean_ctor_set(v___x_472_, 5, v___x_471_);
lean_ctor_set(v___x_472_, 6, v_recordedDeps_465_);
lean_ctor_set(v___x_472_, 7, v_messages_466_);
lean_ctor_set(v___x_472_, 8, v_infoState_467_);
lean_ctor_set(v___x_472_, 9, v_snapshotTasks_468_);
v___x_473_ = lean_st_ref_put(v___y_460_, v___x_472_);
v___x_474_ = lean_st_ref_take(v___y_469_);
v_mctx_475_ = lean_ctor_get(v___x_474_, 0);
v_zetaDeltaFVarIds_476_ = lean_ctor_get(v___x_474_, 2);
v_postponed_477_ = lean_ctor_get(v___x_474_, 3);
v_diag_478_ = lean_ctor_get(v___x_474_, 4);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_490_ == 0)
{
lean_object* v_unused_491_; 
v_unused_491_ = lean_ctor_get(v___x_474_, 1);
lean_dec(v_unused_491_);
v___x_480_ = v___x_474_;
v_isShared_481_ = v_isSharedCheck_490_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_diag_478_);
lean_inc(v_postponed_477_);
lean_inc(v_zetaDeltaFVarIds_476_);
lean_inc(v_mctx_475_);
lean_dec(v___x_474_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_490_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_482_);
v___x_484_ = v___x_480_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_mctx_475_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_489_, 2, v_zetaDeltaFVarIds_476_);
lean_ctor_set(v_reuseFailAlloc_489_, 3, v_postponed_477_);
lean_ctor_set(v_reuseFailAlloc_489_, 4, v_diag_478_);
v___x_484_ = v_reuseFailAlloc_489_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_485_; size_t v___x_486_; size_t v___x_487_; 
v___x_485_ = lean_st_ref_put(v___y_469_, v___x_484_);
v___x_486_ = ((size_t)1ULL);
v___x_487_ = lean_usize_add(v_i_447_, v___x_486_);
v_i_447_ = v___x_487_;
v_b_448_ = v___x_458_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___boxed(lean_object* v___x_542_, lean_object* v_as_543_, lean_object* v_sz_544_, lean_object* v_i_545_, lean_object* v_b_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v___x_7788__boxed_554_; size_t v_sz_boxed_555_; size_t v_i_boxed_556_; lean_object* v_res_557_; 
v___x_7788__boxed_554_ = lean_unbox(v___x_542_);
v_sz_boxed_555_ = lean_unbox_usize(v_sz_544_);
lean_dec(v_sz_544_);
v_i_boxed_556_ = lean_unbox_usize(v_i_545_);
lean_dec(v_i_545_);
v_res_557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(v___x_7788__boxed_554_, v_as_543_, v_sz_boxed_555_, v_i_boxed_556_, v_b_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec_ref(v_as_543_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___lam__0(lean_object* v___x_558_, lean_object* v___x_559_, lean_object* v_s_560_){
_start:
{
lean_object* v_addEntryFn_561_; lean_object* v_importedEntries_562_; lean_object* v_state_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_571_; 
v_addEntryFn_561_ = lean_ctor_get(v___x_558_, 3);
lean_inc(v_addEntryFn_561_);
lean_dec_ref(v___x_558_);
v_importedEntries_562_ = lean_ctor_get(v_s_560_, 0);
v_state_563_ = lean_ctor_get(v_s_560_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_s_560_);
if (v_isSharedCheck_571_ == 0)
{
v___x_565_ = v_s_560_;
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_state_563_);
lean_inc(v_importedEntries_562_);
lean_dec(v_s_560_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_571_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v_state_567_; lean_object* v___x_569_; 
v_state_567_ = lean_apply_2(v_addEntryFn_561_, v_state_563_, v___x_559_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_state_567_);
v___x_569_ = v___x_565_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_importedEntries_562_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_state_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(uint8_t v___y_575_, lean_object* v_as_576_, size_t v_sz_577_, size_t v_i_578_, lean_object* v_b_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
uint8_t v___x_587_; 
v___x_587_ = lean_usize_dec_lt(v_i_578_, v_sz_577_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v_b_579_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v_nextMacroScope_593_; lean_object* v_ngen_594_; lean_object* v_auxDeclNGen_595_; lean_object* v_traceState_596_; lean_object* v_recordedDeps_597_; lean_object* v_messages_598_; lean_object* v_infoState_599_; lean_object* v_snapshotTasks_600_; lean_object* v___y_601_; lean_object* v___x_623_; lean_object* v_a_624_; lean_object* v___x_625_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___x_648_; lean_object* v_env_649_; lean_object* v___x_650_; lean_object* v_toEnvExtension_651_; lean_object* v_asyncMode_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v___x_589_ = lean_box(0);
v___x_623_ = lean_box(1);
v_a_624_ = lean_array_uget_borrowed(v_as_576_, v_i_578_);
v___x_625_ = l_Lean_TSyntax_getId(v_a_624_);
v___x_648_ = lean_st_ref_get(v___y_585_);
v_env_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc_ref(v_env_649_);
lean_dec(v___x_648_);
v___x_650_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_651_ = lean_ctor_get(v___x_650_, 0);
v_asyncMode_652_ = lean_ctor_get(v_toEnvExtension_651_, 2);
v___x_653_ = lean_box(0);
v___x_654_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_623_, v___x_650_, v_env_649_, v_asyncMode_652_, v___x_653_);
v___x_655_ = l_Lean_NameSet_contains(v___x_654_, v___x_625_);
lean_dec(v___x_654_);
if (v___x_655_ == 0)
{
v___y_627_ = v___y_583_;
v___y_628_ = v___y_585_;
goto v___jp_626_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_656_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v___x_625_);
v___x_657_ = l_Lean_MessageData_ofName(v___x_625_);
v___x_658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1);
v___x_660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
v___x_661_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v___x_660_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_dec_ref_known(v___x_661_, 1);
v___y_627_ = v___y_583_;
v___y_628_ = v___y_585_;
goto v___jp_626_;
}
else
{
lean_dec(v___x_625_);
return v___x_661_;
}
}
v___jp_590_:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_mctx_606_; lean_object* v_zetaDeltaFVarIds_607_; lean_object* v_postponed_608_; lean_object* v_diag_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_621_; 
v___x_602_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1);
v___x_603_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_603_, 0, v___y_601_);
lean_ctor_set(v___x_603_, 1, v_nextMacroScope_593_);
lean_ctor_set(v___x_603_, 2, v_ngen_594_);
lean_ctor_set(v___x_603_, 3, v_auxDeclNGen_595_);
lean_ctor_set(v___x_603_, 4, v_traceState_596_);
lean_ctor_set(v___x_603_, 5, v___x_602_);
lean_ctor_set(v___x_603_, 6, v_recordedDeps_597_);
lean_ctor_set(v___x_603_, 7, v_messages_598_);
lean_ctor_set(v___x_603_, 8, v_infoState_599_);
lean_ctor_set(v___x_603_, 9, v_snapshotTasks_600_);
v___x_604_ = lean_st_ref_put(v___y_591_, v___x_603_);
v___x_605_ = lean_st_ref_take(v___y_592_);
v_mctx_606_ = lean_ctor_get(v___x_605_, 0);
v_zetaDeltaFVarIds_607_ = lean_ctor_get(v___x_605_, 2);
v_postponed_608_ = lean_ctor_get(v___x_605_, 3);
v_diag_609_ = lean_ctor_get(v___x_605_, 4);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v___x_605_, 1);
lean_dec(v_unused_622_);
v___x_611_ = v___x_605_;
v_isShared_612_ = v_isSharedCheck_621_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_diag_609_);
lean_inc(v_postponed_608_);
lean_inc(v_zetaDeltaFVarIds_607_);
lean_inc(v_mctx_606_);
lean_dec(v___x_605_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_621_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2);
if (v_isShared_612_ == 0)
{
lean_ctor_set(v___x_611_, 1, v___x_613_);
v___x_615_ = v___x_611_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_mctx_606_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_zetaDeltaFVarIds_607_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_postponed_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v_diag_609_);
v___x_615_ = v_reuseFailAlloc_620_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; size_t v___x_617_; size_t v___x_618_; 
v___x_616_ = lean_st_ref_put(v___y_592_, v___x_615_);
v___x_617_ = ((size_t)1ULL);
v___x_618_ = lean_usize_add(v_i_578_, v___x_617_);
v_i_578_ = v___x_618_;
v_b_579_ = v___x_589_;
goto _start;
}
}
}
v___jp_626_:
{
lean_object* v___x_629_; lean_object* v_env_630_; lean_object* v_nextMacroScope_631_; lean_object* v_ngen_632_; lean_object* v_auxDeclNGen_633_; lean_object* v_traceState_634_; lean_object* v_recordedDeps_635_; lean_object* v_messages_636_; lean_object* v_infoState_637_; lean_object* v_snapshotTasks_638_; lean_object* v___x_639_; lean_object* v_toEnvExtension_640_; lean_object* v_asyncMode_641_; uint8_t v_logWrites_642_; lean_object* v___f_643_; lean_object* v___x_644_; 
v___x_629_ = lean_st_ref_take(v___y_628_);
v_env_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc_ref(v_env_630_);
v_nextMacroScope_631_ = lean_ctor_get(v___x_629_, 1);
lean_inc(v_nextMacroScope_631_);
v_ngen_632_ = lean_ctor_get(v___x_629_, 2);
lean_inc_ref(v_ngen_632_);
v_auxDeclNGen_633_ = lean_ctor_get(v___x_629_, 3);
lean_inc_ref(v_auxDeclNGen_633_);
v_traceState_634_ = lean_ctor_get(v___x_629_, 4);
lean_inc_ref(v_traceState_634_);
v_recordedDeps_635_ = lean_ctor_get(v___x_629_, 6);
lean_inc_ref(v_recordedDeps_635_);
v_messages_636_ = lean_ctor_get(v___x_629_, 7);
lean_inc_ref(v_messages_636_);
v_infoState_637_ = lean_ctor_get(v___x_629_, 8);
lean_inc_ref(v_infoState_637_);
v_snapshotTasks_638_ = lean_ctor_get(v___x_629_, 9);
lean_inc_ref(v_snapshotTasks_638_);
lean_dec(v___x_629_);
v___x_639_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_640_ = lean_ctor_get(v___x_639_, 0);
v_asyncMode_641_ = lean_ctor_get(v_toEnvExtension_640_, 2);
v_logWrites_642_ = lean_ctor_get_uint8(v_toEnvExtension_640_, sizeof(void*)*6);
v___f_643_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___lam__0), 3, 2);
lean_closure_set(v___f_643_, 0, v___x_639_);
lean_closure_set(v___f_643_, 1, v___x_625_);
v___x_644_ = lean_box(0);
if (v_logWrites_642_ == 0)
{
lean_object* v___x_645_; 
lean_inc_ref(v_toEnvExtension_640_);
v___x_645_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_640_, v_env_630_, v___f_643_, v_asyncMode_641_, v___x_644_, v___y_575_);
v___y_591_ = v___y_628_;
v___y_592_ = v___y_627_;
v_nextMacroScope_593_ = v_nextMacroScope_631_;
v_ngen_594_ = v_ngen_632_;
v_auxDeclNGen_595_ = v_auxDeclNGen_633_;
v_traceState_596_ = v_traceState_634_;
v_recordedDeps_597_ = v_recordedDeps_635_;
v_messages_598_ = v_messages_636_;
v_infoState_599_ = v_infoState_637_;
v_snapshotTasks_600_ = v_snapshotTasks_638_;
v___y_601_ = v___x_645_;
goto v___jp_590_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_inc_ref_n(v_toEnvExtension_640_, 2);
v___x_646_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_640_, v_env_630_);
lean_dec_ref(v_env_630_);
v___x_647_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_640_, v___x_646_, v___f_643_, v_asyncMode_641_, v___x_644_, v___y_575_);
v___y_591_ = v___y_628_;
v___y_592_ = v___y_627_;
v_nextMacroScope_593_ = v_nextMacroScope_631_;
v_ngen_594_ = v_ngen_632_;
v_auxDeclNGen_595_ = v_auxDeclNGen_633_;
v_traceState_596_ = v_traceState_634_;
v_recordedDeps_597_ = v_recordedDeps_635_;
v_messages_598_ = v_messages_636_;
v_infoState_599_ = v_infoState_637_;
v_snapshotTasks_600_ = v_snapshotTasks_638_;
v___y_601_ = v___x_647_;
goto v___jp_590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___boxed(lean_object* v___y_662_, lean_object* v_as_663_, lean_object* v_sz_664_, lean_object* v_i_665_, lean_object* v_b_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
uint8_t v___y_7981__boxed_674_; size_t v_sz_boxed_675_; size_t v_i_boxed_676_; lean_object* v_res_677_; 
v___y_7981__boxed_674_ = lean_unbox(v___y_662_);
v_sz_boxed_675_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v_i_boxed_676_ = lean_unbox_usize(v_i_665_);
lean_dec(v_i_665_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(v___y_7981__boxed_674_, v_as_663_, v_sz_boxed_675_, v_i_boxed_676_, v_b_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec_ref(v_as_663_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(uint8_t v___y_678_, lean_object* v_ids_679_, uint8_t v___x_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
if (v___y_678_ == 0)
{
lean_object* v___x_688_; size_t v_sz_689_; size_t v___x_690_; lean_object* v___x_691_; 
v___x_688_ = lean_box(0);
v_sz_689_ = lean_array_size(v_ids_679_);
v___x_690_ = ((size_t)0ULL);
v___x_691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(v___x_680_, v_ids_679_, v_sz_689_, v___x_690_, v___x_688_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_698_ == 0)
{
lean_object* v_unused_699_; 
v_unused_699_ = lean_ctor_get(v___x_691_, 0);
lean_dec(v_unused_699_);
v___x_693_ = v___x_691_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_dec(v___x_691_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_688_);
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_688_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
else
{
return v___x_691_;
}
}
else
{
lean_object* v___x_700_; size_t v_sz_701_; size_t v___x_702_; lean_object* v___x_703_; 
v___x_700_ = lean_box(0);
v_sz_701_ = lean_array_size(v_ids_679_);
v___x_702_ = ((size_t)0ULL);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(v___y_678_, v_ids_679_, v_sz_701_, v___x_702_, v___x_700_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v___x_703_, 0);
lean_dec(v_unused_711_);
v___x_705_ = v___x_703_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_dec(v___x_703_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v___x_700_);
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_700_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed(lean_object* v___y_712_, lean_object* v_ids_713_, lean_object* v___x_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
uint8_t v___y_8104__boxed_722_; uint8_t v___x_8105__boxed_723_; lean_object* v_res_724_; 
v___y_8104__boxed_722_ = lean_unbox(v___y_712_);
v___x_8105__boxed_723_ = lean_unbox(v___x_714_);
v_res_724_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(v___y_8104__boxed_722_, v_ids_713_, v___x_8105__boxed_723_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec_ref(v_ids_713_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(lean_object* v_stx_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_734_; uint8_t v___x_735_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; uint8_t v___y_740_; lean_object* v_sfx_x3f_746_; lean_object* v___y_747_; lean_object* v___y_748_; 
v___x_734_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1));
lean_inc(v_stx_730_);
v___x_735_ = l_Lean_Syntax_isOfKind(v_stx_730_, v___x_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_753_; 
lean_dec(v_stx_730_);
v___x_753_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
return v___x_753_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = lean_unsigned_to_nat(2u);
v___x_755_ = l_Lean_Syntax_getArg(v_stx_730_, v___x_754_);
v___x_756_ = l_Lean_Syntax_isNone(v___x_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_755_);
v___x_758_ = l_Lean_Syntax_matchesNull(v___x_755_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; 
lean_dec(v___x_755_);
lean_dec(v_stx_730_);
v___x_759_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
return v___x_759_;
}
else
{
lean_object* v___x_760_; lean_object* v_sfx_x3f_761_; lean_object* v___x_762_; 
v___x_760_ = lean_unsigned_to_nat(0u);
v_sfx_x3f_761_ = l_Lean_Syntax_getArg(v___x_755_, v___x_760_);
lean_dec(v___x_755_);
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v_sfx_x3f_761_);
v_sfx_x3f_746_ = v___x_762_;
v___y_747_ = v_a_731_;
v___y_748_ = v_a_732_;
goto v___jp_745_;
}
}
else
{
lean_object* v___x_763_; 
lean_dec(v___x_755_);
v___x_763_ = lean_box(0);
v_sfx_x3f_746_ = v___x_763_;
v___y_747_ = v_a_731_;
v___y_748_ = v_a_732_;
goto v___jp_745_;
}
}
v___jp_736_:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___y_743_; lean_object* v___x_744_; 
v___x_741_ = lean_box(v___y_740_);
v___x_742_ = lean_box(v___x_735_);
v___y_743_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed), 10, 3);
lean_closure_set(v___y_743_, 0, v___x_741_);
lean_closure_set(v___y_743_, 1, v___y_738_);
lean_closure_set(v___y_743_, 2, v___x_742_);
v___x_744_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_743_, v___y_739_, v___y_737_);
return v___x_744_;
}
v___jp_745_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_ids_751_; 
v___x_749_ = lean_unsigned_to_nat(3u);
v___x_750_ = l_Lean_Syntax_getArg(v_stx_730_, v___x_749_);
lean_dec(v_stx_730_);
v_ids_751_ = l_Lean_Syntax_getArgs(v___x_750_);
lean_dec(v___x_750_);
if (lean_obj_tag(v_sfx_x3f_746_) == 0)
{
uint8_t v___x_752_; 
v___x_752_ = 0;
v___y_737_ = v___y_748_;
v___y_738_ = v_ids_751_;
v___y_739_ = v___y_747_;
v___y_740_ = v___x_752_;
goto v___jp_736_;
}
else
{
lean_dec_ref_known(v_sfx_x3f_746_, 1);
v___y_737_ = v___y_748_;
v___y_738_ = v_ids_751_;
v___y_739_ = v___y_747_;
v___y_740_ = v___x_735_;
goto v___jp_736_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed(lean_object* v_stx_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(v_stx_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0(lean_object* v_00_u03b1_769_, lean_object* v_msg_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v_msg_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___boxed(lean_object* v_00_u03b1_779_, lean_object* v_msg_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0(v_00_u03b1_779_, v_msg_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
lean_dec(v___y_786_);
lean_dec_ref(v___y_785_);
lean_dec(v___y_784_);
lean_dec_ref(v___y_783_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1(lean_object* v_msgData_789_, lean_object* v_macroStack_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(v_msgData_789_, v_macroStack_790_, v___y_795_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___boxed(lean_object* v_msgData_799_, lean_object* v_macroStack_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1(v_msgData_799_, v_macroStack_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
lean_dec(v___y_806_);
lean_dec_ref(v___y_805_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1(){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_814_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_815_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1));
v___x_816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1));
v___x_817_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed), 4, 0);
v___x_818_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_814_, v___x_815_, v___x_816_, v___x_817_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___boxed(lean_object* v_a_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1();
return v_res_820_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0));
v___x_823_ = l_Lean_stringToMessageData(v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(uint8_t v___x_824_, lean_object* v_as_825_, size_t v_sz_826_, size_t v_i_827_, lean_object* v_b_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v___x_836_; 
v___x_836_ = lean_usize_dec_lt(v_i_827_, v_sz_826_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; 
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v_b_828_);
return v___x_837_;
}
else
{
lean_object* v___x_838_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v_nextMacroScope_842_; lean_object* v_ngen_843_; lean_object* v_auxDeclNGen_844_; lean_object* v_traceState_845_; lean_object* v_recordedDeps_846_; lean_object* v_messages_847_; lean_object* v_infoState_848_; lean_object* v_snapshotTasks_849_; lean_object* v___y_850_; lean_object* v___x_872_; lean_object* v_a_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v___x_838_ = lean_box(0);
v___x_872_ = lean_box(1);
v_a_873_ = lean_array_uget_borrowed(v_as_825_, v_i_827_);
v___x_874_ = lean_box(0);
lean_inc(v_a_873_);
v___x_875_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_873_, v___x_874_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___x_899_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc_n(v_a_876_, 2);
lean_dec_ref_known(v___x_875_, 1);
v___x_899_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_a_876_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_900_; lean_object* v_env_901_; lean_object* v___x_902_; lean_object* v_toEnvExtension_903_; lean_object* v_asyncMode_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; 
lean_dec_ref_known(v___x_899_, 1);
v___x_900_ = lean_st_ref_get(v___y_834_);
v_env_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc_ref(v_env_901_);
lean_dec(v___x_900_);
v___x_902_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_903_ = lean_ctor_get(v___x_902_, 0);
v_asyncMode_904_ = lean_ctor_get(v_toEnvExtension_903_, 2);
v___x_905_ = lean_box(0);
v___x_906_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_872_, v___x_902_, v_env_901_, v_asyncMode_904_, v___x_905_);
v___x_907_ = l_Lean_NameSet_contains(v___x_906_, v_a_876_);
lean_dec(v___x_906_);
if (v___x_907_ == 0)
{
v___y_878_ = v___y_832_;
v___y_879_ = v___y_834_;
goto v___jp_877_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_908_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v_a_876_);
v___x_909_ = l_Lean_MessageData_ofName(v_a_876_);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_908_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1);
v___x_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v___x_912_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_dec_ref_known(v___x_913_, 1);
v___y_878_ = v___y_832_;
v___y_879_ = v___y_834_;
goto v___jp_877_;
}
else
{
lean_dec(v_a_876_);
return v___x_913_;
}
}
}
else
{
lean_dec(v_a_876_);
return v___x_899_;
}
v___jp_877_:
{
lean_object* v___x_880_; lean_object* v_env_881_; lean_object* v_nextMacroScope_882_; lean_object* v_ngen_883_; lean_object* v_auxDeclNGen_884_; lean_object* v_traceState_885_; lean_object* v_recordedDeps_886_; lean_object* v_messages_887_; lean_object* v_infoState_888_; lean_object* v_snapshotTasks_889_; lean_object* v___x_890_; lean_object* v_toEnvExtension_891_; lean_object* v_asyncMode_892_; uint8_t v_logWrites_893_; lean_object* v___f_894_; lean_object* v___x_895_; 
v___x_880_ = lean_st_ref_take(v___y_879_);
v_env_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc_ref(v_env_881_);
v_nextMacroScope_882_ = lean_ctor_get(v___x_880_, 1);
lean_inc(v_nextMacroScope_882_);
v_ngen_883_ = lean_ctor_get(v___x_880_, 2);
lean_inc_ref(v_ngen_883_);
v_auxDeclNGen_884_ = lean_ctor_get(v___x_880_, 3);
lean_inc_ref(v_auxDeclNGen_884_);
v_traceState_885_ = lean_ctor_get(v___x_880_, 4);
lean_inc_ref(v_traceState_885_);
v_recordedDeps_886_ = lean_ctor_get(v___x_880_, 6);
lean_inc_ref(v_recordedDeps_886_);
v_messages_887_ = lean_ctor_get(v___x_880_, 7);
lean_inc_ref(v_messages_887_);
v_infoState_888_ = lean_ctor_get(v___x_880_, 8);
lean_inc_ref(v_infoState_888_);
v_snapshotTasks_889_ = lean_ctor_get(v___x_880_, 9);
lean_inc_ref(v_snapshotTasks_889_);
lean_dec(v___x_880_);
v___x_890_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_891_ = lean_ctor_get(v___x_890_, 0);
v_asyncMode_892_ = lean_ctor_get(v_toEnvExtension_891_, 2);
v_logWrites_893_ = lean_ctor_get_uint8(v_toEnvExtension_891_, sizeof(void*)*6);
v___f_894_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___lam__0), 3, 2);
lean_closure_set(v___f_894_, 0, v___x_890_);
lean_closure_set(v___f_894_, 1, v_a_876_);
v___x_895_ = lean_box(0);
if (v_logWrites_893_ == 0)
{
lean_object* v___x_896_; 
lean_inc_ref(v_toEnvExtension_891_);
v___x_896_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_891_, v_env_881_, v___f_894_, v_asyncMode_892_, v___x_895_, v___x_824_);
v___y_840_ = v___y_879_;
v___y_841_ = v___y_878_;
v_nextMacroScope_842_ = v_nextMacroScope_882_;
v_ngen_843_ = v_ngen_883_;
v_auxDeclNGen_844_ = v_auxDeclNGen_884_;
v_traceState_845_ = v_traceState_885_;
v_recordedDeps_846_ = v_recordedDeps_886_;
v_messages_847_ = v_messages_887_;
v_infoState_848_ = v_infoState_888_;
v_snapshotTasks_849_ = v_snapshotTasks_889_;
v___y_850_ = v___x_896_;
goto v___jp_839_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_inc_ref_n(v_toEnvExtension_891_, 2);
v___x_897_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_891_, v_env_881_);
lean_dec_ref(v_env_881_);
v___x_898_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_891_, v___x_897_, v___f_894_, v_asyncMode_892_, v___x_895_, v___x_824_);
v___y_840_ = v___y_879_;
v___y_841_ = v___y_878_;
v_nextMacroScope_842_ = v_nextMacroScope_882_;
v_ngen_843_ = v_ngen_883_;
v_auxDeclNGen_844_ = v_auxDeclNGen_884_;
v_traceState_845_ = v_traceState_885_;
v_recordedDeps_846_ = v_recordedDeps_886_;
v_messages_847_ = v_messages_887_;
v_infoState_848_ = v_infoState_888_;
v_snapshotTasks_849_ = v_snapshotTasks_889_;
v___y_850_ = v___x_898_;
goto v___jp_839_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
v_a_914_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_875_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_875_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
v___jp_839_:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v_mctx_855_; lean_object* v_zetaDeltaFVarIds_856_; lean_object* v_postponed_857_; lean_object* v_diag_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_870_; 
v___x_851_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1);
v___x_852_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_852_, 0, v___y_850_);
lean_ctor_set(v___x_852_, 1, v_nextMacroScope_842_);
lean_ctor_set(v___x_852_, 2, v_ngen_843_);
lean_ctor_set(v___x_852_, 3, v_auxDeclNGen_844_);
lean_ctor_set(v___x_852_, 4, v_traceState_845_);
lean_ctor_set(v___x_852_, 5, v___x_851_);
lean_ctor_set(v___x_852_, 6, v_recordedDeps_846_);
lean_ctor_set(v___x_852_, 7, v_messages_847_);
lean_ctor_set(v___x_852_, 8, v_infoState_848_);
lean_ctor_set(v___x_852_, 9, v_snapshotTasks_849_);
v___x_853_ = lean_st_ref_put(v___y_840_, v___x_852_);
v___x_854_ = lean_st_ref_take(v___y_841_);
v_mctx_855_ = lean_ctor_get(v___x_854_, 0);
v_zetaDeltaFVarIds_856_ = lean_ctor_get(v___x_854_, 2);
v_postponed_857_ = lean_ctor_get(v___x_854_, 3);
v_diag_858_ = lean_ctor_get(v___x_854_, 4);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_870_ == 0)
{
lean_object* v_unused_871_; 
v_unused_871_ = lean_ctor_get(v___x_854_, 1);
lean_dec(v_unused_871_);
v___x_860_ = v___x_854_;
v_isShared_861_ = v_isSharedCheck_870_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_diag_858_);
lean_inc(v_postponed_857_);
lean_inc(v_zetaDeltaFVarIds_856_);
lean_inc(v_mctx_855_);
lean_dec(v___x_854_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_870_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 1, v___x_862_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_mctx_855_);
lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_869_, 2, v_zetaDeltaFVarIds_856_);
lean_ctor_set(v_reuseFailAlloc_869_, 3, v_postponed_857_);
lean_ctor_set(v_reuseFailAlloc_869_, 4, v_diag_858_);
v___x_864_ = v_reuseFailAlloc_869_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; size_t v___x_866_; size_t v___x_867_; 
v___x_865_ = lean_st_ref_put(v___y_841_, v___x_864_);
v___x_866_ = ((size_t)1ULL);
v___x_867_ = lean_usize_add(v_i_827_, v___x_866_);
v_i_827_ = v___x_867_;
v_b_828_ = v___x_838_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___boxed(lean_object* v___x_922_, lean_object* v_as_923_, lean_object* v_sz_924_, lean_object* v_i_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
uint8_t v___x_3241__boxed_934_; size_t v_sz_boxed_935_; size_t v_i_boxed_936_; lean_object* v_res_937_; 
v___x_3241__boxed_934_ = lean_unbox(v___x_922_);
v_sz_boxed_935_ = lean_unbox_usize(v_sz_924_);
lean_dec(v_sz_924_);
v_i_boxed_936_ = lean_unbox_usize(v_i_925_);
lean_dec(v_i_925_);
v_res_937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(v___x_3241__boxed_934_, v_as_923_, v_sz_boxed_935_, v_i_boxed_936_, v_b_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec_ref(v_as_923_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(uint8_t v___x_938_, lean_object* v_ids_939_, size_t v_sz_940_, size_t v___x_941_, lean_object* v___x_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(v___x_938_, v_ids_939_, v_sz_940_, v___x_941_, v___x_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v___x_950_, 0);
lean_dec(v_unused_958_);
v___x_952_ = v___x_950_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_dec(v___x_950_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_942_);
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_942_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
else
{
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed(lean_object* v___x_959_, lean_object* v_ids_960_, lean_object* v_sz_961_, lean_object* v___x_962_, lean_object* v___x_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v___x_3388__boxed_971_; size_t v_sz_boxed_972_; size_t v___x_3389__boxed_973_; lean_object* v_res_974_; 
v___x_3388__boxed_971_ = lean_unbox(v___x_959_);
v_sz_boxed_972_ = lean_unbox_usize(v_sz_961_);
lean_dec(v_sz_961_);
v___x_3389__boxed_973_ = lean_unbox_usize(v___x_962_);
lean_dec(v___x_962_);
v_res_974_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(v___x_3388__boxed_971_, v_ids_960_, v_sz_boxed_972_, v___x_3389__boxed_973_, v___x_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec_ref(v_ids_960_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(lean_object* v_stx_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1));
lean_inc(v_stx_982_);
v___x_987_ = l_Lean_Syntax_isOfKind(v_stx_982_, v___x_986_);
if (v___x_987_ == 0)
{
lean_object* v___x_988_; 
lean_dec(v_stx_982_);
v___x_988_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
return v___x_988_;
}
else
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v_ids_991_; lean_object* v___x_992_; size_t v_sz_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___f_997_; lean_object* v___x_998_; 
v___x_989_ = lean_unsigned_to_nat(2u);
v___x_990_ = l_Lean_Syntax_getArg(v_stx_982_, v___x_989_);
lean_dec(v_stx_982_);
v_ids_991_ = l_Lean_Syntax_getArgs(v___x_990_);
lean_dec(v___x_990_);
v___x_992_ = lean_box(0);
v_sz_993_ = lean_array_size(v_ids_991_);
v___x_994_ = lean_box(v___x_987_);
v___x_995_ = lean_box_usize(v_sz_993_);
v___x_996_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1));
v___f_997_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed), 12, 5);
lean_closure_set(v___f_997_, 0, v___x_994_);
lean_closure_set(v___f_997_, 1, v_ids_991_);
lean_closure_set(v___f_997_, 2, v___x_995_);
lean_closure_set(v___f_997_, 3, v___x_996_);
lean_closure_set(v___f_997_, 4, v___x_992_);
v___x_998_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_997_, v_a_983_, v_a_984_);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed(lean_object* v_stx_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(v_stx_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1(){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1009_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_1010_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1));
v___x_1011_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1));
v___x_1012_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed), 4, 0);
v___x_1013_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_1009_, v___x_1010_, v___x_1011_, v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___boxed(lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1();
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(lean_object* v_items_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig));
v___x_1038_ = l_Lean_Elab_Tactic_Grind_elabConfigItems___redArg(v___x_1037_, v_items_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg___boxed(lean_object* v_items_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_items_1039_, v_a_1040_, v_a_1041_, v_a_1042_);
lean_dec(v_a_1042_);
lean_dec_ref(v_a_1041_);
lean_dec_ref(v_a_1040_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(lean_object* v_items_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_items_1045_, v_a_1046_, v_a_1050_, v_a_1051_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___boxed(lean_object* v_items_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(v_items_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(lean_object* v_init_1063_, lean_object* v_x_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
if (lean_obj_tag(v_x_1064_) == 0)
{
lean_object* v_k_1070_; lean_object* v_l_1071_; lean_object* v_r_1072_; lean_object* v___x_1073_; 
v_k_1070_ = lean_ctor_get(v_x_1064_, 1);
lean_inc(v_k_1070_);
v_l_1071_ = lean_ctor_get(v_x_1064_, 3);
lean_inc(v_l_1071_);
v_r_1072_ = lean_ctor_get(v_x_1064_, 4);
lean_inc(v_r_1072_);
lean_dec_ref_known(v_x_1064_, 5);
v___x_1073_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_init_1063_, v_l_1071_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v_a_1075_; lean_object* v___x_1076_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v_a_1075_ = lean_ctor_get(v_a_1074_, 0);
lean_inc_n(v_a_1075_, 2);
lean_dec(v_a_1074_);
v___x_1076_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_a_1075_, v_k_1070_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; 
lean_dec(v_a_1075_);
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref_known(v___x_1076_, 1);
v_init_1063_ = v_a_1077_;
v_x_1064_ = v_r_1072_;
goto _start;
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1091_; 
v_a_1079_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1081_ = v___x_1076_;
v_isShared_1082_ = v_isSharedCheck_1091_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1076_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1091_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
uint8_t v___y_1084_; uint8_t v___x_1089_; 
v___x_1089_ = l_Lean_Exception_isInterrupt(v_a_1079_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; 
lean_inc(v_a_1079_);
v___x_1090_ = l_Lean_Exception_isRuntime(v_a_1079_);
v___y_1084_ = v___x_1090_;
goto v___jp_1083_;
}
else
{
v___y_1084_ = v___x_1089_;
goto v___jp_1083_;
}
v___jp_1083_:
{
if (v___y_1084_ == 0)
{
lean_del_object(v___x_1081_);
lean_dec(v_a_1079_);
v_init_1063_ = v_a_1075_;
v_x_1064_ = v_r_1072_;
goto _start;
}
else
{
lean_object* v___x_1087_; 
lean_dec(v_a_1075_);
lean_dec(v_r_1072_);
if (v_isShared_1082_ == 0)
{
v___x_1087_ = v___x_1081_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_a_1079_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
return v___x_1087_;
}
}
}
}
}
}
else
{
lean_dec(v_r_1072_);
lean_dec(v_k_1070_);
return v___x_1073_;
}
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1092_, 0, v_init_1063_);
v___x_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0___boxed(lean_object* v_init_1094_, lean_object* v_x_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_init_1094_, v_x_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(lean_object* v_config_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1108_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1109_ = lean_box(1);
v___x_1110_ = l_Lean_Meta_Grind_mkDefaultParams(v_config_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1177_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1177_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1177_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_config_1115_; lean_object* v_extensions_1116_; lean_object* v_extra_1117_; lean_object* v_extraInj_1118_; lean_object* v_extraFacts_1119_; lean_object* v_symPrios_1120_; lean_object* v_norm_1121_; lean_object* v_normProcs_1122_; lean_object* v_anchorRefs_x3f_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1176_; 
v_config_1115_ = lean_ctor_get(v_a_1111_, 0);
v_extensions_1116_ = lean_ctor_get(v_a_1111_, 1);
v_extra_1117_ = lean_ctor_get(v_a_1111_, 2);
v_extraInj_1118_ = lean_ctor_get(v_a_1111_, 3);
v_extraFacts_1119_ = lean_ctor_get(v_a_1111_, 4);
v_symPrios_1120_ = lean_ctor_get(v_a_1111_, 5);
v_norm_1121_ = lean_ctor_get(v_a_1111_, 6);
v_normProcs_1122_ = lean_ctor_get(v_a_1111_, 7);
v_anchorRefs_x3f_1123_ = lean_ctor_get(v_a_1111_, 8);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_a_1111_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1125_ = v_a_1111_;
v_isShared_1126_ = v_isSharedCheck_1176_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_anchorRefs_x3f_1123_);
lean_inc(v_normProcs_1122_);
lean_inc(v_norm_1121_);
lean_inc(v_symPrios_1120_);
lean_inc(v_extraFacts_1119_);
lean_inc(v_extraInj_1118_);
lean_inc(v_extra_1117_);
lean_inc(v_extensions_1116_);
lean_inc(v_config_1115_);
lean_dec(v_a_1111_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1176_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___y_1128_; lean_object* v___x_1135_; lean_object* v_a_1137_; lean_object* v___x_1156_; lean_object* v_ematch_1157_; lean_object* v___x_1158_; lean_object* v_env_1159_; lean_object* v___x_1160_; lean_object* v_toEnvExtension_1161_; lean_object* v_asyncMode_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1135_ = lean_unsigned_to_nat(0u);
v___x_1156_ = lean_array_get_borrowed(v___x_1108_, v_extensions_1116_, v___x_1135_);
v_ematch_1157_ = lean_ctor_get(v___x_1156_, 3);
v___x_1158_ = lean_st_ref_get(v_a_1106_);
v_env_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc_ref(v_env_1159_);
lean_dec(v___x_1158_);
v___x_1160_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_1161_ = lean_ctor_get(v___x_1160_, 0);
v_asyncMode_1162_ = lean_ctor_get(v_toEnvExtension_1161_, 2);
v___x_1163_ = lean_box(0);
v___x_1164_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1109_, v___x_1160_, v_env_1159_, v_asyncMode_1162_, v___x_1163_);
lean_inc_ref(v_ematch_1157_);
v___x_1165_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_ematch_1157_, v___x_1164_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_);
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v_a_1167_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc(v_a_1166_);
lean_dec_ref_known(v___x_1165_, 1);
v_a_1167_ = lean_ctor_get(v_a_1166_, 0);
lean_inc(v_a_1167_);
lean_dec(v_a_1166_);
v_a_1137_ = v_a_1167_;
goto v___jp_1136_;
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
lean_del_object(v___x_1125_);
lean_dec(v_anchorRefs_x3f_1123_);
lean_dec_ref(v_normProcs_1122_);
lean_dec_ref(v_norm_1121_);
lean_dec_ref(v_symPrios_1120_);
lean_dec_ref(v_extraFacts_1119_);
lean_dec_ref(v_extraInj_1118_);
lean_dec_ref(v_extra_1117_);
lean_dec_ref(v_extensions_1116_);
lean_dec_ref(v_config_1115_);
lean_del_object(v___x_1113_);
v_a_1168_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1165_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1165_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
v___jp_1127_:
{
lean_object* v___x_1130_; 
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v___y_1128_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_config_1115_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v___y_1128_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_extra_1117_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_extraInj_1118_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v_extraFacts_1119_);
lean_ctor_set(v_reuseFailAlloc_1134_, 5, v_symPrios_1120_);
lean_ctor_set(v_reuseFailAlloc_1134_, 6, v_norm_1121_);
lean_ctor_set(v_reuseFailAlloc_1134_, 7, v_normProcs_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 8, v_anchorRefs_x3f_1123_);
v___x_1130_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
lean_object* v___x_1132_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1130_);
v___x_1132_ = v___x_1113_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
v___jp_1136_:
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_array_get_size(v_extensions_1116_);
v___x_1139_ = lean_nat_dec_lt(v___x_1135_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_dec_ref(v_a_1137_);
v___y_1128_ = v_extensions_1116_;
goto v___jp_1127_;
}
else
{
lean_object* v_v_1140_; lean_object* v_casesTypes_1141_; lean_object* v_extThms_1142_; lean_object* v_funCC_1143_; lean_object* v_inj_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1154_; 
v_v_1140_ = lean_array_fget(v_extensions_1116_, v___x_1135_);
v_casesTypes_1141_ = lean_ctor_get(v_v_1140_, 0);
v_extThms_1142_ = lean_ctor_get(v_v_1140_, 1);
v_funCC_1143_ = lean_ctor_get(v_v_1140_, 2);
v_inj_1144_ = lean_ctor_get(v_v_1140_, 4);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_v_1140_);
if (v_isSharedCheck_1154_ == 0)
{
lean_object* v_unused_1155_; 
v_unused_1155_ = lean_ctor_get(v_v_1140_, 3);
lean_dec(v_unused_1155_);
v___x_1146_ = v_v_1140_;
v_isShared_1147_ = v_isSharedCheck_1154_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_inj_1144_);
lean_inc(v_funCC_1143_);
lean_inc(v_extThms_1142_);
lean_inc(v_casesTypes_1141_);
lean_dec(v_v_1140_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1154_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v_xs_x27_1149_; lean_object* v___x_1151_; 
v___x_1148_ = lean_box(0);
v_xs_x27_1149_ = lean_array_fset(v_extensions_1116_, v___x_1135_, v___x_1148_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 3, v_a_1137_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_casesTypes_1141_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_extThms_1142_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_funCC_1143_);
lean_ctor_set(v_reuseFailAlloc_1153_, 3, v_a_1137_);
lean_ctor_set(v_reuseFailAlloc_1153_, 4, v_inj_1144_);
v___x_1151_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; 
v___x_1152_ = lean_array_fset(v_xs_x27_1149_, v___x_1135_, v___x_1151_);
v___y_1128_ = v___x_1152_;
goto v___jp_1127_;
}
}
}
}
}
}
}
else
{
return v___x_1110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams___boxed(lean_object* v_config_1178_, lean_object* v_a_1179_, lean_object* v_a_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v_res_1184_; 
v_res_1184_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_config_1178_, v_a_1179_, v_a_1180_, v_a_1181_, v_a_1182_);
lean_dec(v_a_1182_);
lean_dec_ref(v_a_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_a_1179_);
return v_res_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(lean_object* v_x_1185_, lean_object* v_____s_1186_){
_start:
{
lean_object* v_snd_1187_; lean_object* v_r_1188_; lean_object* v___x_1189_; 
v_snd_1187_ = lean_ctor_get(v_x_1185_, 1);
v_r_1188_ = lean_nat_add(v_____s_1186_, v_snd_1187_);
v___x_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1189_, 0, v_r_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0___boxed(lean_object* v_x_1190_, lean_object* v_____s_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(v_x_1190_, v_____s_1191_);
lean_dec(v_____s_1191_);
lean_dec_ref(v_x_1190_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0(lean_object* v_f_1193_, lean_object* v_s_1194_, lean_object* v_a_1195_, lean_object* v_b_1196_){
_start:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v_a_1195_);
lean_ctor_set(v___x_1197_, 1, v_b_1196_);
v___x_1198_ = lean_apply_2(v_f_1193_, v___x_1197_, v_s_1194_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1207_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1198_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1198_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1215_, lean_object* v_keys_1216_, lean_object* v_vals_1217_, lean_object* v_i_1218_, lean_object* v_acc_1219_){
_start:
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = lean_array_get_size(v_keys_1216_);
v___x_1221_ = lean_nat_dec_lt(v_i_1218_, v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
lean_dec(v_i_1218_);
lean_dec_ref(v_f_1215_);
v___x_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1222_, 0, v_acc_1219_);
return v___x_1222_;
}
else
{
lean_object* v_k_1223_; lean_object* v_v_1224_; lean_object* v___x_1225_; 
v_k_1223_ = lean_array_fget_borrowed(v_keys_1216_, v_i_1218_);
v_v_1224_ = lean_array_fget_borrowed(v_vals_1217_, v_i_1218_);
lean_inc_ref(v_f_1215_);
lean_inc(v_v_1224_);
lean_inc(v_k_1223_);
v___x_1225_ = lean_apply_3(v_f_1215_, v_acc_1219_, v_k_1223_, v_v_1224_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_dec(v_i_1218_);
lean_dec_ref(v_f_1215_);
return v___x_1225_;
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v___x_1225_, 1);
v___x_1227_ = lean_unsigned_to_nat(1u);
v___x_1228_ = lean_nat_add(v_i_1218_, v___x_1227_);
lean_dec(v_i_1218_);
v_i_1218_ = v___x_1228_;
v_acc_1219_ = v_a_1226_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1230_, lean_object* v_keys_1231_, lean_object* v_vals_1232_, lean_object* v_i_1233_, lean_object* v_acc_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1230_, v_keys_1231_, v_vals_1232_, v_i_1233_, v_acc_1234_);
lean_dec_ref(v_vals_1232_);
lean_dec_ref(v_keys_1231_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1236_, lean_object* v_as_1237_, size_t v_i_1238_, size_t v_stop_1239_, lean_object* v_b_1240_){
_start:
{
lean_object* v_a_1242_; lean_object* v___y_1247_; uint8_t v___x_1249_; 
v___x_1249_ = lean_usize_dec_eq(v_i_1238_, v_stop_1239_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_array_uget_borrowed(v_as_1237_, v_i_1238_);
switch(lean_obj_tag(v___x_1250_))
{
case 0:
{
lean_object* v_key_1251_; lean_object* v_val_1252_; lean_object* v___x_1253_; 
v_key_1251_ = lean_ctor_get(v___x_1250_, 0);
v_val_1252_ = lean_ctor_get(v___x_1250_, 1);
lean_inc_ref(v_f_1236_);
lean_inc(v_val_1252_);
lean_inc(v_key_1251_);
v___x_1253_ = lean_apply_3(v_f_1236_, v_b_1240_, v_key_1251_, v_val_1252_);
v___y_1247_ = v___x_1253_;
goto v___jp_1246_;
}
case 1:
{
lean_object* v_node_1254_; lean_object* v___x_1255_; 
v_node_1254_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_node_1254_);
lean_inc_ref(v_f_1236_);
v___x_1255_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1236_, v_node_1254_, v_b_1240_);
v___y_1247_ = v___x_1255_;
goto v___jp_1246_;
}
default: 
{
v_a_1242_ = v_b_1240_;
goto v___jp_1241_;
}
}
}
else
{
lean_object* v___x_1256_; 
lean_dec_ref(v_f_1236_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v_b_1240_);
return v___x_1256_;
}
v___jp_1241_:
{
size_t v___x_1243_; size_t v___x_1244_; 
v___x_1243_ = ((size_t)1ULL);
v___x_1244_ = lean_usize_add(v_i_1238_, v___x_1243_);
v_i_1238_ = v___x_1244_;
v_b_1240_ = v_a_1242_;
goto _start;
}
v___jp_1246_:
{
if (lean_obj_tag(v___y_1247_) == 0)
{
lean_dec_ref(v_f_1236_);
return v___y_1247_;
}
else
{
lean_object* v_a_1248_; 
v_a_1248_ = lean_ctor_get(v___y_1247_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___y_1247_, 1);
v_a_1242_ = v_a_1248_;
goto v___jp_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_){
_start:
{
if (lean_obj_tag(v_x_1258_) == 0)
{
lean_object* v_es_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1273_; 
v_es_1260_ = lean_ctor_get(v_x_1258_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_x_1258_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1262_ = v_x_1258_;
v_isShared_1263_ = v_isSharedCheck_1273_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_es_1260_);
lean_dec(v_x_1258_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1273_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v___x_1264_ = lean_unsigned_to_nat(0u);
v___x_1265_ = lean_array_get_size(v_es_1260_);
v___x_1266_ = lean_nat_dec_lt(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___x_1268_; 
lean_dec_ref(v_es_1260_);
lean_dec_ref(v_f_1257_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set_tag(v___x_1262_, 1);
lean_ctor_set(v___x_1262_, 0, v_x_1259_);
v___x_1268_ = v___x_1262_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_x_1259_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
else
{
size_t v___x_1270_; size_t v___x_1271_; lean_object* v___x_1272_; 
lean_del_object(v___x_1262_);
v___x_1270_ = ((size_t)0ULL);
v___x_1271_ = lean_usize_of_nat(v___x_1265_);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1257_, v_es_1260_, v___x_1270_, v___x_1271_, v_x_1259_);
lean_dec_ref(v_es_1260_);
return v___x_1272_;
}
}
}
else
{
lean_object* v_ks_1274_; lean_object* v_vs_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v_ks_1274_ = lean_ctor_get(v_x_1258_, 0);
lean_inc_ref(v_ks_1274_);
v_vs_1275_ = lean_ctor_get(v_x_1258_, 1);
lean_inc_ref(v_vs_1275_);
lean_dec_ref_known(v_x_1258_, 2);
v___x_1276_ = lean_unsigned_to_nat(0u);
v___x_1277_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1257_, v_ks_1274_, v_vs_1275_, v___x_1276_, v_x_1259_);
lean_dec_ref(v_vs_1275_);
lean_dec_ref(v_ks_1274_);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1278_, lean_object* v_as_1279_, lean_object* v_i_1280_, lean_object* v_stop_1281_, lean_object* v_b_1282_){
_start:
{
size_t v_i_boxed_1283_; size_t v_stop_boxed_1284_; lean_object* v_res_1285_; 
v_i_boxed_1283_ = lean_unbox_usize(v_i_1280_);
lean_dec(v_i_1280_);
v_stop_boxed_1284_ = lean_unbox_usize(v_stop_1281_);
lean_dec(v_stop_1281_);
v_res_1285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1278_, v_as_1279_, v_i_boxed_1283_, v_stop_boxed_1284_, v_b_1282_);
lean_dec_ref(v_as_1279_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(lean_object* v_map_1286_, lean_object* v_init_1287_, lean_object* v_f_1288_){
_start:
{
lean_object* v___f_1289_; lean_object* v___x_1290_; lean_object* v_a_1291_; 
v___f_1289_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1289_, 0, v_f_1288_);
lean_inc_ref(v_map_1286_);
v___x_1290_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v___f_1289_, v_map_1286_, v_init_1287_);
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref(v___x_1290_);
return v_a_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___boxed(lean_object* v_map_1292_, lean_object* v_init_1293_, lean_object* v_f_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_map_1292_, v_init_1293_, v_f_1294_);
lean_dec_ref(v_map_1292_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(lean_object* v_cs_1297_){
_start:
{
lean_object* v___f_1298_; lean_object* v_r_1299_; lean_object* v___x_1300_; 
v___f_1298_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0));
v_r_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_cs_1297_, v_r_1299_, v___f_1298_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___boxed(lean_object* v_cs_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(v_cs_1301_);
lean_dec_ref(v_cs_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(lean_object* v_00_u03c3_1303_, lean_object* v_00_u03b2_1304_, lean_object* v_map_1305_, lean_object* v_init_1306_, lean_object* v_f_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_map_1305_, v_init_1306_, v_f_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___boxed(lean_object* v_00_u03c3_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_map_1311_, lean_object* v_init_1312_, lean_object* v_f_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(v_00_u03c3_1309_, v_00_u03b2_1310_, v_map_1311_, v_init_1312_, v_f_1313_);
lean_dec_ref(v_map_1311_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0___redArg(lean_object* v_map_1315_, lean_object* v_f_1316_, lean_object* v_init_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1316_, v_map_1315_, v_init_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0(lean_object* v_00_u03c3_1319_, lean_object* v_00_u03c3_1320_, lean_object* v_00_u03b2_1321_, lean_object* v_map_1322_, lean_object* v_f_1323_, lean_object* v_init_1324_){
_start:
{
lean_object* v___x_1325_; 
v___x_1325_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1323_, v_map_1322_, v_init_1324_);
return v___x_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1326_, lean_object* v_00_u03c3_1327_, lean_object* v_00_u03b1_1328_, lean_object* v_00_u03b2_1329_, lean_object* v_f_1330_, lean_object* v_x_1331_, lean_object* v_x_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1330_, v_x_1331_, v_x_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1334_, lean_object* v_00_u03b2_1335_, lean_object* v_00_u03c3_1336_, lean_object* v_00_u03c3_1337_, lean_object* v_f_1338_, lean_object* v_as_1339_, size_t v_i_1340_, size_t v_stop_1341_, lean_object* v_b_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1338_, v_as_1339_, v_i_1340_, v_stop_1341_, v_b_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1344_, lean_object* v_00_u03b2_1345_, lean_object* v_00_u03c3_1346_, lean_object* v_00_u03c3_1347_, lean_object* v_f_1348_, lean_object* v_as_1349_, lean_object* v_i_1350_, lean_object* v_stop_1351_, lean_object* v_b_1352_){
_start:
{
size_t v_i_boxed_1353_; size_t v_stop_boxed_1354_; lean_object* v_res_1355_; 
v_i_boxed_1353_ = lean_unbox_usize(v_i_1350_);
lean_dec(v_i_1350_);
v_stop_boxed_1354_ = lean_unbox_usize(v_stop_1351_);
lean_dec(v_stop_1351_);
v_res_1355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1344_, v_00_u03b2_1345_, v_00_u03c3_1346_, v_00_u03c3_1347_, v_f_1348_, v_as_1349_, v_i_boxed_1353_, v_stop_boxed_1354_, v_b_1352_);
lean_dec_ref(v_as_1349_);
return v_res_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_1356_, lean_object* v_00_u03c3_1357_, lean_object* v_00_u03b1_1358_, lean_object* v_00_u03b2_1359_, lean_object* v_f_1360_, lean_object* v_keys_1361_, lean_object* v_vals_1362_, lean_object* v_heq_1363_, lean_object* v_i_1364_, lean_object* v_acc_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1360_, v_keys_1361_, v_vals_1362_, v_i_1364_, v_acc_1365_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1367_, lean_object* v_00_u03c3_1368_, lean_object* v_00_u03b1_1369_, lean_object* v_00_u03b2_1370_, lean_object* v_f_1371_, lean_object* v_keys_1372_, lean_object* v_vals_1373_, lean_object* v_heq_1374_, lean_object* v_i_1375_, lean_object* v_acc_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_1367_, v_00_u03c3_1368_, v_00_u03b1_1369_, v_00_u03b2_1370_, v_f_1371_, v_keys_1372_, v_vals_1373_, v_heq_1374_, v_i_1375_, v_acc_1376_);
lean_dec_ref(v_vals_1373_);
lean_dec_ref(v_keys_1372_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(lean_object* v_as_1378_, size_t v_i_1379_, size_t v_stop_1380_, lean_object* v_b_1381_){
_start:
{
lean_object* v___y_1383_; uint8_t v___x_1387_; 
v___x_1387_ = lean_usize_dec_eq(v_i_1379_, v_stop_1380_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v_fst_1389_; 
v___x_1388_ = lean_array_uget(v_as_1378_, v_i_1379_);
v_fst_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_fst_1389_);
if (lean_obj_tag(v_fst_1389_) == 0)
{
lean_object* v_snd_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1399_; 
v_snd_1390_ = lean_ctor_get(v___x_1388_, 1);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1388_);
if (v_isSharedCheck_1399_ == 0)
{
lean_object* v_unused_1400_; 
v_unused_1400_ = lean_ctor_get(v___x_1388_, 0);
lean_dec(v_unused_1400_);
v___x_1392_ = v___x_1388_;
v_isShared_1393_ = v_isSharedCheck_1399_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_snd_1390_);
lean_dec(v___x_1388_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1399_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v_declName_1394_; lean_object* v___x_1396_; 
v_declName_1394_ = lean_ctor_get(v_fst_1389_, 0);
lean_inc(v_declName_1394_);
lean_dec_ref_known(v_fst_1389_, 1);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v_declName_1394_);
v___x_1396_ = v___x_1392_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v_declName_1394_);
lean_ctor_set(v_reuseFailAlloc_1398_, 1, v_snd_1390_);
v___x_1396_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_array_push(v_b_1381_, v___x_1396_);
v___y_1383_ = v___x_1397_;
goto v___jp_1382_;
}
}
}
else
{
lean_dec(v_fst_1389_);
lean_dec(v___x_1388_);
v___y_1383_ = v_b_1381_;
goto v___jp_1382_;
}
}
else
{
return v_b_1381_;
}
v___jp_1382_:
{
size_t v___x_1384_; size_t v___x_1385_; 
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_add(v_i_1379_, v___x_1384_);
v_i_1379_ = v___x_1385_;
v_b_1381_ = v___y_1383_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6___boxed(lean_object* v_as_1401_, lean_object* v_i_1402_, lean_object* v_stop_1403_, lean_object* v_b_1404_){
_start:
{
size_t v_i_boxed_1405_; size_t v_stop_boxed_1406_; lean_object* v_res_1407_; 
v_i_boxed_1405_ = lean_unbox_usize(v_i_1402_);
lean_dec(v_i_1402_);
v_stop_boxed_1406_ = lean_unbox_usize(v_stop_1403_);
lean_dec(v_stop_1403_);
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1401_, v_i_boxed_1405_, v_stop_boxed_1406_, v_b_1404_);
lean_dec_ref(v_as_1401_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(lean_object* v_as_1410_, lean_object* v_start_1411_, lean_object* v_stop_1412_){
_start:
{
lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1413_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0));
v___x_1414_ = lean_nat_dec_lt(v_start_1411_, v_stop_1412_);
if (v___x_1414_ == 0)
{
return v___x_1413_;
}
else
{
lean_object* v___x_1415_; uint8_t v___x_1416_; 
v___x_1415_ = lean_array_get_size(v_as_1410_);
v___x_1416_ = lean_nat_dec_le(v_stop_1412_, v___x_1415_);
if (v___x_1416_ == 0)
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_lt(v_start_1411_, v___x_1415_);
if (v___x_1417_ == 0)
{
return v___x_1413_;
}
else
{
size_t v___x_1418_; size_t v___x_1419_; lean_object* v___x_1420_; 
v___x_1418_ = lean_usize_of_nat(v_start_1411_);
v___x_1419_ = lean_usize_of_nat(v___x_1415_);
v___x_1420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1410_, v___x_1418_, v___x_1419_, v___x_1413_);
return v___x_1420_;
}
}
else
{
size_t v___x_1421_; size_t v___x_1422_; lean_object* v___x_1423_; 
v___x_1421_ = lean_usize_of_nat(v_start_1411_);
v___x_1422_ = lean_usize_of_nat(v_stop_1412_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1410_, v___x_1421_, v___x_1422_, v___x_1413_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___boxed(lean_object* v_as_1424_, lean_object* v_start_1425_, lean_object* v_stop_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(v_as_1424_, v_start_1425_, v_stop_1426_);
lean_dec(v_stop_1426_);
lean_dec(v_start_1425_);
lean_dec_ref(v_as_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(lean_object* v_x_1428_, lean_object* v_x_1429_){
_start:
{
lean_object* v_fst_1430_; lean_object* v_snd_1431_; lean_object* v_fst_1432_; lean_object* v_snd_1433_; uint8_t v___x_1434_; 
v_fst_1430_ = lean_ctor_get(v_x_1428_, 0);
v_snd_1431_ = lean_ctor_get(v_x_1428_, 1);
v_fst_1432_ = lean_ctor_get(v_x_1429_, 0);
v_snd_1433_ = lean_ctor_get(v_x_1429_, 1);
v___x_1434_ = lean_nat_dec_eq(v_snd_1431_, v_snd_1433_);
if (v___x_1434_ == 0)
{
uint8_t v___x_1435_; 
v___x_1435_ = lean_nat_dec_lt(v_snd_1433_, v_snd_1431_);
return v___x_1435_;
}
else
{
uint8_t v___x_1436_; 
v___x_1436_ = l_Lean_Name_lt(v_fst_1430_, v_fst_1432_);
return v___x_1436_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0___boxed(lean_object* v_x_1437_, lean_object* v_x_1438_){
_start:
{
uint8_t v_res_1439_; lean_object* v_r_1440_; 
v_res_1439_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v_x_1437_, v_x_1438_);
lean_dec_ref(v_x_1438_);
lean_dec_ref(v_x_1437_);
v_r_1440_ = lean_box(v_res_1439_);
return v_r_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(lean_object* v_hi_1441_, lean_object* v_pivot_1442_, lean_object* v_as_1443_, lean_object* v_i_1444_, lean_object* v_k_1445_){
_start:
{
uint8_t v___y_1447_; uint8_t v___x_1456_; 
v___x_1456_ = lean_nat_dec_lt(v_k_1445_, v_hi_1441_);
if (v___x_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
lean_dec(v_k_1445_);
v___x_1457_ = lean_array_fswap(v_as_1443_, v_i_1444_, v_hi_1441_);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_i_1444_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
return v___x_1458_;
}
else
{
lean_object* v___x_1459_; lean_object* v_fst_1460_; lean_object* v_snd_1461_; lean_object* v_fst_1462_; lean_object* v_snd_1463_; uint8_t v___x_1464_; 
v___x_1459_ = lean_array_fget_borrowed(v_as_1443_, v_k_1445_);
v_fst_1460_ = lean_ctor_get(v___x_1459_, 0);
v_snd_1461_ = lean_ctor_get(v___x_1459_, 1);
v_fst_1462_ = lean_ctor_get(v_pivot_1442_, 0);
v_snd_1463_ = lean_ctor_get(v_pivot_1442_, 1);
v___x_1464_ = lean_nat_dec_eq(v_snd_1461_, v_snd_1463_);
if (v___x_1464_ == 0)
{
uint8_t v___x_1465_; 
v___x_1465_ = lean_nat_dec_lt(v_snd_1463_, v_snd_1461_);
v___y_1447_ = v___x_1465_;
goto v___jp_1446_;
}
else
{
uint8_t v___x_1466_; 
v___x_1466_ = l_Lean_Name_lt(v_fst_1460_, v_fst_1462_);
v___y_1447_ = v___x_1466_;
goto v___jp_1446_;
}
}
v___jp_1446_:
{
if (v___y_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_add(v_k_1445_, v___x_1448_);
lean_dec(v_k_1445_);
v_k_1445_ = v___x_1449_;
goto _start;
}
else
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1451_ = lean_array_fswap(v_as_1443_, v_i_1444_, v_k_1445_);
v___x_1452_ = lean_unsigned_to_nat(1u);
v___x_1453_ = lean_nat_add(v_i_1444_, v___x_1452_);
lean_dec(v_i_1444_);
v___x_1454_ = lean_nat_add(v_k_1445_, v___x_1452_);
lean_dec(v_k_1445_);
v_as_1443_ = v___x_1451_;
v_i_1444_ = v___x_1453_;
v_k_1445_ = v___x_1454_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg___boxed(lean_object* v_hi_1467_, lean_object* v_pivot_1468_, lean_object* v_as_1469_, lean_object* v_i_1470_, lean_object* v_k_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_1467_, v_pivot_1468_, v_as_1469_, v_i_1470_, v_k_1471_);
lean_dec_ref(v_pivot_1468_);
lean_dec(v_hi_1467_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(lean_object* v_n_1473_, lean_object* v_as_1474_, lean_object* v_lo_1475_, lean_object* v_hi_1476_){
_start:
{
lean_object* v___y_1478_; uint8_t v___x_1488_; 
v___x_1488_ = lean_nat_dec_lt(v_lo_1475_, v_hi_1476_);
if (v___x_1488_ == 0)
{
lean_dec(v_lo_1475_);
return v_as_1474_;
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v_mid_1491_; lean_object* v___y_1493_; lean_object* v___y_1499_; lean_object* v___x_1504_; lean_object* v___x_1505_; uint8_t v___x_1506_; 
v___x_1489_ = lean_nat_add(v_lo_1475_, v_hi_1476_);
v___x_1490_ = lean_unsigned_to_nat(1u);
v_mid_1491_ = lean_nat_shiftr(v___x_1489_, v___x_1490_);
lean_dec(v___x_1489_);
v___x_1504_ = lean_array_fget_borrowed(v_as_1474_, v_mid_1491_);
v___x_1505_ = lean_array_fget_borrowed(v_as_1474_, v_lo_1475_);
v___x_1506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1504_, v___x_1505_);
if (v___x_1506_ == 0)
{
v___y_1499_ = v_as_1474_;
goto v___jp_1498_;
}
else
{
lean_object* v___x_1507_; 
v___x_1507_ = lean_array_fswap(v_as_1474_, v_lo_1475_, v_mid_1491_);
v___y_1499_ = v___x_1507_;
goto v___jp_1498_;
}
v___jp_1492_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; uint8_t v___x_1496_; 
v___x_1494_ = lean_array_fget_borrowed(v___y_1493_, v_mid_1491_);
v___x_1495_ = lean_array_fget_borrowed(v___y_1493_, v_hi_1476_);
v___x_1496_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1494_, v___x_1495_);
if (v___x_1496_ == 0)
{
lean_dec(v_mid_1491_);
v___y_1478_ = v___y_1493_;
goto v___jp_1477_;
}
else
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_array_fswap(v___y_1493_, v_mid_1491_, v_hi_1476_);
lean_dec(v_mid_1491_);
v___y_1478_ = v___x_1497_;
goto v___jp_1477_;
}
}
v___jp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; uint8_t v___x_1502_; 
v___x_1500_ = lean_array_fget_borrowed(v___y_1499_, v_hi_1476_);
v___x_1501_ = lean_array_fget_borrowed(v___y_1499_, v_lo_1475_);
v___x_1502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1500_, v___x_1501_);
if (v___x_1502_ == 0)
{
v___y_1493_ = v___y_1499_;
goto v___jp_1492_;
}
else
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_array_fswap(v___y_1499_, v_lo_1475_, v_hi_1476_);
v___y_1493_ = v___x_1503_;
goto v___jp_1492_;
}
}
}
v___jp_1477_:
{
lean_object* v_pivot_1479_; lean_object* v___x_1480_; lean_object* v_fst_1481_; lean_object* v_snd_1482_; uint8_t v___x_1483_; 
v_pivot_1479_ = lean_array_fget(v___y_1478_, v_hi_1476_);
lean_inc_n(v_lo_1475_, 2);
v___x_1480_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_1476_, v_pivot_1479_, v___y_1478_, v_lo_1475_, v_lo_1475_);
lean_dec(v_pivot_1479_);
v_fst_1481_ = lean_ctor_get(v___x_1480_, 0);
lean_inc(v_fst_1481_);
v_snd_1482_ = lean_ctor_get(v___x_1480_, 1);
lean_inc(v_snd_1482_);
lean_dec_ref(v___x_1480_);
v___x_1483_ = lean_nat_dec_le(v_hi_1476_, v_fst_1481_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1484_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_1473_, v_snd_1482_, v_lo_1475_, v_fst_1481_);
v___x_1485_ = lean_unsigned_to_nat(1u);
v___x_1486_ = lean_nat_add(v_fst_1481_, v___x_1485_);
lean_dec(v_fst_1481_);
v_as_1474_ = v___x_1484_;
v_lo_1475_ = v___x_1486_;
goto _start;
}
else
{
lean_dec(v_fst_1481_);
lean_dec(v_lo_1475_);
return v_snd_1482_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___boxed(lean_object* v_n_1508_, lean_object* v_as_1509_, lean_object* v_lo_1510_, lean_object* v_hi_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_1508_, v_as_1509_, v_lo_1510_, v_hi_1511_);
lean_dec(v_hi_1511_);
lean_dec(v_n_1508_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___lam__0(lean_object* v_ps_1513_, lean_object* v_k_1514_, lean_object* v_v_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1516_, 0, v_k_1514_);
lean_ctor_set(v___x_1516_, 1, v_v_1515_);
v___x_1517_ = lean_array_push(v_ps_1513_, v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0(lean_object* v_f_1518_, lean_object* v_x1_1519_, lean_object* v_x2_1520_, lean_object* v_x3_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_apply_3(v_f_1518_, v_x1_1519_, v_x2_1520_, v_x3_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(lean_object* v_f_1523_, lean_object* v_keys_1524_, lean_object* v_vals_1525_, lean_object* v_i_1526_, lean_object* v_acc_1527_){
_start:
{
lean_object* v___x_1528_; uint8_t v___x_1529_; 
v___x_1528_ = lean_array_get_size(v_keys_1524_);
v___x_1529_ = lean_nat_dec_lt(v_i_1526_, v___x_1528_);
if (v___x_1529_ == 0)
{
lean_dec(v_i_1526_);
lean_dec(v_f_1523_);
return v_acc_1527_;
}
else
{
lean_object* v_k_1530_; lean_object* v_v_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v_k_1530_ = lean_array_fget_borrowed(v_keys_1524_, v_i_1526_);
v_v_1531_ = lean_array_fget_borrowed(v_vals_1525_, v_i_1526_);
lean_inc(v_f_1523_);
lean_inc(v_v_1531_);
lean_inc(v_k_1530_);
v___x_1532_ = lean_apply_3(v_f_1523_, v_acc_1527_, v_k_1530_, v_v_1531_);
v___x_1533_ = lean_unsigned_to_nat(1u);
v___x_1534_ = lean_nat_add(v_i_1526_, v___x_1533_);
lean_dec(v_i_1526_);
v_i_1526_ = v___x_1534_;
v_acc_1527_ = v___x_1532_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_f_1536_, lean_object* v_keys_1537_, lean_object* v_vals_1538_, lean_object* v_i_1539_, lean_object* v_acc_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_1536_, v_keys_1537_, v_vals_1538_, v_i_1539_, v_acc_1540_);
lean_dec_ref(v_vals_1538_);
lean_dec_ref(v_keys_1537_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(lean_object* v_f_1542_, lean_object* v_as_1543_, size_t v_i_1544_, size_t v_stop_1545_, lean_object* v_b_1546_){
_start:
{
lean_object* v___y_1548_; uint8_t v___x_1552_; 
v___x_1552_ = lean_usize_dec_eq(v_i_1544_, v_stop_1545_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_array_uget_borrowed(v_as_1543_, v_i_1544_);
switch(lean_obj_tag(v___x_1553_))
{
case 0:
{
lean_object* v_key_1554_; lean_object* v_val_1555_; lean_object* v___x_1556_; 
v_key_1554_ = lean_ctor_get(v___x_1553_, 0);
v_val_1555_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_f_1542_);
lean_inc(v_val_1555_);
lean_inc(v_key_1554_);
v___x_1556_ = lean_apply_3(v_f_1542_, v_b_1546_, v_key_1554_, v_val_1555_);
v___y_1548_ = v___x_1556_;
goto v___jp_1547_;
}
case 1:
{
lean_object* v_node_1557_; lean_object* v___x_1558_; 
v_node_1557_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_f_1542_);
v___x_1558_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_1542_, v_node_1557_, v_b_1546_);
v___y_1548_ = v___x_1558_;
goto v___jp_1547_;
}
default: 
{
v___y_1548_ = v_b_1546_;
goto v___jp_1547_;
}
}
}
else
{
lean_dec(v_f_1542_);
return v_b_1546_;
}
v___jp_1547_:
{
size_t v___x_1549_; size_t v___x_1550_; 
v___x_1549_ = ((size_t)1ULL);
v___x_1550_ = lean_usize_add(v_i_1544_, v___x_1549_);
v_i_1544_ = v___x_1550_;
v_b_1546_ = v___y_1548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_f_1559_, lean_object* v_x_1560_, lean_object* v_x_1561_){
_start:
{
if (lean_obj_tag(v_x_1560_) == 0)
{
lean_object* v_es_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
v_es_1562_ = lean_ctor_get(v_x_1560_, 0);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_array_get_size(v_es_1562_);
v___x_1565_ = lean_nat_dec_lt(v___x_1563_, v___x_1564_);
if (v___x_1565_ == 0)
{
lean_dec(v_f_1559_);
return v_x_1561_;
}
else
{
size_t v___x_1566_; size_t v___x_1567_; lean_object* v___x_1568_; 
v___x_1566_ = ((size_t)0ULL);
v___x_1567_ = lean_usize_of_nat(v___x_1564_);
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_1559_, v_es_1562_, v___x_1566_, v___x_1567_, v_x_1561_);
return v___x_1568_;
}
}
else
{
lean_object* v_ks_1569_; lean_object* v_vs_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_ks_1569_ = lean_ctor_get(v_x_1560_, 0);
v_vs_1570_ = lean_ctor_get(v_x_1560_, 1);
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_1559_, v_ks_1569_, v_vs_1570_, v___x_1571_, v_x_1561_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_f_1573_, lean_object* v_x_1574_, lean_object* v_x_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_1573_, v_x_1574_, v_x_1575_);
lean_dec_ref(v_x_1574_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg___boxed(lean_object* v_f_1577_, lean_object* v_as_1578_, lean_object* v_i_1579_, lean_object* v_stop_1580_, lean_object* v_b_1581_){
_start:
{
size_t v_i_boxed_1582_; size_t v_stop_boxed_1583_; lean_object* v_res_1584_; 
v_i_boxed_1582_ = lean_unbox_usize(v_i_1579_);
lean_dec(v_i_1579_);
v_stop_boxed_1583_ = lean_unbox_usize(v_stop_1580_);
lean_dec(v_stop_1580_);
v_res_1584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_1577_, v_as_1578_, v_i_boxed_1582_, v_stop_boxed_1583_, v_b_1581_);
lean_dec_ref(v_as_1578_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(lean_object* v_map_1585_, lean_object* v_f_1586_, lean_object* v_init_1587_){
_start:
{
lean_object* v___f_1588_; lean_object* v___x_1589_; 
v___f_1588_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1588_, 0, v_f_1586_);
v___x_1589_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v___f_1588_, v_map_1585_, v_init_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___boxed(lean_object* v_map_1590_, lean_object* v_f_1591_, lean_object* v_init_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_map_1590_, v_f_1591_, v_init_1592_);
lean_dec_ref(v_map_1590_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(lean_object* v_m_1597_){
_start:
{
lean_object* v___f_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___f_1598_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0));
v___x_1599_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1));
v___x_1600_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_m_1597_, v___f_1598_, v___x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___boxed(lean_object* v_m_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_m_1601_);
lean_dec_ref(v_m_1601_);
return v_res_1602_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0));
v___x_1605_ = l_Lean_stringToMessageData(v___x_1604_);
return v___x_1605_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2));
v___x_1608_ = l_Lean_stringToMessageData(v___x_1607_);
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4));
v___x_1611_ = l_Lean_stringToMessageData(v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6));
v___x_1614_ = l_Lean_stringToMessageData(v___x_1613_);
return v___x_1614_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8));
v___x_1617_ = l_Lean_stringToMessageData(v___x_1616_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10));
v___x_1620_ = l_Lean_stringToMessageData(v___x_1619_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12));
v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
return v___x_1623_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__15(void){
_start:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__14));
v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__17(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__16));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__19(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__18));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__21(void){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__20));
v___x_1635_ = l_Lean_stringToMessageData(v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(lean_object* v_msg_1636_, lean_object* v_declHint_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_env_1642_; uint8_t v___x_1643_; 
v___x_1640_ = lean_box(0);
v___x_1641_ = lean_st_ref_get(v___y_1638_);
v_env_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc_ref(v_env_1642_);
lean_dec(v___x_1641_);
v___x_1643_ = l_Lean_Name_isAnonymous(v_declHint_1637_);
if (v___x_1643_ == 0)
{
uint8_t v_isExporting_1644_; 
v_isExporting_1644_ = lean_ctor_get_uint8(v_env_1642_, sizeof(void*)*13);
if (v_isExporting_1644_ == 0)
{
lean_object* v___x_1645_; 
lean_dec_ref(v_env_1642_);
lean_dec(v_declHint_1637_);
v___x_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1645_, 0, v_msg_1636_);
return v___x_1645_;
}
else
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
lean_inc_ref(v_env_1642_);
v___x_1646_ = l_Lean_Environment_setExporting(v_env_1642_, v___x_1643_);
lean_inc(v_declHint_1637_);
lean_inc_ref(v___x_1646_);
v___x_1647_ = l_Lean_Environment_contains(v___x_1646_, v_declHint_1637_, v_isExporting_1644_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_dec_ref(v___x_1646_);
lean_dec_ref(v_env_1642_);
lean_dec(v_declHint_1637_);
v___x_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1648_, 0, v_msg_1636_);
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v_c_1654_; lean_object* v___x_1655_; 
v___x_1649_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2);
v___x_1650_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5);
v___x_1651_ = l_Lean_Options_empty;
v___x_1652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1646_);
lean_ctor_set(v___x_1652_, 1, v___x_1649_);
lean_ctor_set(v___x_1652_, 2, v___x_1650_);
lean_ctor_set(v___x_1652_, 3, v___x_1651_);
lean_inc(v_declHint_1637_);
v___x_1653_ = l_Lean_MessageData_ofConstName(v_declHint_1637_, v___x_1643_);
v_c_1654_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1654_, 0, v___x_1652_);
lean_ctor_set(v_c_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1642_, v_declHint_1637_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
lean_dec_ref(v_env_1642_);
lean_dec(v_declHint_1637_);
v___x_1656_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
lean_ctor_set(v___x_1657_, 1, v_c_1654_);
v___x_1658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_1659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1657_);
lean_ctor_set(v___x_1659_, 1, v___x_1658_);
v___x_1660_ = l_Lean_MessageData_note(v___x_1659_);
v___x_1661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1661_, 0, v_msg_1636_);
lean_ctor_set(v___x_1661_, 1, v___x_1660_);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
return v___x_1662_;
}
else
{
lean_object* v_val_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1719_; 
v_val_1663_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1665_ = v___x_1655_;
v_isShared_1666_ = v_isSharedCheck_1719_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_val_1663_);
lean_dec(v___x_1655_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1719_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v_modules_1668_; lean_object* v_moduleNames_1669_; lean_object* v_mod_1670_; uint8_t v___y_1672_; uint8_t v___x_1702_; 
v___x_1667_ = l_Lean_Environment_header(v_env_1642_);
lean_dec_ref(v_env_1642_);
v_modules_1668_ = lean_ctor_get(v___x_1667_, 3);
lean_inc_ref(v_modules_1668_);
v_moduleNames_1669_ = lean_ctor_get(v___x_1667_, 4);
lean_inc_ref(v_moduleNames_1669_);
lean_dec_ref(v___x_1667_);
v_mod_1670_ = lean_array_get(v___x_1640_, v_moduleNames_1669_, v_val_1663_);
lean_dec_ref(v_moduleNames_1669_);
v___x_1702_ = l_Lean_isPrivateName(v_declHint_1637_);
lean_dec(v_declHint_1637_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1703_ = lean_array_get_size(v_modules_1668_);
v___x_1704_ = lean_nat_dec_lt(v_val_1663_, v___x_1703_);
if (v___x_1704_ == 0)
{
lean_dec_ref(v_modules_1668_);
lean_dec(v_val_1663_);
v___y_1672_ = v___x_1702_;
goto v___jp_1671_;
}
else
{
lean_object* v___x_1705_; lean_object* v_toImport_1706_; uint8_t v_isExported_1707_; 
v___x_1705_ = lean_array_fget(v_modules_1668_, v_val_1663_);
lean_dec(v_val_1663_);
lean_dec_ref(v_modules_1668_);
v_toImport_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc_ref(v_toImport_1706_);
lean_dec(v___x_1705_);
v_isExported_1707_ = lean_ctor_get_uint8(v_toImport_1706_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_1706_);
v___y_1672_ = v_isExported_1707_;
goto v___jp_1671_;
}
}
else
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_dec_ref(v_modules_1668_);
lean_del_object(v___x_1665_);
lean_dec(v_val_1663_);
v___x_1708_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_1709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
lean_ctor_set(v___x_1709_, 1, v_c_1654_);
v___x_1710_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__19);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1709_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = l_Lean_MessageData_ofName(v_mod_1670_);
v___x_1713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__21);
v___x_1715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1715_, 0, v___x_1713_);
lean_ctor_set(v___x_1715_, 1, v___x_1714_);
v___x_1716_ = l_Lean_MessageData_note(v___x_1715_);
v___x_1717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1717_, 0, v_msg_1636_);
lean_ctor_set(v___x_1717_, 1, v___x_1716_);
v___x_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
return v___x_1718_;
}
v___jp_1671_:
{
if (v___y_1672_ == 0)
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1684_; 
v___x_1673_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5);
v___x_1674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v_c_1654_);
v___x_1675_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_1676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1674_);
lean_ctor_set(v___x_1676_, 1, v___x_1675_);
v___x_1677_ = l_Lean_MessageData_ofName(v_mod_1670_);
v___x_1678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
v___x_1679_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9);
v___x_1680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1678_);
lean_ctor_set(v___x_1680_, 1, v___x_1679_);
v___x_1681_ = l_Lean_MessageData_note(v___x_1680_);
v___x_1682_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1682_, 0, v_msg_1636_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1682_);
v___x_1684_ = v___x_1665_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v___x_1682_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
else
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1700_; 
v___x_1686_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11);
v___x_1687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v_c_1654_);
v___x_1688_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13);
v___x_1689_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1687_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = l_Lean_MessageData_ofName(v_mod_1670_);
lean_inc_ref(v___x_1690_);
v___x_1691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1689_);
lean_ctor_set(v___x_1691_, 1, v___x_1690_);
v___x_1692_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__15);
v___x_1693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1691_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v___x_1690_);
v___x_1695_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__17);
v___x_1696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1694_);
lean_ctor_set(v___x_1696_, 1, v___x_1695_);
v___x_1697_ = l_Lean_MessageData_note(v___x_1696_);
v___x_1698_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1698_, 0, v_msg_1636_);
lean_ctor_set(v___x_1698_, 1, v___x_1697_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set_tag(v___x_1665_, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1698_);
v___x_1700_ = v___x_1665_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
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
lean_object* v___x_1720_; 
lean_dec_ref(v_env_1642_);
lean_dec(v_declHint_1637_);
v___x_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1720_, 0, v_msg_1636_);
return v___x_1720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___boxed(lean_object* v_msg_1721_, lean_object* v_declHint_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_1721_, v_declHint_1722_, v___y_1723_);
lean_dec(v___y_1723_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(lean_object* v_msg_1726_, lean_object* v_declHint_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1743_; 
v___x_1733_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_1726_, v_declHint_1727_, v___y_1731_);
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1736_ = v___x_1733_;
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1733_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1738_ = l_Lean_unknownIdentifierMessageTag;
v___x_1739_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
lean_ctor_set(v___x_1739_, 1, v_a_1734_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1739_);
v___x_1741_ = v___x_1736_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16___boxed(lean_object* v_msg_1744_, lean_object* v_declHint_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(v_msg_1744_, v_declHint_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(lean_object* v_msg_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_ref_1758_; lean_object* v___x_1759_; lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1768_; 
v_ref_1758_ = lean_ctor_get(v___y_1755_, 2);
v___x_1759_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v_msg_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1768_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1764_; lean_object* v___x_1766_; 
lean_inc(v_ref_1758_);
v___x_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1764_, 0, v_ref_1758_);
lean_ctor_set(v___x_1764_, 1, v_a_1760_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set_tag(v___x_1762_, 1);
lean_ctor_set(v___x_1762_, 0, v___x_1764_);
v___x_1766_ = v___x_1762_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1764_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_msg_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
lean_dec_ref(v___y_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(lean_object* v_ref_1776_, lean_object* v_msg_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_){
_start:
{
lean_object* v_toCold_1783_; lean_object* v_currRecDepth_1784_; lean_object* v_ref_1785_; uint16_t v_optionFlags_1786_; uint8_t v_suppressElabErrors_1787_; uint8_t v_isRecordingDeps_1788_; lean_object* v_ref_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_toCold_1783_ = lean_ctor_get(v___y_1780_, 0);
v_currRecDepth_1784_ = lean_ctor_get(v___y_1780_, 1);
v_ref_1785_ = lean_ctor_get(v___y_1780_, 2);
v_optionFlags_1786_ = lean_ctor_get_uint16(v___y_1780_, sizeof(void*)*3);
v_suppressElabErrors_1787_ = lean_ctor_get_uint8(v___y_1780_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1788_ = lean_ctor_get_uint8(v___y_1780_, sizeof(void*)*3 + 3);
v_ref_1789_ = l_Lean_replaceRef(v_ref_1776_, v_ref_1785_);
lean_inc(v_currRecDepth_1784_);
lean_inc_ref(v_toCold_1783_);
v___x_1790_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1790_, 0, v_toCold_1783_);
lean_ctor_set(v___x_1790_, 1, v_currRecDepth_1784_);
lean_ctor_set(v___x_1790_, 2, v_ref_1789_);
lean_ctor_set_uint16(v___x_1790_, sizeof(void*)*3, v_optionFlags_1786_);
lean_ctor_set_uint8(v___x_1790_, sizeof(void*)*3 + 2, v_suppressElabErrors_1787_);
lean_ctor_set_uint8(v___x_1790_, sizeof(void*)*3 + 3, v_isRecordingDeps_1788_);
v___x_1791_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_1777_, v___y_1778_, v___y_1779_, v___x_1790_, v___y_1781_);
lean_dec_ref_known(v___x_1790_, 3);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg___boxed(lean_object* v_ref_1792_, lean_object* v_msg_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_1792_, v_msg_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec(v_ref_1792_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(lean_object* v_ref_1800_, lean_object* v_msg_1801_, lean_object* v_declHint_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; lean_object* v_a_1809_; lean_object* v___x_1810_; 
v___x_1808_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(v_msg_1801_, v_declHint_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref(v___x_1808_);
v___x_1810_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_1800_, v_a_1809_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg___boxed(lean_object* v_ref_1811_, lean_object* v_msg_1812_, lean_object* v_declHint_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_1811_, v_msg_1812_, v_declHint_1813_, v___y_1814_, v___y_1815_, v___y_1816_, v___y_1817_);
lean_dec(v___y_1817_);
lean_dec_ref(v___y_1816_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v_ref_1811_);
return v_res_1819_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0));
v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(lean_object* v_ref_1823_, lean_object* v_constName_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v___x_1830_; uint8_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1830_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1);
v___x_1831_ = 0;
lean_inc(v_constName_1824_);
v___x_1832_ = l_Lean_MessageData_ofConstName(v_constName_1824_, v___x_1831_);
v___x_1833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1830_);
lean_ctor_set(v___x_1833_, 1, v___x_1832_);
v___x_1834_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
v___x_1835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
lean_ctor_set(v___x_1835_, 1, v___x_1834_);
v___x_1836_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_1823_, v___x_1835_, v_constName_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_ref_1837_, lean_object* v_constName_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_1837_, v_constName_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec(v_ref_1837_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(lean_object* v_constName_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_ref_1851_; lean_object* v___x_1852_; 
v_ref_1851_ = lean_ctor_get(v___y_1848_, 2);
v___x_1852_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_1851_, v_constName_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_constName_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(lean_object* v_constName_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; lean_object* v_env_1867_; uint8_t v___x_1868_; lean_object* v___x_1869_; 
v___x_1866_ = lean_st_ref_get(v___y_1864_);
v_env_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc_ref(v_env_1867_);
lean_dec(v___x_1866_);
v___x_1868_ = 0;
lean_inc(v_constName_1860_);
v___x_1869_ = l_Lean_Environment_findConstVal_x3f(v_env_1867_, v_constName_1860_, v___x_1868_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
return v___x_1870_;
}
else
{
lean_object* v_val_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1878_; 
lean_dec(v_constName_1860_);
v_val_1871_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1878_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1873_ = v___x_1869_;
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_val_1871_);
lean_dec(v___x_1869_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1878_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1876_; 
if (v_isShared_1874_ == 0)
{
lean_ctor_set_tag(v___x_1873_, 0);
v___x_1876_ = v___x_1873_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_val_1871_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2___boxed(lean_object* v_constName_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(v_constName_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(lean_object* v_a_1886_, lean_object* v_a_1887_){
_start:
{
if (lean_obj_tag(v_a_1886_) == 0)
{
lean_object* v___x_1888_; 
v___x_1888_ = l_List_reverse___redArg(v_a_1887_);
return v___x_1888_;
}
else
{
lean_object* v_head_1889_; lean_object* v_tail_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1899_; 
v_head_1889_ = lean_ctor_get(v_a_1886_, 0);
v_tail_1890_ = lean_ctor_get(v_a_1886_, 1);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_a_1886_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1892_ = v_a_1886_;
v_isShared_1893_ = v_isSharedCheck_1899_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_tail_1890_);
lean_inc(v_head_1889_);
lean_dec(v_a_1886_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1899_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1896_; 
v___x_1894_ = l_Lean_mkLevelParam(v_head_1889_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v_a_1887_);
lean_ctor_set(v___x_1892_, 0, v___x_1894_);
v___x_1896_ = v___x_1892_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_a_1887_);
v___x_1896_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
v_a_1886_ = v_tail_1890_;
v_a_1887_ = v___x_1896_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(lean_object* v_constName_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; 
lean_inc(v_constName_1900_);
v___x_1906_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(v_constName_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1918_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1909_ = v___x_1906_;
v_isShared_1910_ = v_isSharedCheck_1918_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_a_1907_);
lean_dec(v___x_1906_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1918_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_levelParams_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1916_; 
v_levelParams_1911_ = lean_ctor_get(v_a_1907_, 1);
lean_inc(v_levelParams_1911_);
lean_dec(v_a_1907_);
v___x_1912_ = lean_box(0);
v___x_1913_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(v_levelParams_1911_, v___x_1912_);
v___x_1914_ = l_Lean_mkConst(v_constName_1900_, v___x_1913_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1914_);
v___x_1916_ = v___x_1909_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v_constName_1900_);
v_a_1919_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1906_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1906_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1___boxed(lean_object* v_constName_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(v_constName_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_);
lean_dec(v___y_1931_);
lean_dec_ref(v___y_1930_);
lean_dec(v___y_1929_);
lean_dec_ref(v___y_1928_);
return v_res_1933_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1937_; double v___x_1938_; 
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = lean_float_of_nat(v___x_1937_);
return v___x_1938_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4));
v___x_1942_ = l_Lean_stringToMessageData(v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(size_t v_sz_1945_, size_t v_i_1946_, lean_object* v_bs_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
uint8_t v___x_1953_; 
v___x_1953_ = lean_usize_dec_lt(v_i_1946_, v_sz_1945_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1954_, 0, v_bs_1947_);
return v___x_1954_;
}
else
{
lean_object* v_v_1955_; lean_object* v_fst_1956_; lean_object* v_snd_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1993_; 
v_v_1955_ = lean_array_uget(v_bs_1947_, v_i_1946_);
v_fst_1956_ = lean_ctor_get(v_v_1955_, 0);
v_snd_1957_ = lean_ctor_get(v_v_1955_, 1);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_v_1955_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1959_ = v_v_1955_;
v_isShared_1960_ = v_isSharedCheck_1993_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_snd_1957_);
lean_inc(v_fst_1956_);
lean_dec(v_v_1955_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1993_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
lean_object* v___x_1961_; lean_object* v_bs_x27_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_unsigned_to_nat(0u);
v_bs_x27_1962_ = lean_array_uset(v_bs_1947_, v_i_1946_, v___x_1961_);
v___x_1963_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(v_fst_1956_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; double v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v___x_1965_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1));
v___x_1966_ = lean_box(0);
v___x_1967_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2);
v___x_1968_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
v___x_1969_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1969_, 0, v___x_1965_);
lean_ctor_set(v___x_1969_, 1, v___x_1966_);
lean_ctor_set(v___x_1969_, 2, v___x_1968_);
lean_ctor_set_float(v___x_1969_, sizeof(void*)*3, v___x_1967_);
lean_ctor_set_float(v___x_1969_, sizeof(void*)*3 + 8, v___x_1967_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*3 + 16, v___x_1953_);
v___x_1970_ = l_Lean_MessageData_ofConst(v_a_1964_);
v___x_1971_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5);
if (v_isShared_1960_ == 0)
{
lean_ctor_set_tag(v___x_1959_, 7);
lean_ctor_set(v___x_1959_, 1, v___x_1971_);
lean_ctor_set(v___x_1959_, 0, v___x_1970_);
v___x_1973_ = v___x_1959_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; size_t v___x_1980_; size_t v___x_1981_; lean_object* v___x_1982_; 
v___x_1974_ = l_Nat_reprFast(v_snd_1957_);
v___x_1975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
v___x_1976_ = l_Lean_MessageData_ofFormat(v___x_1975_);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1973_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6));
v___x_1979_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1969_);
lean_ctor_set(v___x_1979_, 1, v___x_1977_);
lean_ctor_set(v___x_1979_, 2, v___x_1978_);
v___x_1980_ = ((size_t)1ULL);
v___x_1981_ = lean_usize_add(v_i_1946_, v___x_1980_);
v___x_1982_ = lean_array_uset(v_bs_x27_1962_, v_i_1946_, v___x_1979_);
v_i_1946_ = v___x_1981_;
v_bs_1947_ = v___x_1982_;
goto _start;
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v_bs_x27_1962_);
lean_del_object(v___x_1959_);
lean_dec(v_snd_1957_);
v_a_1985_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1963_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1963_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___boxed(lean_object* v_sz_1994_, lean_object* v_i_1995_, lean_object* v_bs_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
size_t v_sz_boxed_2002_; size_t v_i_boxed_2003_; lean_object* v_res_2004_; 
v_sz_boxed_2002_ = lean_unbox_usize(v_sz_1994_);
lean_dec(v_sz_1994_);
v_i_boxed_2003_ = lean_unbox_usize(v_i_1995_);
lean_dec(v_i_1995_);
v_res_2004_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(v_sz_boxed_2002_, v_i_boxed_2003_, v_bs_1996_, v___y_1997_, v___y_1998_, v___y_1999_, v___y_2000_);
lean_dec(v___y_2000_);
lean_dec_ref(v___y_1999_);
lean_dec(v___y_1998_);
lean_dec_ref(v___y_1997_);
return v_res_2004_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0(void){
_start:
{
lean_object* v___x_2005_; uint8_t v___x_2006_; double v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2005_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
v___x_2006_ = 1;
v___x_2007_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2);
v___x_2008_ = lean_box(0);
v___x_2009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1));
v___x_2010_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v___x_2008_);
lean_ctor_set(v___x_2010_, 2, v___x_2005_);
lean_ctor_set_float(v___x_2010_, sizeof(void*)*3, v___x_2007_);
lean_ctor_set_float(v___x_2010_, sizeof(void*)*3 + 8, v___x_2007_);
lean_ctor_set_uint8(v___x_2010_, sizeof(void*)*3 + 16, v___x_2006_);
return v___x_2010_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2));
v___x_2015_ = l_Lean_MessageData_ofFormat(v___x_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(lean_object* v_thms_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___y_2025_; lean_object* v___x_2048_; lean_object* v_data_2049_; lean_object* v___x_2050_; lean_object* v___y_2052_; lean_object* v___y_2053_; uint8_t v___x_2055_; 
v___x_2022_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_thms_2016_);
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2048_ = lean_array_get_size(v___x_2022_);
v_data_2049_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(v___x_2022_, v___x_2023_, v___x_2048_);
lean_dec_ref(v___x_2022_);
v___x_2050_ = lean_array_get_size(v_data_2049_);
v___x_2055_ = lean_nat_dec_eq(v___x_2050_, v___x_2023_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___y_2059_; uint8_t v___x_2061_; 
v___x_2056_ = lean_unsigned_to_nat(1u);
v___x_2057_ = lean_nat_sub(v___x_2050_, v___x_2056_);
v___x_2061_ = lean_nat_dec_le(v___x_2023_, v___x_2057_);
if (v___x_2061_ == 0)
{
lean_inc(v___x_2057_);
v___y_2059_ = v___x_2057_;
goto v___jp_2058_;
}
else
{
v___y_2059_ = v___x_2023_;
goto v___jp_2058_;
}
v___jp_2058_:
{
uint8_t v___x_2060_; 
v___x_2060_ = lean_nat_dec_le(v___y_2059_, v___x_2057_);
if (v___x_2060_ == 0)
{
lean_dec(v___x_2057_);
lean_inc(v___y_2059_);
v___y_2052_ = v___y_2059_;
v___y_2053_ = v___y_2059_;
goto v___jp_2051_;
}
else
{
v___y_2052_ = v___y_2059_;
v___y_2053_ = v___x_2057_;
goto v___jp_2051_;
}
}
}
else
{
v___y_2025_ = v_data_2049_;
goto v___jp_2024_;
}
v___jp_2024_:
{
size_t v_sz_2026_; size_t v___x_2027_; lean_object* v___x_2028_; 
v_sz_2026_ = lean_array_size(v___y_2025_);
v___x_2027_ = ((size_t)0ULL);
v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(v_sz_2026_, v___x_2027_, v___y_2025_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2039_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2031_ = v___x_2028_;
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_a_2029_);
lean_dec(v___x_2028_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2039_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2033_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0);
v___x_2034_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3);
v___x_2035_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2033_);
lean_ctor_set(v___x_2035_, 1, v___x_2034_);
lean_ctor_set(v___x_2035_, 2, v_a_2029_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2035_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
lean_object* v_a_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2047_; 
v_a_2040_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2042_ = v___x_2028_;
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_a_2040_);
lean_dec(v___x_2028_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2047_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
if (v_isShared_2043_ == 0)
{
v___x_2045_ = v___x_2042_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v_a_2040_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
}
v___jp_2051_:
{
lean_object* v___x_2054_; 
v___x_2054_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v___x_2050_, v_data_2049_, v___y_2052_, v___y_2053_);
lean_dec(v___y_2053_);
v___y_2025_ = v___x_2054_;
goto v___jp_2024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___boxed(lean_object* v_thms_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(v_thms_2062_, v_a_2063_, v_a_2064_, v_a_2065_, v_a_2066_);
lean_dec(v_a_2066_);
lean_dec_ref(v_a_2065_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec_ref(v_thms_2062_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(lean_object* v_00_u03b2_2069_, lean_object* v_m_2070_){
_start:
{
lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_m_2070_);
return v___x_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___boxed(lean_object* v_00_u03b2_2072_, lean_object* v_m_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(v_00_u03b2_2072_, v_m_2073_);
lean_dec_ref(v_m_2073_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(lean_object* v_n_2075_, lean_object* v_as_2076_, lean_object* v_lo_2077_, lean_object* v_hi_2078_, lean_object* v_w_2079_, lean_object* v_hlo_2080_, lean_object* v_hhi_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_2075_, v_as_2076_, v_lo_2077_, v_hi_2078_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___boxed(lean_object* v_n_2083_, lean_object* v_as_2084_, lean_object* v_lo_2085_, lean_object* v_hi_2086_, lean_object* v_w_2087_, lean_object* v_hlo_2088_, lean_object* v_hhi_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(v_n_2083_, v_as_2084_, v_lo_2085_, v_hi_2086_, v_w_2087_, v_hlo_2088_, v_hhi_2089_);
lean_dec(v_hi_2086_);
lean_dec(v_n_2083_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(lean_object* v_00_u03c3_2091_, lean_object* v_00_u03b2_2092_, lean_object* v_map_2093_, lean_object* v_f_2094_, lean_object* v_init_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_map_2093_, v_f_2094_, v_init_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___boxed(lean_object* v_00_u03c3_2097_, lean_object* v_00_u03b2_2098_, lean_object* v_map_2099_, lean_object* v_f_2100_, lean_object* v_init_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(v_00_u03c3_2097_, v_00_u03b2_2098_, v_map_2099_, v_f_2100_, v_init_2101_);
lean_dec_ref(v_map_2099_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(lean_object* v_n_2103_, lean_object* v_lo_2104_, lean_object* v_hi_2105_, lean_object* v_hhi_2106_, lean_object* v_pivot_2107_, lean_object* v_as_2108_, lean_object* v_i_2109_, lean_object* v_k_2110_, lean_object* v_ilo_2111_, lean_object* v_ik_2112_, lean_object* v_w_2113_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_2105_, v_pivot_2107_, v_as_2108_, v_i_2109_, v_k_2110_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___boxed(lean_object* v_n_2115_, lean_object* v_lo_2116_, lean_object* v_hi_2117_, lean_object* v_hhi_2118_, lean_object* v_pivot_2119_, lean_object* v_as_2120_, lean_object* v_i_2121_, lean_object* v_k_2122_, lean_object* v_ilo_2123_, lean_object* v_ik_2124_, lean_object* v_w_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(v_n_2115_, v_lo_2116_, v_hi_2117_, v_hhi_2118_, v_pivot_2119_, v_as_2120_, v_i_2121_, v_k_2122_, v_ilo_2123_, v_ik_2124_, v_w_2125_);
lean_dec_ref(v_pivot_2119_);
lean_dec(v_hi_2117_);
lean_dec(v_lo_2116_);
lean_dec(v_n_2115_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(lean_object* v_map_2127_, lean_object* v_f_2128_, lean_object* v_init_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2128_, v_map_2127_, v_init_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_2131_, lean_object* v_f_2132_, lean_object* v_init_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(v_map_2131_, v_f_2132_, v_init_2133_);
lean_dec_ref(v_map_2131_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2135_, lean_object* v_00_u03b2_2136_, lean_object* v_map_2137_, lean_object* v_f_2138_, lean_object* v_init_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2138_, v_map_2137_, v_init_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_2141_, lean_object* v_00_u03b2_2142_, lean_object* v_map_2143_, lean_object* v_f_2144_, lean_object* v_init_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(v_00_u03c3_2141_, v_00_u03b2_2142_, v_map_2143_, v_f_2144_, v_init_2145_);
lean_dec_ref(v_map_2143_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2147_, lean_object* v_constName_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2155_, lean_object* v_constName_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(v_00_u03b1_2155_, v_constName_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03c3_2163_, lean_object* v_00_u03b1_2164_, lean_object* v_00_u03b2_2165_, lean_object* v_f_2166_, lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2166_, v_x_2167_, v_x_2168_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03c3_2170_, lean_object* v_00_u03b1_2171_, lean_object* v_00_u03b2_2172_, lean_object* v_f_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(v_00_u03c3_2170_, v_00_u03b1_2171_, v_00_u03b2_2172_, v_f_2173_, v_x_2174_, v_x_2175_);
lean_dec_ref(v_x_2174_);
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(lean_object* v_00_u03b1_2177_, lean_object* v_ref_2178_, lean_object* v_constName_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_2178_, v_constName_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b1_2186_, lean_object* v_ref_2187_, lean_object* v_constName_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(v_00_u03b1_2186_, v_ref_2187_, v_constName_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
lean_dec(v_ref_2187_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(lean_object* v_00_u03b1_2195_, lean_object* v_00_u03b2_2196_, lean_object* v_00_u03c3_2197_, lean_object* v_f_2198_, lean_object* v_as_2199_, size_t v_i_2200_, size_t v_stop_2201_, lean_object* v_b_2202_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_2198_, v_as_2199_, v_i_2200_, v_stop_2201_, v_b_2202_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___boxed(lean_object* v_00_u03b1_2204_, lean_object* v_00_u03b2_2205_, lean_object* v_00_u03c3_2206_, lean_object* v_f_2207_, lean_object* v_as_2208_, lean_object* v_i_2209_, lean_object* v_stop_2210_, lean_object* v_b_2211_){
_start:
{
size_t v_i_boxed_2212_; size_t v_stop_boxed_2213_; lean_object* v_res_2214_; 
v_i_boxed_2212_ = lean_unbox_usize(v_i_2209_);
lean_dec(v_i_2209_);
v_stop_boxed_2213_ = lean_unbox_usize(v_stop_2210_);
lean_dec(v_stop_2210_);
v_res_2214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(v_00_u03b1_2204_, v_00_u03b2_2205_, v_00_u03c3_2206_, v_f_2207_, v_as_2208_, v_i_boxed_2212_, v_stop_boxed_2213_, v_b_2211_);
lean_dec_ref(v_as_2208_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(lean_object* v_00_u03c3_2215_, lean_object* v_00_u03b1_2216_, lean_object* v_00_u03b2_2217_, lean_object* v_f_2218_, lean_object* v_keys_2219_, lean_object* v_vals_2220_, lean_object* v_heq_2221_, lean_object* v_i_2222_, lean_object* v_acc_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_2218_, v_keys_2219_, v_vals_2220_, v_i_2222_, v_acc_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03c3_2225_, lean_object* v_00_u03b1_2226_, lean_object* v_00_u03b2_2227_, lean_object* v_f_2228_, lean_object* v_keys_2229_, lean_object* v_vals_2230_, lean_object* v_heq_2231_, lean_object* v_i_2232_, lean_object* v_acc_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(v_00_u03c3_2225_, v_00_u03b1_2226_, v_00_u03b2_2227_, v_f_2228_, v_keys_2229_, v_vals_2230_, v_heq_2231_, v_i_2232_, v_acc_2233_);
lean_dec_ref(v_vals_2230_);
lean_dec_ref(v_keys_2229_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(lean_object* v_00_u03b1_2235_, lean_object* v_ref_2236_, lean_object* v_msg_2237_, lean_object* v_declHint_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_2236_, v_msg_2237_, v_declHint_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___boxed(lean_object* v_00_u03b1_2245_, lean_object* v_ref_2246_, lean_object* v_msg_2247_, lean_object* v_declHint_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(v_00_u03b1_2245_, v_ref_2246_, v_msg_2247_, v_declHint_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v_ref_2246_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(lean_object* v_msg_2255_, lean_object* v_declHint_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_2255_, v_declHint_2256_, v___y_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___boxed(lean_object* v_msg_2263_, lean_object* v_declHint_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(v_msg_2263_, v_declHint_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(lean_object* v_00_u03b1_2271_, lean_object* v_ref_2272_, lean_object* v_msg_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_2272_, v_msg_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___boxed(lean_object* v_00_u03b1_2280_, lean_object* v_ref_2281_, lean_object* v_msg_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v_res_2288_; 
v_res_2288_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(v_00_u03b1_2280_, v_ref_2281_, v_msg_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v_ref_2281_);
return v_res_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_2289_, lean_object* v_msg_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_2290_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_2297_, lean_object* v_msg_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_){
_start:
{
lean_object* v_res_2304_; 
v_res_2304_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(v_00_u03b1_2297_, v_msg_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(lean_object* v_k_2305_, lean_object* v_b_2306_, lean_object* v_c_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; 
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
v___x_2313_ = lean_apply_7(v_k_2305_, v_b_2306_, v_c_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, lean_box(0));
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed(lean_object* v_k_2314_, lean_object* v_b_2315_, lean_object* v_c_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(v_k_2314_, v_b_2315_, v_c_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(lean_object* v_type_2323_, lean_object* v_k_2324_, uint8_t v_cleanupAnnotations_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___f_2331_; uint8_t v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___f_2331_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2331_, 0, v_k_2324_);
v___x_2332_ = 0;
v___x_2333_ = lean_box(0);
v___x_2334_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2332_, v___x_2333_, v_type_2323_, v___f_2331_, v_cleanupAnnotations_2325_, v___x_2332_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
v_a_2343_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2334_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2334_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___boxed(lean_object* v_type_2351_, lean_object* v_k_2352_, lean_object* v_cleanupAnnotations_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2359_; lean_object* v_res_2360_; 
v_cleanupAnnotations_boxed_2359_ = lean_unbox(v_cleanupAnnotations_2353_);
v_res_2360_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v_type_2351_, v_k_2352_, v_cleanupAnnotations_boxed_2359_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
lean_dec(v___y_2357_);
lean_dec_ref(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec_ref(v___y_2354_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(lean_object* v_00_u03b1_2361_, lean_object* v_type_2362_, lean_object* v_k_2363_, uint8_t v_cleanupAnnotations_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v_type_2362_, v_k_2363_, v_cleanupAnnotations_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___boxed(lean_object* v_00_u03b1_2371_, lean_object* v_type_2372_, lean_object* v_k_2373_, lean_object* v_cleanupAnnotations_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2380_; lean_object* v_res_2381_; 
v_cleanupAnnotations_boxed_2380_ = lean_unbox(v_cleanupAnnotations_2374_);
v_res_2381_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(v_00_u03b1_2371_, v_type_2372_, v_k_2373_, v_cleanupAnnotations_boxed_2380_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v_res_2381_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2385_ = lean_box(0);
v___x_2386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1));
v___x_2387_ = l_Lean_mkConst(v___x_2386_, v___x_2385_);
return v___x_2387_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2);
v___x_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(lean_object* v_x_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2396_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3);
v___x_2397_ = 0;
v___x_2398_ = lean_box(0);
v___x_2399_ = l_Lean_Meta_mkFreshExprMVar(v___x_2396_, v___x_2397_, v___x_2398_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2408_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2408_ == 0)
{
v___x_2402_ = v___x_2399_;
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2399_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2408_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2404_ = l_Lean_Expr_mvarId_x21(v_a_2400_);
lean_dec(v_a_2400_);
if (v_isShared_2403_ == 0)
{
lean_ctor_set(v___x_2402_, 0, v___x_2404_);
v___x_2406_ = v___x_2402_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
else
{
lean_object* v_a_2409_; lean_object* v___x_2411_; uint8_t v_isShared_2412_; uint8_t v_isSharedCheck_2416_; 
v_a_2409_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2416_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2411_ = v___x_2399_;
v_isShared_2412_ = v_isSharedCheck_2416_;
goto v_resetjp_2410_;
}
else
{
lean_inc(v_a_2409_);
lean_dec(v___x_2399_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___boxed(lean_object* v_x_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v_res_2423_; 
v_res_2423_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(v_x_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec_ref(v_x_2417_);
return v_res_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2424_, lean_object* v_b_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; 
lean_inc(v___y_2429_);
lean_inc_ref(v___y_2428_);
lean_inc(v___y_2427_);
lean_inc_ref(v___y_2426_);
v___x_2431_ = lean_apply_6(v_k_2424_, v_b_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, lean_box(0));
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2432_, lean_object* v_b_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(v_k_2432_, v_b_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec_ref(v___y_2434_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_name_2440_, uint8_t v_bi_2441_, lean_object* v_type_2442_, lean_object* v_k_2443_, uint8_t v_kind_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___f_2450_; lean_object* v___x_2451_; 
v___f_2450_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2450_, 0, v_k_2443_);
v___x_2451_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2440_, v_bi_2441_, v_type_2442_, v___f_2450_, v_kind_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2451_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2451_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
v_a_2460_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2451_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2451_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_name_2468_, lean_object* v_bi_2469_, lean_object* v_type_2470_, lean_object* v_k_2471_, lean_object* v_kind_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_){
_start:
{
uint8_t v_bi_boxed_2478_; uint8_t v_kind_boxed_2479_; lean_object* v_res_2480_; 
v_bi_boxed_2478_ = lean_unbox(v_bi_2469_);
v_kind_boxed_2479_ = lean_unbox(v_kind_2472_);
v_res_2480_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2468_, v_bi_boxed_2478_, v_type_2470_, v_k_2471_, v_kind_boxed_2479_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(lean_object* v_name_2481_, lean_object* v_type_2482_, lean_object* v_k_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
uint8_t v___x_2489_; uint8_t v___x_2490_; lean_object* v___x_2491_; 
v___x_2489_ = 0;
v___x_2490_ = 0;
v___x_2491_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2481_, v___x_2489_, v_type_2482_, v_k_2483_, v___x_2490_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg___boxed(lean_object* v_name_2492_, lean_object* v_type_2493_, lean_object* v_k_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v_name_2492_, v_type_2493_, v_k_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(lean_object* v___f_2504_, lean_object* v_x_2505_, lean_object* v_type_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1));
v___x_2513_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v___x_2512_, v_type_2506_, v___f_2504_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___boxed(lean_object* v___f_2514_, lean_object* v_x_2515_, lean_object* v_type_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(v___f_2514_, v_x_2515_, v_type_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec_ref(v_x_2515_);
return v_res_2522_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(uint8_t v_suppressElabErrors_2529_, uint8_t v___y_2530_, lean_object* v_x_2531_){
_start:
{
if (lean_obj_tag(v_x_2531_) == 1)
{
lean_object* v_pre_2532_; 
v_pre_2532_ = lean_ctor_get(v_x_2531_, 0);
switch(lean_obj_tag(v_pre_2532_))
{
case 1:
{
lean_object* v_pre_2533_; 
v_pre_2533_ = lean_ctor_get(v_pre_2532_, 0);
switch(lean_obj_tag(v_pre_2533_))
{
case 0:
{
lean_object* v_str_2534_; lean_object* v_str_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; 
v_str_2534_ = lean_ctor_get(v_x_2531_, 1);
v_str_2535_ = lean_ctor_get(v_pre_2532_, 1);
v___x_2536_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_2537_ = lean_string_dec_eq(v_str_2535_, v___x_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_2539_ = lean_string_dec_eq(v_str_2535_, v___x_2538_);
if (v___x_2539_ == 0)
{
return v___x_2539_;
}
else
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0));
v___x_2541_ = lean_string_dec_eq(v_str_2534_, v___x_2540_);
if (v___x_2541_ == 0)
{
return v___x_2541_;
}
else
{
return v_suppressElabErrors_2529_;
}
}
}
else
{
lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2542_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1));
v___x_2543_ = lean_string_dec_eq(v_str_2534_, v___x_2542_);
if (v___x_2543_ == 0)
{
return v___x_2543_;
}
else
{
return v_suppressElabErrors_2529_;
}
}
}
case 1:
{
lean_object* v_pre_2544_; 
v_pre_2544_ = lean_ctor_get(v_pre_2533_, 0);
if (lean_obj_tag(v_pre_2544_) == 0)
{
lean_object* v_str_2545_; lean_object* v_str_2546_; lean_object* v_str_2547_; lean_object* v___x_2548_; uint8_t v___x_2549_; 
v_str_2545_ = lean_ctor_get(v_x_2531_, 1);
v_str_2546_ = lean_ctor_get(v_pre_2532_, 1);
v_str_2547_ = lean_ctor_get(v_pre_2533_, 1);
v___x_2548_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2));
v___x_2549_ = lean_string_dec_eq(v_str_2547_, v___x_2548_);
if (v___x_2549_ == 0)
{
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; uint8_t v___x_2551_; 
v___x_2550_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3));
v___x_2551_ = lean_string_dec_eq(v_str_2546_, v___x_2550_);
if (v___x_2551_ == 0)
{
return v___x_2551_;
}
else
{
lean_object* v___x_2552_; uint8_t v___x_2553_; 
v___x_2552_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4));
v___x_2553_ = lean_string_dec_eq(v_str_2545_, v___x_2552_);
if (v___x_2553_ == 0)
{
return v___x_2553_;
}
else
{
return v_suppressElabErrors_2529_;
}
}
}
}
else
{
return v___y_2530_;
}
}
default: 
{
return v___y_2530_;
}
}
}
case 0:
{
lean_object* v_str_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v_str_2554_ = lean_ctor_get(v_x_2531_, 1);
v___x_2555_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5));
v___x_2556_ = lean_string_dec_eq(v_str_2554_, v___x_2555_);
if (v___x_2556_ == 0)
{
return v___x_2556_;
}
else
{
return v_suppressElabErrors_2529_;
}
}
default: 
{
return v___y_2530_;
}
}
}
else
{
return v___y_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_2557_, lean_object* v___y_2558_, lean_object* v_x_2559_){
_start:
{
uint8_t v_suppressElabErrors_boxed_2560_; uint8_t v___y_5567__boxed_2561_; uint8_t v_res_2562_; lean_object* v_r_2563_; 
v_suppressElabErrors_boxed_2560_ = lean_unbox(v_suppressElabErrors_2557_);
v___y_5567__boxed_2561_ = lean_unbox(v___y_2558_);
v_res_2562_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(v_suppressElabErrors_boxed_2560_, v___y_5567__boxed_2561_, v_x_2559_);
lean_dec(v_x_2559_);
v_r_2563_ = lean_box(v_res_2562_);
return v_r_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(lean_object* v_ref_2564_, lean_object* v_msgData_2565_, uint8_t v_severity_2566_, uint8_t v_isSilent_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; uint8_t v___y_2577_; uint8_t v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v_toCold_2581_; lean_object* v___y_2582_; lean_object* v___y_2611_; lean_object* v___y_2612_; uint8_t v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; uint8_t v___y_2616_; uint8_t v___y_2617_; lean_object* v___y_2618_; uint8_t v___y_2638_; lean_object* v___y_2639_; lean_object* v___y_2640_; uint8_t v___y_2641_; uint8_t v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; uint8_t v___y_2648_; uint8_t v___y_2649_; uint8_t v___y_2650_; uint8_t v___x_2661_; uint8_t v___y_2663_; uint8_t v___y_2664_; uint8_t v___y_2665_; uint8_t v___y_2667_; uint8_t v___x_2675_; 
v___x_2661_ = 2;
v___x_2675_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2566_, v___x_2661_);
if (v___x_2675_ == 0)
{
v___y_2667_ = v___x_2675_;
goto v___jp_2666_;
}
else
{
uint8_t v___x_2676_; 
lean_inc_ref(v_msgData_2565_);
v___x_2676_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2565_);
v___y_2667_ = v___x_2676_;
goto v___jp_2666_;
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
lean_ctor_set(v___x_2586_, 1, v___y_2580_);
lean_inc_ref(v___y_2576_);
lean_inc_ref(v___y_2575_);
v___x_2587_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2587_, 0, v___y_2575_);
lean_ctor_set(v___x_2587_, 1, v___y_2579_);
lean_ctor_set(v___x_2587_, 2, v___y_2574_);
lean_ctor_set(v___x_2587_, 3, v___y_2576_);
lean_ctor_set(v___x_2587_, 4, v___x_2586_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*5, v___y_2577_);
lean_ctor_set_uint8(v___x_2587_, sizeof(void*)*5 + 1, v___y_2578_);
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
v_fileName_2619_ = lean_ctor_get(v___y_2614_, 0);
v_fileMap_2620_ = lean_ctor_get(v___y_2614_, 1);
v___x_2621_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2565_);
v___x_2622_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v___x_2621_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
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
v___x_2627_ = l_Lean_FileMap_toPosition(v_fileMap_2620_, v___y_2615_);
lean_dec(v___y_2615_);
v___x_2628_ = l_Lean_FileMap_toPosition(v_fileMap_2620_, v___y_2618_);
lean_dec(v___y_2618_);
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
v___x_2630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
if (v___y_2613_ == 0)
{
lean_del_object(v___x_2625_);
lean_dec_ref(v___y_2612_);
v___y_2574_ = v___x_2629_;
v___y_2575_ = v_fileName_2619_;
v___y_2576_ = v___x_2630_;
v___y_2577_ = v___y_2616_;
v___y_2578_ = v___y_2617_;
v___y_2579_ = v___x_2627_;
v___y_2580_ = v_a_2623_;
v_toCold_2581_ = v___y_2611_;
v___y_2582_ = v___y_2571_;
goto v___jp_2573_;
}
else
{
uint8_t v___x_2631_; 
lean_inc(v_a_2623_);
v___x_2631_ = l_Lean_MessageData_hasTag(v___y_2612_, v_a_2623_);
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
v___y_2574_ = v___x_2629_;
v___y_2575_ = v_fileName_2619_;
v___y_2576_ = v___x_2630_;
v___y_2577_ = v___y_2616_;
v___y_2578_ = v___y_2617_;
v___y_2579_ = v___x_2627_;
v___y_2580_ = v_a_2623_;
v_toCold_2581_ = v___y_2611_;
v___y_2582_ = v___y_2571_;
goto v___jp_2573_;
}
}
}
}
v___jp_2637_:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lean_Syntax_getTailPos_x3f(v___y_2643_, v___y_2641_);
lean_dec(v___y_2643_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_inc(v___y_2644_);
v___y_2611_ = v___y_2639_;
v___y_2612_ = v___y_2640_;
v___y_2613_ = v___y_2638_;
v___y_2614_ = v___y_2639_;
v___y_2615_ = v___y_2644_;
v___y_2616_ = v___y_2641_;
v___y_2617_ = v___y_2642_;
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
v___y_2614_ = v___y_2639_;
v___y_2615_ = v___y_2644_;
v___y_2616_ = v___y_2641_;
v___y_2617_ = v___y_2642_;
v___y_2618_ = v_val_2646_;
goto v___jp_2610_;
}
}
v___jp_2647_:
{
lean_object* v_toCold_2651_; lean_object* v_ref_2652_; uint8_t v_suppressElabErrors_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___f_2656_; lean_object* v_ref_2657_; lean_object* v___x_2658_; 
v_toCold_2651_ = lean_ctor_get(v___y_2570_, 0);
v_ref_2652_ = lean_ctor_get(v___y_2570_, 2);
v_suppressElabErrors_2653_ = lean_ctor_get_uint8(v___y_2570_, sizeof(void*)*3 + 2);
v___x_2654_ = lean_box(v_suppressElabErrors_2653_);
v___x_2655_ = lean_box(v___y_2648_);
v___f_2656_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2656_, 0, v___x_2654_);
lean_closure_set(v___f_2656_, 1, v___x_2655_);
v_ref_2657_ = l_Lean_replaceRef(v_ref_2564_, v_ref_2652_);
v___x_2658_ = l_Lean_Syntax_getPos_x3f(v_ref_2657_, v___y_2649_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v___x_2659_; 
v___x_2659_ = lean_unsigned_to_nat(0u);
v___y_2638_ = v_suppressElabErrors_2653_;
v___y_2639_ = v_toCold_2651_;
v___y_2640_ = v___f_2656_;
v___y_2641_ = v___y_2649_;
v___y_2642_ = v___y_2650_;
v___y_2643_ = v_ref_2657_;
v___y_2644_ = v___x_2659_;
goto v___jp_2637_;
}
else
{
lean_object* v_val_2660_; 
v_val_2660_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_val_2660_);
lean_dec_ref_known(v___x_2658_, 1);
v___y_2638_ = v_suppressElabErrors_2653_;
v___y_2639_ = v_toCold_2651_;
v___y_2640_ = v___f_2656_;
v___y_2641_ = v___y_2649_;
v___y_2642_ = v___y_2650_;
v___y_2643_ = v_ref_2657_;
v___y_2644_ = v_val_2660_;
goto v___jp_2637_;
}
}
v___jp_2662_:
{
if (v___y_2665_ == 0)
{
v___y_2648_ = v___y_2663_;
v___y_2649_ = v___y_2664_;
v___y_2650_ = v_severity_2566_;
goto v___jp_2647_;
}
else
{
v___y_2648_ = v___y_2663_;
v___y_2649_ = v___y_2664_;
v___y_2650_ = v___x_2661_;
goto v___jp_2647_;
}
}
v___jp_2666_:
{
if (v___y_2667_ == 0)
{
uint8_t v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = 1;
v___x_2669_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2566_, v___x_2668_);
if (v___x_2669_ == 0)
{
v___y_2663_ = v___y_2667_;
v___y_2664_ = v___y_2667_;
v___y_2665_ = v___x_2669_;
goto v___jp_2662_;
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; 
v___x_2670_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2570_);
v___x_2671_ = l_Lean_warningAsError;
v___x_2672_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v___x_2670_, v___x_2671_);
lean_dec_ref(v___x_2670_);
v___y_2663_ = v___y_2667_;
v___y_2664_ = v___y_2667_;
v___y_2665_ = v___x_2672_;
goto v___jp_2662_;
}
}
else
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec_ref(v_msgData_2565_);
v___x_2673_ = lean_box(0);
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2673_);
return v___x_2674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_ref_2677_, lean_object* v_msgData_2678_, lean_object* v_severity_2679_, lean_object* v_isSilent_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
uint8_t v_severity_boxed_2686_; uint8_t v_isSilent_boxed_2687_; lean_object* v_res_2688_; 
v_severity_boxed_2686_ = lean_unbox(v_severity_2679_);
v_isSilent_boxed_2687_ = lean_unbox(v_isSilent_2680_);
v_res_2688_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(v_ref_2677_, v_msgData_2678_, v_severity_boxed_2686_, v_isSilent_boxed_2687_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
lean_dec(v___y_2682_);
lean_dec_ref(v___y_2681_);
lean_dec(v_ref_2677_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(lean_object* v_msgData_2689_, uint8_t v_severity_2690_, uint8_t v_isSilent_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_ref_2697_; lean_object* v___x_2698_; 
v_ref_2697_ = lean_ctor_get(v___y_2694_, 2);
v___x_2698_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(v_ref_2697_, v_msgData_2689_, v_severity_2690_, v_isSilent_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4___boxed(lean_object* v_msgData_2699_, lean_object* v_severity_2700_, lean_object* v_isSilent_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
uint8_t v_severity_boxed_2707_; uint8_t v_isSilent_boxed_2708_; lean_object* v_res_2709_; 
v_severity_boxed_2707_ = lean_unbox(v_severity_2700_);
v_isSilent_boxed_2708_ = lean_unbox(v_isSilent_2701_);
v_res_2709_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(v_msgData_2699_, v_severity_boxed_2707_, v_isSilent_boxed_2708_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(lean_object* v_msgData_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
uint8_t v___x_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; 
v___x_2716_ = 0;
v___x_2717_ = 0;
v___x_2718_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(v_msgData_2710_, v___x_2716_, v___x_2717_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3___boxed(lean_object* v_msgData_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v_msgData_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(lean_object* v_constName_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; lean_object* v_env_2733_; uint8_t v___x_2734_; lean_object* v___x_2735_; 
v___x_2732_ = lean_st_ref_get(v___y_2730_);
v_env_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc_ref(v_env_2733_);
lean_dec(v___x_2732_);
v___x_2734_ = 0;
lean_inc(v_constName_2726_);
v___x_2735_ = l_Lean_Environment_find_x3f(v_env_2733_, v_constName_2726_, v___x_2734_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
return v___x_2736_;
}
else
{
lean_object* v_val_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec(v_constName_2726_);
v_val_2737_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2735_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_val_2737_);
lean_dec(v___x_2735_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
lean_ctor_set_tag(v___x_2739_, 0);
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_val_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1___boxed(lean_object* v_constName_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(v_constName_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2751_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(lean_object* v_declName_2770_, lean_object* v_params_2771_, lean_object* v_a_2772_, lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v___f_2777_; lean_object* v___x_2778_; 
v___f_2777_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1));
lean_inc(v_declName_2770_);
v___x_2778_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(v_declName_2770_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; uint8_t v___x_2781_; lean_object* v___x_2782_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = l_Lean_ConstantInfo_type(v_a_2779_);
lean_dec(v_a_2779_);
v___x_2781_ = 0;
v___x_2782_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v___x_2780_, v___f_2777_, v___x_2781_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
lean_inc_ref(v_params_2771_);
v___x_2784_ = l_Lean_Meta_Grind_main(v_a_2783_, v_params_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2873_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2787_ = v___x_2784_;
v_isShared_2788_ = v_isSharedCheck_2873_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2784_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2873_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v_counters_2789_; lean_object* v_config_2790_; lean_object* v_thm_2791_; lean_object* v_instances_2792_; lean_object* v_min_2793_; lean_object* v_detailed_2794_; lean_object* v___x_2795_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; uint8_t v___x_2831_; 
v_counters_2789_ = lean_ctor_get(v_a_2785_, 3);
lean_inc_ref(v_counters_2789_);
lean_dec(v_a_2785_);
v_config_2790_ = lean_ctor_get(v_params_2771_, 0);
lean_inc_ref(v_config_2790_);
lean_dec_ref(v_params_2771_);
v_thm_2791_ = lean_ctor_get(v_counters_2789_, 0);
lean_inc_ref(v_thm_2791_);
lean_dec_ref(v_counters_2789_);
v_instances_2792_ = lean_ctor_get(v_config_2790_, 4);
lean_inc(v_instances_2792_);
v_min_2793_ = lean_ctor_get(v_config_2790_, 11);
lean_inc(v_min_2793_);
v_detailed_2794_ = lean_ctor_get(v_config_2790_, 12);
lean_inc(v_detailed_2794_);
lean_dec_ref(v_config_2790_);
v___x_2795_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(v_thm_2791_);
v___x_2831_ = lean_nat_dec_lt(v_min_2793_, v___x_2795_);
if (v___x_2831_ == 0)
{
lean_dec(v_instances_2792_);
v___y_2803_ = v_a_2772_;
v___y_2804_ = v_a_2773_;
v___y_2805_ = v_a_2774_;
v___y_2806_ = v_a_2775_;
goto v___jp_2802_;
}
else
{
uint8_t v___x_2832_; 
v___x_2832_ = lean_nat_dec_le(v_instances_2792_, v___x_2795_);
lean_dec(v_instances_2792_);
if (v___x_2832_ == 0)
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2833_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5);
lean_inc(v_declName_2770_);
v___x_2834_ = l_Lean_MessageData_ofName(v_declName_2770_);
v___x_2835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2835_, 0, v___x_2833_);
lean_ctor_set(v___x_2835_, 1, v___x_2834_);
v___x_2836_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7);
v___x_2837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2837_, 0, v___x_2835_);
lean_ctor_set(v___x_2837_, 1, v___x_2836_);
lean_inc(v___x_2795_);
v___x_2838_ = l_Nat_reprFast(v___x_2795_);
v___x_2839_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2839_, 0, v___x_2838_);
v___x_2840_ = l_Lean_MessageData_ofFormat(v___x_2839_);
v___x_2841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2841_, 0, v___x_2837_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9);
v___x_2843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2841_);
lean_ctor_set(v___x_2843_, 1, v___x_2842_);
v___x_2844_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2843_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_dec_ref_known(v___x_2844_, 1);
v___y_2803_ = v_a_2772_;
v___y_2804_ = v_a_2773_;
v___y_2805_ = v_a_2774_;
v___y_2806_ = v_a_2775_;
goto v___jp_2802_;
}
else
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
lean_dec(v___x_2795_);
lean_dec(v_detailed_2794_);
lean_dec(v_min_2793_);
lean_dec_ref(v_thm_2791_);
lean_del_object(v___x_2787_);
lean_dec(v_declName_2770_);
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2852_ == 0)
{
v___x_2847_ = v___x_2844_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___x_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
}
else
{
lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2853_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5);
lean_inc(v_declName_2770_);
v___x_2854_ = l_Lean_MessageData_ofName(v_declName_2770_);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2853_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11);
v___x_2857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2855_);
lean_ctor_set(v___x_2857_, 1, v___x_2856_);
lean_inc(v___x_2795_);
v___x_2858_ = l_Nat_reprFast(v___x_2795_);
v___x_2859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
v___x_2860_ = l_Lean_MessageData_ofFormat(v___x_2859_);
v___x_2861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2857_);
lean_ctor_set(v___x_2861_, 1, v___x_2860_);
v___x_2862_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9);
v___x_2863_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v___x_2862_);
v___x_2864_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2863_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_dec_ref_known(v___x_2864_, 1);
v___y_2803_ = v_a_2772_;
v___y_2804_ = v_a_2773_;
v___y_2805_ = v_a_2774_;
v___y_2806_ = v_a_2775_;
goto v___jp_2802_;
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v___x_2795_);
lean_dec(v_detailed_2794_);
lean_dec(v_min_2793_);
lean_dec_ref(v_thm_2791_);
lean_del_object(v___x_2787_);
lean_dec(v_declName_2770_);
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
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
}
v___jp_2796_:
{
uint8_t v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2797_ = lean_nat_dec_lt(v_min_2793_, v___x_2795_);
lean_dec(v___x_2795_);
lean_dec(v_min_2793_);
v___x_2798_ = lean_box(v___x_2797_);
if (v_isShared_2788_ == 0)
{
lean_ctor_set(v___x_2787_, 0, v___x_2798_);
v___x_2800_ = v___x_2787_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
v___jp_2802_:
{
uint8_t v___x_2807_; 
v___x_2807_ = lean_nat_dec_lt(v_detailed_2794_, v___x_2795_);
lean_dec(v_detailed_2794_);
if (v___x_2807_ == 0)
{
lean_dec_ref(v_thm_2791_);
lean_dec(v_declName_2770_);
goto v___jp_2796_;
}
else
{
lean_object* v___x_2808_; 
v___x_2808_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(v_thm_2791_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec_ref(v_thm_2791_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = l_Lean_MessageData_ofName(v_declName_2770_);
v___x_2811_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3);
v___x_2812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2811_);
v___x_2813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_ctor_set(v___x_2813_, 1, v_a_2809_);
v___x_2814_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2813_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_dec_ref_known(v___x_2814_, 1);
goto v___jp_2796_;
}
else
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2822_; 
lean_dec(v___x_2795_);
lean_dec(v_min_2793_);
lean_del_object(v___x_2787_);
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2822_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2820_; 
if (v_isShared_2818_ == 0)
{
v___x_2820_ = v___x_2817_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2815_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
return v___x_2820_;
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec(v___x_2795_);
lean_dec(v_min_2793_);
lean_del_object(v___x_2787_);
lean_dec(v_declName_2770_);
v_a_2823_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2830_ == 0)
{
v___x_2825_ = v___x_2808_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_inc(v_a_2823_);
lean_dec(v___x_2808_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2823_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec_ref(v_params_2771_);
lean_dec(v_declName_2770_);
v_a_2874_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2784_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2784_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec_ref(v_params_2771_);
lean_dec(v_declName_2770_);
v_a_2882_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2782_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2782_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec_ref(v_params_2771_);
lean_dec(v_declName_2770_);
v_a_2890_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2778_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2778_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___boxed(lean_object* v_declName_2898_, lean_object* v_params_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_declName_2898_, v_params_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
lean_dec(v_a_2903_);
lean_dec_ref(v_a_2902_);
lean_dec(v_a_2901_);
lean_dec_ref(v_a_2900_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_2906_, lean_object* v_name_2907_, uint8_t v_bi_2908_, lean_object* v_type_2909_, lean_object* v_k_2910_, uint8_t v_kind_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2907_, v_bi_2908_, v_type_2909_, v_k_2910_, v_kind_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2918_, lean_object* v_name_2919_, lean_object* v_bi_2920_, lean_object* v_type_2921_, lean_object* v_k_2922_, lean_object* v_kind_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
uint8_t v_bi_boxed_2929_; uint8_t v_kind_boxed_2930_; lean_object* v_res_2931_; 
v_bi_boxed_2929_ = lean_unbox(v_bi_2920_);
v_kind_boxed_2930_ = lean_unbox(v_kind_2923_);
v_res_2931_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(v_00_u03b1_2918_, v_name_2919_, v_bi_boxed_2929_, v_type_2921_, v_k_2922_, v_kind_boxed_2930_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
lean_dec(v___y_2925_);
lean_dec_ref(v___y_2924_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(lean_object* v_00_u03b1_2932_, lean_object* v_name_2933_, lean_object* v_type_2934_, lean_object* v_k_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v_name_2933_, v_type_2934_, v_k_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___boxed(lean_object* v_00_u03b1_2942_, lean_object* v_name_2943_, lean_object* v_type_2944_, lean_object* v_k_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(v_00_u03b1_2942_, v_name_2943_, v_type_2944_, v_k_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg(){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0);
v___x_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg___boxed(lean_object* v___y_2955_){
_start:
{
lean_object* v_res_2956_; 
v_res_2956_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v_res_2956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(lean_object* v_00_u03b1_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___boxed(lean_object* v_00_u03b1_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(v_00_u03b1_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(lean_object* v_a_2975_, lean_object* v_as_2976_, size_t v_sz_2977_, size_t v_i_2978_, uint8_t v_b_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
uint8_t v_a_2986_; uint8_t v_addCodeAction_2990_; 
v_addCodeAction_2990_ = lean_usize_dec_lt(v_i_2978_, v_sz_2977_);
if (v_addCodeAction_2990_ == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
lean_dec_ref(v_a_2975_);
v___x_2991_ = lean_box(v_b_2979_);
v___x_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2992_, 0, v___x_2991_);
return v___x_2992_;
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_a_2993_ = lean_array_uget_borrowed(v_as_2976_, v_i_2978_);
v___x_2994_ = lean_box(0);
lean_inc(v_a_2993_);
v___x_2995_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_2993_, v___x_2994_, v___y_2982_, v___y_2983_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2997_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_a_2996_);
lean_dec_ref_known(v___x_2995_, 1);
lean_inc_ref(v_a_2975_);
v___x_2997_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_a_2996_, v_a_2975_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; uint8_t v___x_2999_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = lean_unbox(v_a_2998_);
lean_dec(v_a_2998_);
if (v___x_2999_ == 0)
{
v_a_2986_ = v_b_2979_;
goto v___jp_2985_;
}
else
{
v_a_2986_ = v_addCodeAction_2990_;
goto v___jp_2985_;
}
}
else
{
lean_dec_ref(v_a_2975_);
return v___x_2997_;
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref(v_a_2975_);
v_a_3000_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2995_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2995_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
v___jp_2985_:
{
size_t v___x_2987_; size_t v___x_2988_; 
v___x_2987_ = ((size_t)1ULL);
v___x_2988_ = lean_usize_add(v_i_2978_, v___x_2987_);
v_i_2978_ = v___x_2988_;
v_b_2979_ = v_a_2986_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg___boxed(lean_object* v_a_3008_, lean_object* v_as_3009_, lean_object* v_sz_3010_, lean_object* v_i_3011_, lean_object* v_b_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_){
_start:
{
size_t v_sz_boxed_3018_; size_t v_i_boxed_3019_; uint8_t v_b_boxed_3020_; lean_object* v_res_3021_; 
v_sz_boxed_3018_ = lean_unbox_usize(v_sz_3010_);
lean_dec(v_sz_3010_);
v_i_boxed_3019_ = lean_unbox_usize(v_i_3011_);
lean_dec(v_i_3011_);
v_b_boxed_3020_ = lean_unbox(v_b_3012_);
v_res_3021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_3008_, v_as_3009_, v_sz_boxed_3018_, v_i_boxed_3019_, v_b_boxed_3020_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_);
lean_dec(v___y_3016_);
lean_dec_ref(v___y_3015_);
lean_dec(v___y_3014_);
lean_dec_ref(v___y_3013_);
lean_dec_ref(v_as_3009_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(size_t v_sz_3029_, size_t v_i_3030_, lean_object* v_bs_3031_){
_start:
{
uint8_t v___x_3032_; 
v___x_3032_ = lean_usize_dec_lt(v_i_3030_, v_sz_3029_);
if (v___x_3032_ == 0)
{
lean_object* v___x_3033_; 
v___x_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3033_, 0, v_bs_3031_);
return v___x_3033_;
}
else
{
lean_object* v_v_3034_; lean_object* v___x_3035_; uint8_t v___x_3036_; 
v_v_3034_ = lean_array_uget(v_bs_3031_, v_i_3030_);
v___x_3035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2));
lean_inc(v_v_3034_);
v___x_3036_ = l_Lean_Syntax_isOfKind(v_v_3034_, v___x_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; 
lean_dec(v_v_3034_);
lean_dec_ref(v_bs_3031_);
v___x_3037_ = lean_box(0);
return v___x_3037_;
}
else
{
lean_object* v___x_3038_; lean_object* v_bs_x27_3039_; size_t v___x_3040_; size_t v___x_3041_; lean_object* v___x_3042_; 
v___x_3038_ = lean_unsigned_to_nat(0u);
v_bs_x27_3039_ = lean_array_uset(v_bs_3031_, v_i_3030_, v___x_3038_);
v___x_3040_ = ((size_t)1ULL);
v___x_3041_ = lean_usize_add(v_i_3030_, v___x_3040_);
v___x_3042_ = lean_array_uset(v_bs_x27_3039_, v_i_3030_, v_v_3034_);
v_i_3030_ = v___x_3041_;
v_bs_3031_ = v___x_3042_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___boxed(lean_object* v_sz_3044_, lean_object* v_i_3045_, lean_object* v_bs_3046_){
_start:
{
size_t v_sz_boxed_3047_; size_t v_i_boxed_3048_; lean_object* v_res_3049_; 
v_sz_boxed_3047_ = lean_unbox_usize(v_sz_3044_);
lean_dec(v_sz_3044_);
v_i_boxed_3048_ = lean_unbox_usize(v_i_3045_);
lean_dec(v_i_3045_);
v_res_3049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_boxed_3047_, v_i_boxed_3048_, v_bs_3046_);
return v_res_3049_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9));
v___x_3066_ = l_String_toRawSubstring_x27(v___x_3065_);
return v___x_3066_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13(void){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l_Array_mkArray0___redArg();
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(uint8_t v___x_3073_, lean_object* v_stx_3074_, lean_object* v___x_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
if (v___x_3073_ == 0)
{
lean_object* v___x_3083_; 
lean_dec_ref(v___x_3075_);
lean_dec(v_stx_3074_);
v___x_3083_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3083_;
}
else
{
lean_object* v_toCold_3084_; lean_object* v_currRecDepth_3085_; lean_object* v_ref_3086_; uint16_t v_optionFlags_3087_; uint8_t v_suppressElabErrors_3088_; uint8_t v_isRecordingDeps_3089_; lean_object* v_fileName_3090_; lean_object* v_fileMap_3091_; lean_object* v_options_3092_; lean_object* v_maxRecDepth_3093_; lean_object* v_currNamespace_3094_; lean_object* v_openDecls_3095_; lean_object* v_initHeartbeats_3096_; lean_object* v_quotContext_3097_; lean_object* v_currMacroScope_3098_; lean_object* v_cancelTk_x3f_3099_; lean_object* v_inheritedTraceOptions_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; size_t v_sz_3104_; size_t v___x_3105_; lean_object* v___x_3106_; 
v_toCold_3084_ = lean_ctor_get(v___y_3080_, 0);
v_currRecDepth_3085_ = lean_ctor_get(v___y_3080_, 1);
v_ref_3086_ = lean_ctor_get(v___y_3080_, 2);
v_optionFlags_3087_ = lean_ctor_get_uint16(v___y_3080_, sizeof(void*)*3);
v_suppressElabErrors_3088_ = lean_ctor_get_uint8(v___y_3080_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3089_ = lean_ctor_get_uint8(v___y_3080_, sizeof(void*)*3 + 3);
v_fileName_3090_ = lean_ctor_get(v_toCold_3084_, 0);
v_fileMap_3091_ = lean_ctor_get(v_toCold_3084_, 1);
v_options_3092_ = lean_ctor_get(v_toCold_3084_, 2);
v_maxRecDepth_3093_ = lean_ctor_get(v_toCold_3084_, 3);
v_currNamespace_3094_ = lean_ctor_get(v_toCold_3084_, 4);
v_openDecls_3095_ = lean_ctor_get(v_toCold_3084_, 5);
v_initHeartbeats_3096_ = lean_ctor_get(v_toCold_3084_, 6);
v_quotContext_3097_ = lean_ctor_get(v_toCold_3084_, 8);
v_currMacroScope_3098_ = lean_ctor_get(v_toCold_3084_, 9);
v_cancelTk_x3f_3099_ = lean_ctor_get(v_toCold_3084_, 10);
v_inheritedTraceOptions_3100_ = lean_ctor_get(v_toCold_3084_, 11);
v___x_3101_ = lean_unsigned_to_nat(2u);
v___x_3102_ = l_Lean_Syntax_getArg(v_stx_3074_, v___x_3101_);
v___x_3103_ = l_Lean_Syntax_getArgs(v___x_3102_);
lean_dec(v___x_3102_);
v_sz_3104_ = lean_array_size(v___x_3103_);
v___x_3105_ = ((size_t)0ULL);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_3104_, v___x_3105_, v___x_3103_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v___x_3107_; 
lean_dec_ref(v___x_3075_);
lean_dec(v_stx_3074_);
v___x_3107_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3107_;
}
else
{
lean_object* v_val_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v_ids_3114_; lean_object* v___x_3115_; 
v_val_3108_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_val_3108_);
lean_dec_ref_known(v___x_3106_, 1);
v___x_3109_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inheritedTraceOptions_3100_);
lean_inc(v_cancelTk_x3f_3099_);
lean_inc(v_currMacroScope_3098_);
lean_inc(v_quotContext_3097_);
lean_inc(v_initHeartbeats_3096_);
lean_inc(v_openDecls_3095_);
lean_inc(v_currNamespace_3094_);
lean_inc(v_maxRecDepth_3093_);
lean_inc_ref(v_options_3092_);
lean_inc_ref(v_fileMap_3091_);
lean_inc_ref(v_fileName_3090_);
v___x_3110_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3110_, 0, v_fileName_3090_);
lean_ctor_set(v___x_3110_, 1, v_fileMap_3091_);
lean_ctor_set(v___x_3110_, 2, v_options_3092_);
lean_ctor_set(v___x_3110_, 3, v_maxRecDepth_3093_);
lean_ctor_set(v___x_3110_, 4, v_currNamespace_3094_);
lean_ctor_set(v___x_3110_, 5, v_openDecls_3095_);
lean_ctor_set(v___x_3110_, 6, v_initHeartbeats_3096_);
lean_ctor_set(v___x_3110_, 7, v___x_3109_);
lean_ctor_set(v___x_3110_, 8, v_quotContext_3097_);
lean_ctor_set(v___x_3110_, 9, v_currMacroScope_3098_);
lean_ctor_set(v___x_3110_, 10, v_cancelTk_x3f_3099_);
lean_ctor_set(v___x_3110_, 11, v_inheritedTraceOptions_3100_);
lean_inc(v_ref_3086_);
lean_inc(v_currRecDepth_3085_);
v___x_3111_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
lean_ctor_set(v___x_3111_, 1, v_currRecDepth_3085_);
lean_ctor_set(v___x_3111_, 2, v_ref_3086_);
lean_ctor_set_uint16(v___x_3111_, sizeof(void*)*3, v_optionFlags_3087_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*3 + 2, v_suppressElabErrors_3088_);
lean_ctor_set_uint8(v___x_3111_, sizeof(void*)*3 + 3, v_isRecordingDeps_3089_);
v___x_3112_ = lean_unsigned_to_nat(3u);
v___x_3113_ = l_Lean_Syntax_getArg(v_stx_3074_, v___x_3112_);
v_ids_3114_ = l_Lean_Syntax_getArgs(v___x_3113_);
lean_dec(v___x_3113_);
v___x_3115_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_val_3108_, v___y_3076_, v___x_3111_, v___y_3081_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3117_; 
v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
lean_inc(v_a_3116_);
lean_dec_ref_known(v___x_3115_, 1);
v___x_3117_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_a_3116_, v___y_3078_, v___y_3079_, v___x_3111_, v___y_3081_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; uint8_t v___x_3119_; size_t v_sz_3120_; lean_object* v___x_3121_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_a_3118_);
lean_dec_ref_known(v___x_3117_, 1);
v___x_3119_ = 0;
v_sz_3120_ = lean_array_size(v_ids_3114_);
v___x_3121_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_3118_, v_ids_3114_, v_sz_3120_, v___x_3105_, v___x_3119_, v___y_3078_, v___y_3079_, v___x_3111_, v___y_3081_);
lean_dec_ref(v_ids_3114_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3170_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3170_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3170_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3170_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
uint8_t v___x_3126_; 
v___x_3126_ = lean_unbox(v_a_3122_);
lean_dec(v_a_3122_);
if (v___x_3126_ == 0)
{
lean_object* v___x_3127_; lean_object* v___x_3129_; 
lean_dec_ref_known(v___x_3111_, 3);
lean_dec_ref(v___x_3075_);
lean_dec(v_stx_3074_);
v___x_3127_ = lean_box(0);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3127_);
v___x_3129_ = v___x_3124_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3127_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
else
{
lean_object* v___x_3131_; lean_object* v_map_3132_; lean_object* v___x_3133_; uint8_t v___y_3135_; lean_object* v___x_3163_; 
v___x_3131_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___x_3111_);
v_map_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_map_3132_);
lean_dec_ref(v___x_3131_);
v___x_3133_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3));
v___x_3163_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3132_, v___x_3133_);
lean_dec(v_map_3132_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_del_object(v___x_3124_);
v___y_3135_ = v___x_3119_;
goto v___jp_3134_;
}
else
{
lean_object* v_val_3164_; 
v_val_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_val_3164_);
lean_dec_ref_known(v___x_3163_, 1);
if (lean_obj_tag(v_val_3164_) == 1)
{
uint8_t v_v_3165_; 
v_v_3165_ = lean_ctor_get_uint8(v_val_3164_, 0);
lean_dec_ref_known(v_val_3164_, 0);
if (v_v_3165_ == 0)
{
lean_del_object(v___x_3124_);
v___y_3135_ = v_v_3165_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
lean_dec_ref_known(v___x_3111_, 3);
lean_dec_ref(v___x_3075_);
lean_dec(v_stx_3074_);
v___x_3166_ = lean_box(0);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3166_);
v___x_3168_ = v___x_3124_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
else
{
lean_dec(v_val_3164_);
lean_del_object(v___x_3124_);
v___y_3135_ = v___x_3119_;
goto v___jp_3134_;
}
}
v___jp_3134_:
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3136_ = l_Lean_SourceInfo_fromRef(v_ref_3086_, v___y_3135_);
v___x_3137_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5));
v___x_3138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0));
v___x_3139_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6));
v___x_3140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7));
lean_inc_ref(v___x_3075_);
v___x_3141_ = l_Lean_Name_mkStr4(v___x_3075_, v___x_3138_, v___x_3139_, v___x_3140_);
v___x_3142_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8));
v___x_3143_ = l_Lean_Name_mkStr4(v___x_3075_, v___x_3138_, v___x_3139_, v___x_3142_);
lean_inc_n(v___x_3136_, 6);
v___x_3144_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3136_);
lean_ctor_set(v___x_3144_, 1, v___x_3142_);
v___x_3145_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10);
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3136_);
lean_ctor_set(v___x_3147_, 1, v___x_3145_);
lean_ctor_set(v___x_3147_, 2, v___x_3133_);
lean_ctor_set(v___x_3147_, 3, v___x_3146_);
v___x_3148_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12));
v___x_3149_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13);
v___x_3150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3136_);
lean_ctor_set(v___x_3150_, 1, v___x_3148_);
lean_ctor_set(v___x_3150_, 2, v___x_3149_);
v___x_3151_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14));
v___x_3152_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3152_, 0, v___x_3136_);
lean_ctor_set(v___x_3152_, 1, v___x_3151_);
v___x_3153_ = l_Lean_Syntax_node4(v___x_3136_, v___x_3143_, v___x_3144_, v___x_3147_, v___x_3150_, v___x_3152_);
v___x_3154_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3136_);
lean_ctor_set(v___x_3154_, 1, v___x_3140_);
lean_inc(v_stx_3074_);
v___x_3155_ = l_Lean_Syntax_node3(v___x_3136_, v___x_3141_, v___x_3153_, v___x_3154_, v_stx_3074_);
v___x_3156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3137_);
lean_ctor_set(v___x_3156_, 1, v___x_3155_);
v___x_3157_ = lean_box(0);
v___x_3158_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3156_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
lean_ctor_set(v___x_3158_, 2, v___x_3157_);
lean_ctor_set(v___x_3158_, 3, v___x_3157_);
lean_ctor_set(v___x_3158_, 4, v___x_3157_);
lean_ctor_set(v___x_3158_, 5, v___x_3157_);
v___x_3159_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15));
v___x_3160_ = 4;
v___x_3161_ = l_Lean_MessageData_nil;
v___x_3162_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_3074_, v___x_3158_, v___x_3157_, v___x_3159_, v___x_3157_, v___x_3160_, v___x_3161_, v___x_3111_, v___y_3081_);
lean_dec_ref_known(v___x_3111_, 3);
return v___x_3162_;
}
}
}
}
else
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3178_; 
lean_dec_ref_known(v___x_3111_, 3);
lean_dec_ref(v___x_3075_);
lean_dec(v_stx_3074_);
v_a_3171_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3173_ = v___x_3121_;
v_isShared_3174_ = v_isSharedCheck_3178_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___x_3121_);
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
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec_ref(v_ids_3114_);
lean_dec_ref_known(v___x_3111_, 3);
lean_dec_ref(v___x_3075_);
lean_dec(v_stx_3074_);
v_a_3179_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3117_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3117_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec_ref(v_ids_3114_);
lean_dec_ref_known(v___x_3111_, 3);
lean_dec_ref(v___x_3075_);
lean_dec(v_stx_3074_);
v_a_3187_ = lean_ctor_get(v___x_3115_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3115_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3115_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed(lean_object* v___x_3195_, lean_object* v_stx_3196_, lean_object* v___x_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
uint8_t v___x_5700__boxed_3205_; lean_object* v_res_3206_; 
v___x_5700__boxed_3205_ = lean_unbox(v___x_3195_);
v_res_3206_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(v___x_5700__boxed_3205_, v_stx_3196_, v___x_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(lean_object* v_stx_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; uint8_t v___x_3218_; lean_object* v___x_3219_; lean_object* v___f_3220_; lean_object* v___x_3221_; 
v___x_3216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_3217_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1));
lean_inc(v_stx_3212_);
v___x_3218_ = l_Lean_Syntax_isOfKind(v_stx_3212_, v___x_3217_);
v___x_3219_ = lean_box(v___x_3218_);
v___f_3220_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3220_, 0, v___x_3219_);
lean_closure_set(v___f_3220_, 1, v_stx_3212_);
lean_closure_set(v___f_3220_, 2, v___x_3216_);
v___x_3221_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3220_, v_a_3213_, v_a_3214_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed(lean_object* v_stx_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(v_stx_3222_, v_a_3223_, v_a_3224_);
lean_dec(v_a_3224_);
lean_dec_ref(v_a_3223_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(lean_object* v_a_3227_, lean_object* v_as_3228_, size_t v_sz_3229_, size_t v_i_3230_, uint8_t v_b_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_3227_, v_as_3228_, v_sz_3229_, v_i_3230_, v_b_3231_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___boxed(lean_object* v_a_3240_, lean_object* v_as_3241_, lean_object* v_sz_3242_, lean_object* v_i_3243_, lean_object* v_b_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
size_t v_sz_boxed_3252_; size_t v_i_boxed_3253_; uint8_t v_b_boxed_3254_; lean_object* v_res_3255_; 
v_sz_boxed_3252_ = lean_unbox_usize(v_sz_3242_);
lean_dec(v_sz_3242_);
v_i_boxed_3253_ = lean_unbox_usize(v_i_3243_);
lean_dec(v_i_3243_);
v_b_boxed_3254_ = lean_unbox(v_b_3244_);
v_res_3255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(v_a_3240_, v_as_3241_, v_sz_boxed_3252_, v_i_boxed_3253_, v_b_boxed_3254_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
lean_dec(v___y_3248_);
lean_dec_ref(v___y_3247_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec_ref(v_as_3241_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1(){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3261_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3262_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1));
v___x_3263_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1));
v___x_3264_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed), 4, 0);
v___x_3265_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3261_, v___x_3262_, v___x_3263_, v___x_3264_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___boxed(lean_object* v_a_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1();
return v_res_3267_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(lean_object* v_name_3268_, lean_object* v_suff_3269_){
_start:
{
if (lean_obj_tag(v_name_3268_) == 1)
{
lean_object* v_str_3270_; uint8_t v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; 
v_str_3270_ = lean_ctor_get(v_name_3268_, 1);
v___x_3271_ = 1;
v___x_3272_ = l_Lean_Name_toString(v_suff_3269_, v___x_3271_);
v___x_3273_ = lean_string_utf8_byte_size(v_str_3270_);
v___x_3274_ = lean_string_utf8_byte_size(v___x_3272_);
v___x_3275_ = lean_nat_dec_le(v___x_3274_, v___x_3273_);
if (v___x_3275_ == 0)
{
lean_dec_ref(v___x_3272_);
return v___x_3275_;
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; uint8_t v___x_3278_; 
v___x_3276_ = lean_unsigned_to_nat(0u);
v___x_3277_ = lean_nat_sub(v___x_3273_, v___x_3274_);
v___x_3278_ = lean_string_memcmp(v_str_3270_, v___x_3272_, v___x_3277_, v___x_3276_, v___x_3274_);
lean_dec(v___x_3277_);
lean_dec_ref(v___x_3272_);
return v___x_3278_;
}
}
else
{
uint8_t v___x_3279_; 
lean_dec(v_suff_3269_);
v___x_3279_ = 0;
return v___x_3279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix___boxed(lean_object* v_name_3280_, lean_object* v_suff_3281_){
_start:
{
uint8_t v_res_3282_; lean_object* v_r_3283_; 
v_res_3282_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(v_name_3280_, v_suff_3281_);
lean_dec(v_name_3280_);
v_r_3283_ = lean_box(v_res_3282_);
return v_r_3283_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(lean_object* v___x_3284_, lean_object* v_as_3285_, size_t v_i_3286_, size_t v_stop_3287_){
_start:
{
uint8_t v___x_3288_; 
v___x_3288_ = lean_usize_dec_eq(v_i_3286_, v_stop_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; uint8_t v___x_3290_; 
v___x_3289_ = lean_array_uget_borrowed(v_as_3285_, v_i_3286_);
v___x_3290_ = l_Lean_Name_isPrefixOf(v___x_3289_, v___x_3284_);
if (v___x_3290_ == 0)
{
size_t v___x_3291_; size_t v___x_3292_; 
v___x_3291_ = ((size_t)1ULL);
v___x_3292_ = lean_usize_add(v_i_3286_, v___x_3291_);
v_i_3286_ = v___x_3292_;
goto _start;
}
else
{
return v___x_3290_;
}
}
else
{
uint8_t v___x_3294_; 
v___x_3294_ = 0;
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1___boxed(lean_object* v___x_3295_, lean_object* v_as_3296_, lean_object* v_i_3297_, lean_object* v_stop_3298_){
_start:
{
size_t v_i_boxed_3299_; size_t v_stop_boxed_3300_; uint8_t v_res_3301_; lean_object* v_r_3302_; 
v_i_boxed_3299_ = lean_unbox_usize(v_i_3297_);
lean_dec(v_i_3297_);
v_stop_boxed_3300_ = lean_unbox_usize(v_stop_3298_);
lean_dec(v_stop_3298_);
v_res_3301_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(v___x_3295_, v_as_3296_, v_i_boxed_3299_, v_stop_boxed_3300_);
lean_dec_ref(v_as_3296_);
lean_dec(v___x_3295_);
v_r_3302_ = lean_box(v_res_3301_);
return v_r_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(lean_object* v_declName_3306_, lean_object* v_init_3307_, lean_object* v_x_3308_){
_start:
{
if (lean_obj_tag(v_x_3308_) == 0)
{
lean_object* v_k_3309_; lean_object* v_l_3310_; lean_object* v_r_3311_; lean_object* v___x_3312_; 
v_k_3309_ = lean_ctor_get(v_x_3308_, 1);
lean_inc(v_k_3309_);
v_l_3310_ = lean_ctor_get(v_x_3308_, 3);
lean_inc(v_l_3310_);
v_r_3311_ = lean_ctor_get(v_x_3308_, 4);
lean_inc(v_r_3311_);
lean_dec_ref_known(v_x_3308_, 5);
v___x_3312_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3306_, v_init_3307_, v_l_3310_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec(v_r_3311_);
lean_dec(v_k_3309_);
return v___x_3312_;
}
else
{
lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3326_; 
v_isSharedCheck_3326_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3326_ == 0)
{
lean_object* v_unused_3327_; 
v_unused_3327_ = lean_ctor_get(v___x_3312_, 0);
lean_dec(v_unused_3327_);
v___x_3314_ = v___x_3312_;
v_isShared_3315_ = v_isSharedCheck_3326_;
goto v_resetjp_3313_;
}
else
{
lean_dec(v___x_3312_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3326_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = lean_box(0);
v___x_3317_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(v_declName_3306_, v_k_3309_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; 
lean_del_object(v___x_3314_);
v___x_3318_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0));
v_init_3307_ = v___x_3318_;
v_x_3308_ = v_r_3311_;
goto _start;
}
else
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
lean_dec(v_r_3311_);
v___x_3320_ = lean_box(v___x_3317_);
v___x_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3320_);
v___x_3322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
lean_ctor_set(v___x_3322_, 1, v___x_3316_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set_tag(v___x_3314_, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3322_);
v___x_3324_ = v___x_3314_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
return v___x_3324_;
}
}
}
}
}
else
{
lean_object* v___x_3328_; 
v___x_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3328_, 0, v_init_3307_);
return v___x_3328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___boxed(lean_object* v_declName_3329_, lean_object* v_init_3330_, lean_object* v_x_3331_){
_start:
{
lean_object* v_res_3332_; 
v_res_3332_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3329_, v_init_3330_, v_x_3331_);
lean_dec(v_declName_3329_);
return v_res_3332_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(lean_object* v_declName_3336_, lean_object* v_as_3337_, size_t v_i_3338_, size_t v_stop_3339_){
_start:
{
uint8_t v___x_3340_; 
v___x_3340_ = lean_usize_dec_eq(v_i_3338_, v_stop_3339_);
if (v___x_3340_ == 0)
{
uint8_t v___x_3341_; uint8_t v___y_3343_; lean_object* v___x_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; 
v___x_3341_ = 1;
v___x_3347_ = lean_array_uget_borrowed(v_as_3337_, v_i_3338_);
v___x_3348_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1));
v___x_3349_ = lean_name_eq(v___x_3347_, v___x_3348_);
if (v___x_3349_ == 0)
{
uint8_t v___x_3350_; 
v___x_3350_ = l_Lean_Name_isPrefixOf(v___x_3347_, v_declName_3336_);
v___y_3343_ = v___x_3350_;
goto v___jp_3342_;
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; uint8_t v___x_3354_; 
lean_inc(v_declName_3336_);
v___x_3351_ = l_Lean_Name_components(v_declName_3336_);
v___x_3352_ = l_List_lengthTR___redArg(v___x_3351_);
lean_dec(v___x_3351_);
v___x_3353_ = lean_unsigned_to_nat(1u);
v___x_3354_ = lean_nat_dec_eq(v___x_3352_, v___x_3353_);
lean_dec(v___x_3352_);
v___y_3343_ = v___x_3354_;
goto v___jp_3342_;
}
v___jp_3342_:
{
if (v___y_3343_ == 0)
{
size_t v___x_3344_; size_t v___x_3345_; 
v___x_3344_ = ((size_t)1ULL);
v___x_3345_ = lean_usize_add(v_i_3338_, v___x_3344_);
v_i_3338_ = v___x_3345_;
goto _start;
}
else
{
lean_dec(v_declName_3336_);
return v___x_3341_;
}
}
}
else
{
uint8_t v___x_3355_; 
lean_dec(v_declName_3336_);
v___x_3355_ = 0;
return v___x_3355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___boxed(lean_object* v_declName_3356_, lean_object* v_as_3357_, lean_object* v_i_3358_, lean_object* v_stop_3359_){
_start:
{
size_t v_i_boxed_3360_; size_t v_stop_boxed_3361_; uint8_t v_res_3362_; lean_object* v_r_3363_; 
v_i_boxed_3360_ = lean_unbox_usize(v_i_3358_);
lean_dec(v_i_3358_);
v_stop_boxed_3361_ = lean_unbox_usize(v_stop_3359_);
lean_dec(v_stop_3359_);
v_res_3362_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(v_declName_3356_, v_as_3357_, v_i_boxed_3360_, v_stop_boxed_3361_);
lean_dec_ref(v_as_3357_);
v_r_3363_ = lean_box(v_res_3362_);
return v_r_3363_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(lean_object* v_prefixes_x3f_3364_, uint8_t v_inModule_3365_, lean_object* v___x_3366_, lean_object* v___x_3367_, lean_object* v___x_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_){
_start:
{
if (lean_obj_tag(v_a_3369_) == 0)
{
lean_object* v___x_3371_; 
lean_dec(v___x_3368_);
v___x_3371_ = lean_array_to_list(v_a_3370_);
return v___x_3371_;
}
else
{
lean_object* v_head_3372_; lean_object* v_tail_3373_; lean_object* v_val_3375_; 
v_head_3372_ = lean_ctor_get(v_a_3369_, 0);
lean_inc(v_head_3372_);
v_tail_3373_ = lean_ctor_get(v_a_3369_, 1);
lean_inc(v_tail_3373_);
lean_dec_ref_known(v_a_3369_, 2);
if (lean_obj_tag(v_head_3372_) == 0)
{
lean_object* v_declName_3378_; uint8_t v___x_3379_; 
v_declName_3378_ = lean_ctor_get(v_head_3372_, 0);
lean_inc(v_declName_3378_);
lean_dec_ref_known(v_head_3372_, 1);
v___x_3379_ = l_Lean_NameSet_contains(v___x_3367_, v_declName_3378_);
if (v___x_3379_ == 0)
{
lean_object* v___x_3380_; uint8_t v___y_3382_; lean_object* v___y_3411_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v_a_3417_; 
v___x_3380_ = lean_box(0);
v___x_3415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0));
lean_inc(v___x_3368_);
v___x_3416_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3378_, v___x_3415_, v___x_3368_);
v_a_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc(v_a_3417_);
lean_dec_ref(v___x_3416_);
v___y_3411_ = v_a_3417_;
goto v___jp_3410_;
v___jp_3381_:
{
if (v___y_3382_ == 0)
{
if (lean_obj_tag(v_prefixes_x3f_3364_) == 1)
{
if (v_inModule_3365_ == 0)
{
lean_object* v_val_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_val_3383_ = lean_ctor_get(v_prefixes_x3f_3364_, 0);
v___x_3384_ = lean_unsigned_to_nat(0u);
v___x_3385_ = lean_array_get_size(v_val_3383_);
v___x_3386_ = lean_nat_dec_lt(v___x_3384_, v___x_3385_);
if (v___x_3386_ == 0)
{
lean_dec(v_declName_3378_);
v_a_3369_ = v_tail_3373_;
goto _start;
}
else
{
if (v___x_3386_ == 0)
{
lean_dec(v_declName_3378_);
v_a_3369_ = v_tail_3373_;
goto _start;
}
else
{
size_t v___x_3389_; size_t v___x_3390_; uint8_t v___x_3391_; 
v___x_3389_ = ((size_t)0ULL);
v___x_3390_ = lean_usize_of_nat(v___x_3385_);
lean_inc(v_declName_3378_);
v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(v_declName_3378_, v_val_3383_, v___x_3389_, v___x_3390_);
if (v___x_3391_ == 0)
{
lean_dec(v_declName_3378_);
v_a_3369_ = v_tail_3373_;
goto _start;
}
else
{
v_val_3375_ = v_declName_3378_;
goto v___jp_3374_;
}
}
}
}
else
{
lean_object* v_val_3393_; lean_object* v___x_3394_; 
v_val_3393_ = lean_ctor_get(v_prefixes_x3f_3364_, 0);
v___x_3394_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3366_, v_declName_3378_);
if (lean_obj_tag(v___x_3394_) == 1)
{
lean_object* v_val_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; uint8_t v___x_3398_; 
v_val_3395_ = lean_ctor_get(v___x_3394_, 0);
lean_inc(v_val_3395_);
lean_dec_ref_known(v___x_3394_, 1);
v___x_3396_ = lean_unsigned_to_nat(0u);
v___x_3397_ = lean_array_get_size(v_val_3393_);
v___x_3398_ = lean_nat_dec_lt(v___x_3396_, v___x_3397_);
if (v___x_3398_ == 0)
{
lean_dec(v_val_3395_);
lean_dec(v_declName_3378_);
v_a_3369_ = v_tail_3373_;
goto _start;
}
else
{
lean_object* v___x_3400_; 
v___x_3400_ = l_Lean_Environment_header(v___x_3366_);
if (v___x_3398_ == 0)
{
lean_dec_ref(v___x_3400_);
lean_dec(v_val_3395_);
lean_dec(v_declName_3378_);
v_a_3369_ = v_tail_3373_;
goto _start;
}
else
{
lean_object* v_moduleNames_3402_; lean_object* v___x_3403_; size_t v___x_3404_; size_t v___x_3405_; uint8_t v___x_3406_; 
v_moduleNames_3402_ = lean_ctor_get(v___x_3400_, 4);
lean_inc_ref(v_moduleNames_3402_);
lean_dec_ref(v___x_3400_);
v___x_3403_ = lean_array_get(v___x_3380_, v_moduleNames_3402_, v_val_3395_);
lean_dec(v_val_3395_);
lean_dec_ref(v_moduleNames_3402_);
v___x_3404_ = ((size_t)0ULL);
v___x_3405_ = lean_usize_of_nat(v___x_3397_);
v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(v___x_3403_, v_val_3393_, v___x_3404_, v___x_3405_);
lean_dec(v___x_3403_);
if (v___x_3406_ == 0)
{
lean_dec(v_declName_3378_);
v_a_3369_ = v_tail_3373_;
goto _start;
}
else
{
v_val_3375_ = v_declName_3378_;
goto v___jp_3374_;
}
}
}
}
else
{
lean_dec(v___x_3394_);
lean_dec(v_declName_3378_);
v_a_3369_ = v_tail_3373_;
goto _start;
}
}
}
else
{
v_val_3375_ = v_declName_3378_;
goto v___jp_3374_;
}
}
else
{
lean_dec(v_declName_3378_);
v_a_3369_ = v_tail_3373_;
goto _start;
}
}
v___jp_3410_:
{
lean_object* v_fst_3412_; 
v_fst_3412_ = lean_ctor_get(v___y_3411_, 0);
lean_inc(v_fst_3412_);
lean_dec_ref(v___y_3411_);
if (lean_obj_tag(v_fst_3412_) == 0)
{
v___y_3382_ = v___x_3379_;
goto v___jp_3381_;
}
else
{
lean_object* v_val_3413_; uint8_t v___x_3414_; 
v_val_3413_ = lean_ctor_get(v_fst_3412_, 0);
lean_inc(v_val_3413_);
lean_dec_ref_known(v_fst_3412_, 1);
v___x_3414_ = lean_unbox(v_val_3413_);
lean_dec(v_val_3413_);
v___y_3382_ = v___x_3414_;
goto v___jp_3381_;
}
}
}
else
{
lean_dec(v_declName_3378_);
v_a_3369_ = v_tail_3373_;
goto _start;
}
}
else
{
lean_dec(v_head_3372_);
v_a_3369_ = v_tail_3373_;
goto _start;
}
v___jp_3374_:
{
lean_object* v___x_3376_; 
v___x_3376_ = lean_array_push(v_a_3370_, v_val_3375_);
v_a_3369_ = v_tail_3373_;
v_a_3370_ = v___x_3376_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3___boxed(lean_object* v_prefixes_x3f_3420_, lean_object* v_inModule_3421_, lean_object* v___x_3422_, lean_object* v___x_3423_, lean_object* v___x_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
uint8_t v_inModule_boxed_3427_; lean_object* v_res_3428_; 
v_inModule_boxed_3427_ = lean_unbox(v_inModule_3421_);
v_res_3428_ = l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(v_prefixes_x3f_3420_, v_inModule_boxed_3427_, v___x_3422_, v___x_3423_, v___x_3424_, v_a_3425_, v_a_3426_);
lean_dec(v___x_3423_);
lean_dec_ref(v___x_3422_);
lean_dec(v_prefixes_x3f_3420_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(lean_object* v_prefixes_x3f_3431_, uint8_t v_inModule_3432_, lean_object* v_a_3433_){
_start:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v_env_3437_; lean_object* v___x_3438_; lean_object* v_toEnvExtension_3439_; lean_object* v_asyncMode_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v_env_3444_; lean_object* v___x_3445_; lean_object* v_toEnvExtension_3446_; lean_object* v_asyncMode_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3435_ = lean_box(1);
v___x_3436_ = lean_st_ref_get(v_a_3433_);
v_env_3437_ = lean_ctor_get(v___x_3436_, 0);
lean_inc_ref(v_env_3437_);
lean_dec(v___x_3436_);
v___x_3438_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_3439_ = lean_ctor_get(v___x_3438_, 0);
v_asyncMode_3440_ = lean_ctor_get(v_toEnvExtension_3439_, 2);
v___x_3441_ = lean_box(0);
v___x_3442_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3435_, v___x_3438_, v_env_3437_, v_asyncMode_3440_, v___x_3441_);
v___x_3443_ = lean_st_ref_get(v_a_3433_);
v_env_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc_ref(v_env_3444_);
lean_dec(v___x_3443_);
v___x_3445_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_3446_ = lean_ctor_get(v___x_3445_, 0);
v_asyncMode_3447_ = lean_ctor_get(v_toEnvExtension_3446_, 2);
v___x_3448_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3435_, v___x_3445_, v_env_3444_, v_asyncMode_3447_, v___x_3441_);
v___x_3449_ = l_Lean_Meta_Grind_grindExt;
v___x_3450_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3449_, v_a_3433_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3463_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3453_ = v___x_3450_;
v_isShared_3454_ = v_isSharedCheck_3463_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3463_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v_env_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3455_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_a_3451_);
lean_dec(v_a_3451_);
v___x_3456_ = lean_st_ref_get(v_a_3433_);
v_env_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc_ref(v_env_3457_);
lean_dec(v___x_3456_);
v___x_3458_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0));
v___x_3459_ = l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(v_prefixes_x3f_3431_, v_inModule_3432_, v_env_3457_, v___x_3442_, v___x_3448_, v___x_3455_, v___x_3458_);
lean_dec(v___x_3442_);
lean_dec_ref(v_env_3457_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v___x_3459_);
v___x_3461_ = v___x_3453_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v___x_3448_);
lean_dec(v___x_3442_);
v_a_3464_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3450_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3450_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___boxed(lean_object* v_prefixes_x3f_3472_, lean_object* v_inModule_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_){
_start:
{
uint8_t v_inModule_boxed_3476_; lean_object* v_res_3477_; 
v_inModule_boxed_3476_ = lean_unbox(v_inModule_3473_);
v_res_3477_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v_prefixes_x3f_3472_, v_inModule_boxed_3476_, v_a_3474_);
lean_dec(v_a_3474_);
lean_dec(v_prefixes_x3f_3472_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(lean_object* v_prefixes_x3f_3478_, uint8_t v_inModule_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v_prefixes_x3f_3478_, v_inModule_3479_, v_a_3481_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___boxed(lean_object* v_prefixes_x3f_3484_, lean_object* v_inModule_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
uint8_t v_inModule_boxed_3489_; lean_object* v_res_3490_; 
v_inModule_boxed_3489_ = lean_unbox(v_inModule_3485_);
v_res_3490_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(v_prefixes_x3f_3484_, v_inModule_boxed_3489_, v_a_3486_, v_a_3487_);
lean_dec(v_a_3487_);
lean_dec_ref(v_a_3486_);
lean_dec(v_prefixes_x3f_3484_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(size_t v_sz_3491_, size_t v_i_3492_, lean_object* v_bs_3493_){
_start:
{
uint8_t v___x_3494_; 
v___x_3494_ = lean_usize_dec_lt(v_i_3492_, v_sz_3491_);
if (v___x_3494_ == 0)
{
return v_bs_3493_;
}
else
{
lean_object* v_v_3495_; lean_object* v___x_3496_; lean_object* v_bs_x27_3497_; lean_object* v___x_3498_; size_t v___x_3499_; size_t v___x_3500_; lean_object* v___x_3501_; 
v_v_3495_ = lean_array_uget(v_bs_3493_, v_i_3492_);
v___x_3496_ = lean_unsigned_to_nat(0u);
v_bs_x27_3497_ = lean_array_uset(v_bs_3493_, v_i_3492_, v___x_3496_);
v___x_3498_ = l_Lean_TSyntax_getId(v_v_3495_);
lean_dec(v_v_3495_);
v___x_3499_ = ((size_t)1ULL);
v___x_3500_ = lean_usize_add(v_i_3492_, v___x_3499_);
v___x_3501_ = lean_array_uset(v_bs_x27_3497_, v_i_3492_, v___x_3498_);
v_i_3492_ = v___x_3500_;
v_bs_3493_ = v___x_3501_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4___boxed(lean_object* v_sz_3503_, lean_object* v_i_3504_, lean_object* v_bs_3505_){
_start:
{
size_t v_sz_boxed_3506_; size_t v_i_boxed_3507_; lean_object* v_res_3508_; 
v_sz_boxed_3506_ = lean_unbox_usize(v_sz_3503_);
lean_dec(v_sz_3503_);
v_i_boxed_3507_ = lean_unbox_usize(v_i_3504_);
lean_dec(v_i_3504_);
v_res_3508_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(v_sz_boxed_3506_, v_i_boxed_3507_, v_bs_3505_);
return v_res_3508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(lean_object* v_hi_3509_, lean_object* v_pivot_3510_, lean_object* v_as_3511_, lean_object* v_i_3512_, lean_object* v_k_3513_){
_start:
{
uint8_t v___x_3514_; 
v___x_3514_ = lean_nat_dec_lt(v_k_3513_, v_hi_3509_);
if (v___x_3514_ == 0)
{
lean_object* v___x_3515_; lean_object* v___x_3516_; 
lean_dec(v_k_3513_);
v___x_3515_ = lean_array_fswap(v_as_3511_, v_i_3512_, v_hi_3509_);
v___x_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3516_, 0, v_i_3512_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
return v___x_3516_;
}
else
{
lean_object* v___x_3517_; uint8_t v___x_3518_; 
v___x_3517_ = lean_array_fget_borrowed(v_as_3511_, v_k_3513_);
v___x_3518_ = l_Lean_Name_lt(v___x_3517_, v_pivot_3510_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = lean_unsigned_to_nat(1u);
v___x_3520_ = lean_nat_add(v_k_3513_, v___x_3519_);
lean_dec(v_k_3513_);
v_k_3513_ = v___x_3520_;
goto _start;
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3522_ = lean_array_fswap(v_as_3511_, v_i_3512_, v_k_3513_);
v___x_3523_ = lean_unsigned_to_nat(1u);
v___x_3524_ = lean_nat_add(v_i_3512_, v___x_3523_);
lean_dec(v_i_3512_);
v___x_3525_ = lean_nat_add(v_k_3513_, v___x_3523_);
lean_dec(v_k_3513_);
v_as_3511_ = v___x_3522_;
v_i_3512_ = v___x_3524_;
v_k_3513_ = v___x_3525_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg___boxed(lean_object* v_hi_3527_, lean_object* v_pivot_3528_, lean_object* v_as_3529_, lean_object* v_i_3530_, lean_object* v_k_3531_){
_start:
{
lean_object* v_res_3532_; 
v_res_3532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_3527_, v_pivot_3528_, v_as_3529_, v_i_3530_, v_k_3531_);
lean_dec(v_pivot_3528_);
lean_dec(v_hi_3527_);
return v_res_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(lean_object* v_n_3533_, lean_object* v_as_3534_, lean_object* v_lo_3535_, lean_object* v_hi_3536_){
_start:
{
lean_object* v___y_3538_; uint8_t v___x_3548_; 
v___x_3548_ = lean_nat_dec_lt(v_lo_3535_, v_hi_3536_);
if (v___x_3548_ == 0)
{
lean_dec(v_lo_3535_);
return v_as_3534_;
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v_mid_3551_; lean_object* v___y_3553_; lean_object* v___y_3559_; lean_object* v___x_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3549_ = lean_nat_add(v_lo_3535_, v_hi_3536_);
v___x_3550_ = lean_unsigned_to_nat(1u);
v_mid_3551_ = lean_nat_shiftr(v___x_3549_, v___x_3550_);
lean_dec(v___x_3549_);
v___x_3564_ = lean_array_fget_borrowed(v_as_3534_, v_mid_3551_);
v___x_3565_ = lean_array_fget_borrowed(v_as_3534_, v_lo_3535_);
v___x_3566_ = l_Lean_Name_lt(v___x_3564_, v___x_3565_);
if (v___x_3566_ == 0)
{
v___y_3559_ = v_as_3534_;
goto v___jp_3558_;
}
else
{
lean_object* v___x_3567_; 
v___x_3567_ = lean_array_fswap(v_as_3534_, v_lo_3535_, v_mid_3551_);
v___y_3559_ = v___x_3567_;
goto v___jp_3558_;
}
v___jp_3552_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v___x_3554_ = lean_array_fget_borrowed(v___y_3553_, v_mid_3551_);
v___x_3555_ = lean_array_fget_borrowed(v___y_3553_, v_hi_3536_);
v___x_3556_ = l_Lean_Name_lt(v___x_3554_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_dec(v_mid_3551_);
v___y_3538_ = v___y_3553_;
goto v___jp_3537_;
}
else
{
lean_object* v___x_3557_; 
v___x_3557_ = lean_array_fswap(v___y_3553_, v_mid_3551_, v_hi_3536_);
lean_dec(v_mid_3551_);
v___y_3538_ = v___x_3557_;
goto v___jp_3537_;
}
}
v___jp_3558_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; 
v___x_3560_ = lean_array_fget_borrowed(v___y_3559_, v_hi_3536_);
v___x_3561_ = lean_array_fget_borrowed(v___y_3559_, v_lo_3535_);
v___x_3562_ = l_Lean_Name_lt(v___x_3560_, v___x_3561_);
if (v___x_3562_ == 0)
{
v___y_3553_ = v___y_3559_;
goto v___jp_3552_;
}
else
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_array_fswap(v___y_3559_, v_lo_3535_, v_hi_3536_);
v___y_3553_ = v___x_3563_;
goto v___jp_3552_;
}
}
}
v___jp_3537_:
{
lean_object* v_pivot_3539_; lean_object* v___x_3540_; lean_object* v_fst_3541_; lean_object* v_snd_3542_; uint8_t v___x_3543_; 
v_pivot_3539_ = lean_array_fget(v___y_3538_, v_hi_3536_);
lean_inc_n(v_lo_3535_, 2);
v___x_3540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_3536_, v_pivot_3539_, v___y_3538_, v_lo_3535_, v_lo_3535_);
lean_dec(v_pivot_3539_);
v_fst_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_fst_3541_);
v_snd_3542_ = lean_ctor_get(v___x_3540_, 1);
lean_inc(v_snd_3542_);
lean_dec_ref(v___x_3540_);
v___x_3543_ = lean_nat_dec_le(v_hi_3536_, v_fst_3541_);
if (v___x_3543_ == 0)
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; 
v___x_3544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_3533_, v_snd_3542_, v_lo_3535_, v_fst_3541_);
v___x_3545_ = lean_unsigned_to_nat(1u);
v___x_3546_ = lean_nat_add(v_fst_3541_, v___x_3545_);
lean_dec(v_fst_3541_);
v_as_3534_ = v___x_3544_;
v_lo_3535_ = v___x_3546_;
goto _start;
}
else
{
lean_dec(v_fst_3541_);
lean_dec(v_lo_3535_);
return v_snd_3542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg___boxed(lean_object* v_n_3568_, lean_object* v_as_3569_, lean_object* v_lo_3570_, lean_object* v_hi_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_3568_, v_as_3569_, v_lo_3570_, v_hi_3571_);
lean_dec(v_hi_3571_);
lean_dec(v_n_3568_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3573_, lean_object* v_msgData_3574_, uint8_t v_severity_3575_, uint8_t v_isSilent_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; uint8_t v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v_toCold_3590_; lean_object* v___y_3591_; lean_object* v___y_3620_; lean_object* v___y_3621_; uint8_t v___y_3622_; lean_object* v___y_3623_; uint8_t v___y_3624_; lean_object* v___y_3625_; uint8_t v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3647_; uint8_t v___y_3648_; lean_object* v___y_3649_; uint8_t v___y_3650_; uint8_t v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; uint8_t v___y_3657_; uint8_t v___y_3658_; uint8_t v___y_3659_; uint8_t v___x_3670_; uint8_t v___y_3672_; uint8_t v___y_3673_; uint8_t v___y_3674_; uint8_t v___y_3676_; uint8_t v___x_3684_; 
v___x_3670_ = 2;
v___x_3684_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3575_, v___x_3670_);
if (v___x_3684_ == 0)
{
v___y_3676_ = v___x_3684_;
goto v___jp_3675_;
}
else
{
uint8_t v___x_3685_; 
lean_inc_ref(v_msgData_3574_);
v___x_3685_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3574_);
v___y_3676_ = v___x_3685_;
goto v___jp_3675_;
}
v___jp_3582_:
{
lean_object* v_currNamespace_3592_; lean_object* v_openDecls_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v_env_3598_; lean_object* v_nextMacroScope_3599_; lean_object* v_ngen_3600_; lean_object* v_auxDeclNGen_3601_; lean_object* v_traceState_3602_; lean_object* v_cache_3603_; lean_object* v_recordedDeps_3604_; lean_object* v_messages_3605_; lean_object* v_infoState_3606_; lean_object* v_snapshotTasks_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3618_; 
v_currNamespace_3592_ = lean_ctor_get(v_toCold_3590_, 4);
v_openDecls_3593_ = lean_ctor_get(v_toCold_3590_, 5);
lean_inc(v_openDecls_3593_);
lean_inc(v_currNamespace_3592_);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v_currNamespace_3592_);
lean_ctor_set(v___x_3594_, 1, v_openDecls_3593_);
v___x_3595_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3595_, 0, v___x_3594_);
lean_ctor_set(v___x_3595_, 1, v___y_3589_);
lean_inc_ref(v___y_3585_);
lean_inc_ref(v___y_3588_);
v___x_3596_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3596_, 0, v___y_3588_);
lean_ctor_set(v___x_3596_, 1, v___y_3583_);
lean_ctor_set(v___x_3596_, 2, v___y_3587_);
lean_ctor_set(v___x_3596_, 3, v___y_3585_);
lean_ctor_set(v___x_3596_, 4, v___x_3595_);
lean_ctor_set_uint8(v___x_3596_, sizeof(void*)*5, v___y_3584_);
lean_ctor_set_uint8(v___x_3596_, sizeof(void*)*5 + 1, v___y_3586_);
lean_ctor_set_uint8(v___x_3596_, sizeof(void*)*5 + 2, v_isSilent_3576_);
v___x_3597_ = lean_st_ref_take(v___y_3591_);
v_env_3598_ = lean_ctor_get(v___x_3597_, 0);
v_nextMacroScope_3599_ = lean_ctor_get(v___x_3597_, 1);
v_ngen_3600_ = lean_ctor_get(v___x_3597_, 2);
v_auxDeclNGen_3601_ = lean_ctor_get(v___x_3597_, 3);
v_traceState_3602_ = lean_ctor_get(v___x_3597_, 4);
v_cache_3603_ = lean_ctor_get(v___x_3597_, 5);
v_recordedDeps_3604_ = lean_ctor_get(v___x_3597_, 6);
v_messages_3605_ = lean_ctor_get(v___x_3597_, 7);
v_infoState_3606_ = lean_ctor_get(v___x_3597_, 8);
v_snapshotTasks_3607_ = lean_ctor_get(v___x_3597_, 9);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3609_ = v___x_3597_;
v_isShared_3610_ = v_isSharedCheck_3618_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_snapshotTasks_3607_);
lean_inc(v_infoState_3606_);
lean_inc(v_messages_3605_);
lean_inc(v_recordedDeps_3604_);
lean_inc(v_cache_3603_);
lean_inc(v_traceState_3602_);
lean_inc(v_auxDeclNGen_3601_);
lean_inc(v_ngen_3600_);
lean_inc(v_nextMacroScope_3599_);
lean_inc(v_env_3598_);
lean_dec(v___x_3597_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3618_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3611_ = lean_box(0);
v___x_3612_ = l_Lean_MessageLog_add(v___x_3596_, v_messages_3605_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 7, v___x_3612_);
v___x_3614_ = v___x_3609_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_env_3598_);
lean_ctor_set(v_reuseFailAlloc_3617_, 1, v_nextMacroScope_3599_);
lean_ctor_set(v_reuseFailAlloc_3617_, 2, v_ngen_3600_);
lean_ctor_set(v_reuseFailAlloc_3617_, 3, v_auxDeclNGen_3601_);
lean_ctor_set(v_reuseFailAlloc_3617_, 4, v_traceState_3602_);
lean_ctor_set(v_reuseFailAlloc_3617_, 5, v_cache_3603_);
lean_ctor_set(v_reuseFailAlloc_3617_, 6, v_recordedDeps_3604_);
lean_ctor_set(v_reuseFailAlloc_3617_, 7, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3617_, 8, v_infoState_3606_);
lean_ctor_set(v_reuseFailAlloc_3617_, 9, v_snapshotTasks_3607_);
v___x_3614_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; 
v___x_3615_ = lean_st_ref_put(v___y_3591_, v___x_3614_);
v___x_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3611_);
return v___x_3616_;
}
}
}
v___jp_3619_:
{
lean_object* v_fileName_3628_; lean_object* v_fileMap_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3645_; 
v_fileName_3628_ = lean_ctor_get(v___y_3623_, 0);
v_fileMap_3629_ = lean_ctor_get(v___y_3623_, 1);
v___x_3630_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3574_);
v___x_3631_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v___x_3630_, v___y_3577_, v___y_3578_, v___y_3579_, v___y_3580_);
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3634_ = v___x_3631_;
v_isShared_3635_ = v_isSharedCheck_3645_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3645_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
lean_inc_ref_n(v_fileMap_3629_, 2);
v___x_3636_ = l_Lean_FileMap_toPosition(v_fileMap_3629_, v___y_3625_);
lean_dec(v___y_3625_);
v___x_3637_ = l_Lean_FileMap_toPosition(v_fileMap_3629_, v___y_3627_);
lean_dec(v___y_3627_);
v___x_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3637_);
v___x_3639_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
if (v___y_3626_ == 0)
{
lean_del_object(v___x_3634_);
lean_dec_ref(v___y_3621_);
v___y_3583_ = v___x_3636_;
v___y_3584_ = v___y_3622_;
v___y_3585_ = v___x_3639_;
v___y_3586_ = v___y_3624_;
v___y_3587_ = v___x_3638_;
v___y_3588_ = v_fileName_3628_;
v___y_3589_ = v_a_3632_;
v_toCold_3590_ = v___y_3620_;
v___y_3591_ = v___y_3580_;
goto v___jp_3582_;
}
else
{
uint8_t v___x_3640_; 
lean_inc(v_a_3632_);
v___x_3640_ = l_Lean_MessageData_hasTag(v___y_3621_, v_a_3632_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3643_; 
lean_dec_ref_known(v___x_3638_, 1);
lean_dec_ref(v___x_3636_);
lean_dec(v_a_3632_);
v___x_3641_ = lean_box(0);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3641_);
v___x_3643_ = v___x_3634_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v___x_3641_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
else
{
lean_del_object(v___x_3634_);
v___y_3583_ = v___x_3636_;
v___y_3584_ = v___y_3622_;
v___y_3585_ = v___x_3639_;
v___y_3586_ = v___y_3624_;
v___y_3587_ = v___x_3638_;
v___y_3588_ = v_fileName_3628_;
v___y_3589_ = v_a_3632_;
v_toCold_3590_ = v___y_3620_;
v___y_3591_ = v___y_3580_;
goto v___jp_3582_;
}
}
}
}
v___jp_3646_:
{
lean_object* v___x_3654_; 
v___x_3654_ = l_Lean_Syntax_getTailPos_x3f(v___y_3652_, v___y_3650_);
lean_dec(v___y_3652_);
if (lean_obj_tag(v___x_3654_) == 0)
{
lean_inc(v___y_3653_);
v___y_3620_ = v___y_3647_;
v___y_3621_ = v___y_3649_;
v___y_3622_ = v___y_3650_;
v___y_3623_ = v___y_3647_;
v___y_3624_ = v___y_3651_;
v___y_3625_ = v___y_3653_;
v___y_3626_ = v___y_3648_;
v___y_3627_ = v___y_3653_;
goto v___jp_3619_;
}
else
{
lean_object* v_val_3655_; 
v_val_3655_ = lean_ctor_get(v___x_3654_, 0);
lean_inc(v_val_3655_);
lean_dec_ref_known(v___x_3654_, 1);
v___y_3620_ = v___y_3647_;
v___y_3621_ = v___y_3649_;
v___y_3622_ = v___y_3650_;
v___y_3623_ = v___y_3647_;
v___y_3624_ = v___y_3651_;
v___y_3625_ = v___y_3653_;
v___y_3626_ = v___y_3648_;
v___y_3627_ = v_val_3655_;
goto v___jp_3619_;
}
}
v___jp_3656_:
{
lean_object* v_toCold_3660_; lean_object* v_ref_3661_; uint8_t v_suppressElabErrors_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___f_3665_; lean_object* v_ref_3666_; lean_object* v___x_3667_; 
v_toCold_3660_ = lean_ctor_get(v___y_3579_, 0);
v_ref_3661_ = lean_ctor_get(v___y_3579_, 2);
v_suppressElabErrors_3662_ = lean_ctor_get_uint8(v___y_3579_, sizeof(void*)*3 + 2);
v___x_3663_ = lean_box(v_suppressElabErrors_3662_);
v___x_3664_ = lean_box(v___y_3657_);
v___f_3665_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3665_, 0, v___x_3663_);
lean_closure_set(v___f_3665_, 1, v___x_3664_);
v_ref_3666_ = l_Lean_replaceRef(v_ref_3573_, v_ref_3661_);
v___x_3667_ = l_Lean_Syntax_getPos_x3f(v_ref_3666_, v___y_3658_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v___x_3668_; 
v___x_3668_ = lean_unsigned_to_nat(0u);
v___y_3647_ = v_toCold_3660_;
v___y_3648_ = v_suppressElabErrors_3662_;
v___y_3649_ = v___f_3665_;
v___y_3650_ = v___y_3658_;
v___y_3651_ = v___y_3659_;
v___y_3652_ = v_ref_3666_;
v___y_3653_ = v___x_3668_;
goto v___jp_3646_;
}
else
{
lean_object* v_val_3669_; 
v_val_3669_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_val_3669_);
lean_dec_ref_known(v___x_3667_, 1);
v___y_3647_ = v_toCold_3660_;
v___y_3648_ = v_suppressElabErrors_3662_;
v___y_3649_ = v___f_3665_;
v___y_3650_ = v___y_3658_;
v___y_3651_ = v___y_3659_;
v___y_3652_ = v_ref_3666_;
v___y_3653_ = v_val_3669_;
goto v___jp_3646_;
}
}
v___jp_3671_:
{
if (v___y_3674_ == 0)
{
v___y_3657_ = v___y_3672_;
v___y_3658_ = v___y_3673_;
v___y_3659_ = v_severity_3575_;
goto v___jp_3656_;
}
else
{
v___y_3657_ = v___y_3672_;
v___y_3658_ = v___y_3673_;
v___y_3659_ = v___x_3670_;
goto v___jp_3656_;
}
}
v___jp_3675_:
{
if (v___y_3676_ == 0)
{
uint8_t v___x_3677_; uint8_t v___x_3678_; 
v___x_3677_ = 1;
v___x_3678_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3575_, v___x_3677_);
if (v___x_3678_ == 0)
{
v___y_3672_ = v___y_3676_;
v___y_3673_ = v___y_3676_;
v___y_3674_ = v___x_3678_;
goto v___jp_3671_;
}
else
{
lean_object* v___x_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3679_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3579_);
v___x_3680_ = l_Lean_warningAsError;
v___x_3681_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v___x_3679_, v___x_3680_);
lean_dec_ref(v___x_3679_);
v___y_3672_ = v___y_3676_;
v___y_3673_ = v___y_3676_;
v___y_3674_ = v___x_3681_;
goto v___jp_3671_;
}
}
else
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
lean_dec_ref(v_msgData_3574_);
v___x_3682_ = lean_box(0);
v___x_3683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
return v___x_3683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3686_, lean_object* v_msgData_3687_, lean_object* v_severity_3688_, lean_object* v_isSilent_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
uint8_t v_severity_boxed_3695_; uint8_t v_isSilent_boxed_3696_; lean_object* v_res_3697_; 
v_severity_boxed_3695_ = lean_unbox(v_severity_3688_);
v_isSilent_boxed_3696_ = lean_unbox(v_isSilent_3689_);
v_res_3697_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_3686_, v_msgData_3687_, v_severity_boxed_3695_, v_isSilent_boxed_3696_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_);
lean_dec(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v_ref_3686_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(lean_object* v_msgData_3698_, uint8_t v_severity_3699_, uint8_t v_isSilent_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_ref_3708_; lean_object* v___x_3709_; 
v_ref_3708_ = lean_ctor_get(v___y_3705_, 2);
v___x_3709_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_3708_, v_msgData_3698_, v_severity_3699_, v_isSilent_3700_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0___boxed(lean_object* v_msgData_3710_, lean_object* v_severity_3711_, lean_object* v_isSilent_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
uint8_t v_severity_boxed_3720_; uint8_t v_isSilent_boxed_3721_; lean_object* v_res_3722_; 
v_severity_boxed_3720_ = lean_unbox(v_severity_3711_);
v_isSilent_boxed_3721_ = lean_unbox(v_isSilent_3712_);
v_res_3722_ = l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(v_msgData_3710_, v_severity_boxed_3720_, v_isSilent_boxed_3721_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(lean_object* v_msgData_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
uint8_t v___x_3731_; uint8_t v___x_3732_; lean_object* v___x_3733_; 
v___x_3731_ = 2;
v___x_3732_ = 0;
v___x_3733_ = l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(v_msgData_3723_, v___x_3731_, v___x_3732_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0___boxed(lean_object* v_msgData_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_, lean_object* v___y_3741_){
_start:
{
lean_object* v_res_3742_; 
v_res_3742_ = l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(v_msgData_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_);
lean_dec(v___y_3740_);
lean_dec_ref(v___y_3739_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
return v_res_3742_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3744_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0));
v___x_3745_ = l_Lean_stringToMessageData(v___x_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(lean_object* v_a_3746_, lean_object* v_as_3747_, size_t v_sz_3748_, size_t v_i_3749_, lean_object* v_b_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
lean_object* v_snd_3759_; uint8_t v___x_3763_; 
v___x_3763_ = lean_usize_dec_lt(v_i_3749_, v_sz_3748_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; 
lean_dec_ref(v_a_3746_);
v___x_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3764_, 0, v_b_3750_);
return v___x_3764_;
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3766_; 
v_a_3765_ = lean_array_uget_borrowed(v_as_3747_, v_i_3749_);
lean_inc_ref(v_a_3746_);
lean_inc(v_a_3765_);
v___x_3766_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_a_3765_, v_a_3746_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; uint8_t v___x_3768_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v___x_3768_ = lean_unbox(v_a_3767_);
lean_dec(v_a_3767_);
if (v___x_3768_ == 0)
{
v_snd_3759_ = v_b_3750_;
goto v___jp_3758_;
}
else
{
lean_object* v___x_3769_; 
lean_inc(v_a_3765_);
v___x_3769_ = lean_array_push(v_b_3750_, v_a_3765_);
v_snd_3759_ = v___x_3769_;
goto v___jp_3758_;
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3795_; 
v_a_3770_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3772_ = v___x_3766_;
v_isShared_3773_ = v_isSharedCheck_3795_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3766_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3795_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
uint8_t v___y_3775_; uint8_t v___x_3793_; 
v___x_3793_ = l_Lean_Exception_isInterrupt(v_a_3770_);
if (v___x_3793_ == 0)
{
uint8_t v___x_3794_; 
lean_inc(v_a_3770_);
v___x_3794_ = l_Lean_Exception_isRuntime(v_a_3770_);
v___y_3775_ = v___x_3794_;
goto v___jp_3774_;
}
else
{
v___y_3775_ = v___x_3793_;
goto v___jp_3774_;
}
v___jp_3774_:
{
if (v___y_3775_ == 0)
{
lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; 
lean_del_object(v___x_3772_);
lean_inc(v_a_3765_);
v___x_3776_ = l_Lean_MessageData_ofName(v_a_3765_);
v___x_3777_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1);
v___x_3778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3776_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = l_Lean_Exception_toMessageData(v_a_3770_);
v___x_3780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3778_);
lean_ctor_set(v___x_3780_, 1, v___x_3779_);
v___x_3781_ = l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(v___x_3780_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_dec_ref_known(v___x_3781_, 1);
v_snd_3759_ = v_b_3750_;
goto v___jp_3758_;
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_dec_ref(v_b_3750_);
lean_dec_ref(v_a_3746_);
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3781_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3781_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
else
{
lean_object* v___x_3791_; 
lean_dec_ref(v_b_3750_);
lean_dec_ref(v_a_3746_);
if (v_isShared_3773_ == 0)
{
v___x_3791_ = v___x_3772_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3770_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
}
v___jp_3758_:
{
size_t v___x_3760_; size_t v___x_3761_; 
v___x_3760_ = ((size_t)1ULL);
v___x_3761_ = lean_usize_add(v_i_3749_, v___x_3760_);
v_i_3749_ = v___x_3761_;
v_b_3750_ = v_snd_3759_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___boxed(lean_object* v_a_3796_, lean_object* v_as_3797_, lean_object* v_sz_3798_, lean_object* v_i_3799_, lean_object* v_b_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
size_t v_sz_boxed_3808_; size_t v_i_boxed_3809_; lean_object* v_res_3810_; 
v_sz_boxed_3808_ = lean_unbox_usize(v_sz_3798_);
lean_dec(v_sz_3798_);
v_i_boxed_3809_ = lean_unbox_usize(v_i_3799_);
lean_dec(v_i_3799_);
v_res_3810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(v_a_3796_, v_as_3797_, v_sz_boxed_3808_, v_i_boxed_3809_, v_b_3800_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_);
lean_dec(v___y_3806_);
lean_dec_ref(v___y_3805_);
lean_dec(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec_ref(v_as_3797_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(uint8_t v___x_3812_, lean_object* v_as_3813_, size_t v_sz_3814_, size_t v_i_3815_, lean_object* v_b_3816_){
_start:
{
uint8_t v___x_3818_; 
v___x_3818_ = lean_usize_dec_lt(v_i_3815_, v_sz_3814_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; 
v___x_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3819_, 0, v_b_3816_);
return v___x_3819_;
}
else
{
lean_object* v___x_3820_; lean_object* v_a_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; size_t v___x_3827_; size_t v___x_3828_; 
v___x_3820_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v_a_3821_ = lean_array_uget_borrowed(v_as_3813_, v_i_3815_);
v___x_3822_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0));
lean_inc(v_a_3821_);
v___x_3823_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_3821_, v___x_3812_);
v___x_3824_ = lean_string_append(v___x_3822_, v___x_3823_);
lean_dec_ref(v___x_3823_);
v___x_3825_ = lean_string_append(v___x_3824_, v___x_3820_);
v___x_3826_ = lean_string_append(v_b_3816_, v___x_3825_);
lean_dec_ref(v___x_3825_);
v___x_3827_ = ((size_t)1ULL);
v___x_3828_ = lean_usize_add(v_i_3815_, v___x_3827_);
v_i_3815_ = v___x_3828_;
v_b_3816_ = v___x_3826_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___boxed(lean_object* v___x_3830_, lean_object* v_as_3831_, lean_object* v_sz_3832_, lean_object* v_i_3833_, lean_object* v_b_3834_, lean_object* v___y_3835_){
_start:
{
uint8_t v___x_10589__boxed_3836_; size_t v_sz_boxed_3837_; size_t v_i_boxed_3838_; lean_object* v_res_3839_; 
v___x_10589__boxed_3836_ = lean_unbox(v___x_3830_);
v_sz_boxed_3837_ = lean_unbox_usize(v_sz_3832_);
lean_dec(v_sz_3832_);
v_i_boxed_3838_ = lean_unbox_usize(v_i_3833_);
lean_dec(v_i_3833_);
v_res_3839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v___x_10589__boxed_3836_, v_as_3831_, v_sz_boxed_3837_, v_i_boxed_3838_, v_b_3834_);
lean_dec_ref(v_as_3831_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(uint8_t v___x_3841_, lean_object* v_stx_3842_, uint8_t v___x_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
if (v___x_3841_ == 0)
{
lean_object* v___x_3851_; 
lean_dec(v_stx_3842_);
v___x_3851_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3851_;
}
else
{
lean_object* v_toCold_3852_; lean_object* v_currRecDepth_3853_; lean_object* v_ref_3854_; uint16_t v_optionFlags_3855_; uint8_t v_suppressElabErrors_3856_; uint8_t v_isRecordingDeps_3857_; lean_object* v_fileName_3858_; lean_object* v_fileMap_3859_; lean_object* v_options_3860_; lean_object* v_maxRecDepth_3861_; lean_object* v_currNamespace_3862_; lean_object* v_openDecls_3863_; lean_object* v_initHeartbeats_3864_; lean_object* v_quotContext_3865_; lean_object* v_currMacroScope_3866_; lean_object* v_cancelTk_x3f_3867_; lean_object* v_inheritedTraceOptions_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; size_t v_sz_3872_; size_t v___x_3873_; lean_object* v___x_3874_; 
v_toCold_3852_ = lean_ctor_get(v___y_3848_, 0);
v_currRecDepth_3853_ = lean_ctor_get(v___y_3848_, 1);
v_ref_3854_ = lean_ctor_get(v___y_3848_, 2);
v_optionFlags_3855_ = lean_ctor_get_uint16(v___y_3848_, sizeof(void*)*3);
v_suppressElabErrors_3856_ = lean_ctor_get_uint8(v___y_3848_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3857_ = lean_ctor_get_uint8(v___y_3848_, sizeof(void*)*3 + 3);
v_fileName_3858_ = lean_ctor_get(v_toCold_3852_, 0);
v_fileMap_3859_ = lean_ctor_get(v_toCold_3852_, 1);
v_options_3860_ = lean_ctor_get(v_toCold_3852_, 2);
v_maxRecDepth_3861_ = lean_ctor_get(v_toCold_3852_, 3);
v_currNamespace_3862_ = lean_ctor_get(v_toCold_3852_, 4);
v_openDecls_3863_ = lean_ctor_get(v_toCold_3852_, 5);
v_initHeartbeats_3864_ = lean_ctor_get(v_toCold_3852_, 6);
v_quotContext_3865_ = lean_ctor_get(v_toCold_3852_, 8);
v_currMacroScope_3866_ = lean_ctor_get(v_toCold_3852_, 9);
v_cancelTk_x3f_3867_ = lean_ctor_get(v_toCold_3852_, 10);
v_inheritedTraceOptions_3868_ = lean_ctor_get(v_toCold_3852_, 11);
v___x_3869_ = lean_unsigned_to_nat(2u);
v___x_3870_ = l_Lean_Syntax_getArg(v_stx_3842_, v___x_3869_);
v___x_3871_ = l_Lean_Syntax_getArgs(v___x_3870_);
lean_dec(v___x_3870_);
v_sz_3872_ = lean_array_size(v___x_3871_);
v___x_3873_ = ((size_t)0ULL);
v___x_3874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_3872_, v___x_3873_, v___x_3871_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v___x_3875_; 
lean_dec(v_stx_3842_);
v___x_3875_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3875_;
}
else
{
lean_object* v_val_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_4088_; 
v_val_3876_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_3878_ = v___x_3874_;
v_isShared_3879_ = v_isSharedCheck_4088_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_val_3876_);
lean_dec(v___x_3874_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_4088_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3880_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v___y_3969_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; uint8_t v___y_3983_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; lean_object* v___y_4014_; lean_object* v___y_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v_m_x3f_4021_; lean_object* v_ids_x3f_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v_m_x3f_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; uint8_t v___x_4077_; 
v___x_3880_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inheritedTraceOptions_3868_);
lean_inc(v_cancelTk_x3f_3867_);
lean_inc(v_currMacroScope_3866_);
lean_inc(v_quotContext_3865_);
lean_inc(v_initHeartbeats_3864_);
lean_inc(v_openDecls_3863_);
lean_inc(v_currNamespace_3862_);
lean_inc(v_maxRecDepth_3861_);
lean_inc_ref(v_options_3860_);
lean_inc_ref(v_fileMap_3859_);
lean_inc_ref(v_fileName_3858_);
v___x_3971_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_3971_, 0, v_fileName_3858_);
lean_ctor_set(v___x_3971_, 1, v_fileMap_3859_);
lean_ctor_set(v___x_3971_, 2, v_options_3860_);
lean_ctor_set(v___x_3971_, 3, v_maxRecDepth_3861_);
lean_ctor_set(v___x_3971_, 4, v_currNamespace_3862_);
lean_ctor_set(v___x_3971_, 5, v_openDecls_3863_);
lean_ctor_set(v___x_3971_, 6, v_initHeartbeats_3864_);
lean_ctor_set(v___x_3971_, 7, v___x_3880_);
lean_ctor_set(v___x_3971_, 8, v_quotContext_3865_);
lean_ctor_set(v___x_3971_, 9, v_currMacroScope_3866_);
lean_ctor_set(v___x_3971_, 10, v_cancelTk_x3f_3867_);
lean_ctor_set(v___x_3971_, 11, v_inheritedTraceOptions_3868_);
lean_inc(v_ref_3854_);
lean_inc(v_currRecDepth_3853_);
v___x_3972_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set(v___x_3972_, 1, v_currRecDepth_3853_);
lean_ctor_set(v___x_3972_, 2, v_ref_3854_);
lean_ctor_set_uint16(v___x_3972_, sizeof(void*)*3, v_optionFlags_3855_);
lean_ctor_set_uint8(v___x_3972_, sizeof(void*)*3 + 2, v_suppressElabErrors_3856_);
lean_ctor_set_uint8(v___x_3972_, sizeof(void*)*3 + 3, v_isRecordingDeps_3857_);
v___x_3973_ = lean_unsigned_to_nat(1u);
v___x_4061_ = lean_unsigned_to_nat(3u);
v___x_4062_ = l_Lean_Syntax_getArg(v_stx_3842_, v___x_4061_);
v___x_4077_ = l_Lean_Syntax_isNone(v___x_4062_);
if (v___x_4077_ == 0)
{
uint8_t v___x_4078_; 
lean_inc(v___x_4062_);
v___x_4078_ = l_Lean_Syntax_matchesNull(v___x_4062_, v___x_4061_);
if (v___x_4078_ == 0)
{
lean_object* v___x_4079_; 
lean_dec(v___x_4062_);
lean_dec_ref_known(v___x_3972_, 3);
lean_del_object(v___x_3878_);
lean_dec(v_val_3876_);
lean_dec(v_stx_3842_);
v___x_4079_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_4079_;
}
else
{
lean_object* v___x_4080_; uint8_t v___x_4081_; 
v___x_4080_ = l_Lean_Syntax_getArg(v___x_4062_, v___x_3973_);
v___x_4081_ = l_Lean_Syntax_isNone(v___x_4080_);
if (v___x_4081_ == 0)
{
uint8_t v___x_4082_; 
lean_inc(v___x_4080_);
v___x_4082_ = l_Lean_Syntax_matchesNull(v___x_4080_, v___x_3973_);
if (v___x_4082_ == 0)
{
lean_object* v___x_4083_; 
lean_dec(v___x_4080_);
lean_dec(v___x_4062_);
lean_dec_ref_known(v___x_3972_, 3);
lean_del_object(v___x_3878_);
lean_dec(v_val_3876_);
lean_dec(v_stx_3842_);
v___x_4083_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_4083_;
}
else
{
lean_object* v_m_x3f_4084_; lean_object* v___x_4085_; 
v_m_x3f_4084_ = l_Lean_Syntax_getArg(v___x_4080_, v___x_3880_);
lean_dec(v___x_4080_);
v___x_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4085_, 0, v_m_x3f_4084_);
v_m_x3f_4064_ = v___x_4085_;
v___y_4065_ = v___y_3844_;
v___y_4066_ = v___y_3845_;
v___y_4067_ = v___y_3846_;
v___y_4068_ = v___y_3847_;
v___y_4069_ = v___x_3972_;
v___y_4070_ = v___y_3849_;
goto v___jp_4063_;
}
}
else
{
lean_object* v___x_4086_; 
lean_dec(v___x_4080_);
v___x_4086_ = lean_box(0);
v_m_x3f_4064_ = v___x_4086_;
v___y_4065_ = v___y_3844_;
v___y_4066_ = v___y_3845_;
v___y_4067_ = v___y_3846_;
v___y_4068_ = v___y_3847_;
v___y_4069_ = v___x_3972_;
v___y_4070_ = v___y_3849_;
goto v___jp_4063_;
}
}
}
else
{
lean_object* v___x_4087_; 
lean_dec(v___x_4062_);
lean_del_object(v___x_3878_);
v___x_4087_ = lean_box(0);
v_m_x3f_4021_ = v___x_4087_;
v_ids_x3f_4022_ = v___x_4087_;
v___y_4023_ = v___y_3844_;
v___y_4024_ = v___y_3845_;
v___y_4025_ = v___y_3846_;
v___y_4026_ = v___y_3847_;
v___y_4027_ = v___x_3972_;
v___y_4028_ = v___y_3849_;
goto v___jp_4020_;
}
v___jp_3881_:
{
lean_object* v___x_3890_; size_t v_sz_3891_; lean_object* v___x_3892_; 
v___x_3890_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0));
v_sz_3891_ = lean_array_size(v___y_3889_);
v___x_3892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(v___y_3887_, v___y_3889_, v_sz_3891_, v___x_3873_, v___x_3890_, v___y_3888_, v___y_3883_, v___y_3885_, v___y_3886_, v___y_3882_, v___y_3884_);
lean_dec_ref(v___y_3889_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3936_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3936_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3936_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3897_; uint8_t v___x_3898_; 
v___x_3897_ = lean_array_get_size(v_a_3893_);
v___x_3898_ = lean_nat_dec_eq(v___x_3897_, v___x_3880_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
lean_del_object(v___x_3895_);
v___x_3899_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5));
lean_inc(v_stx_3842_);
v___x_3900_ = l_Lean_PrettyPrinter_ppCategory(v___x_3899_, v_stx_3842_, v___y_3882_, v___y_3884_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; size_t v_sz_3906_; lean_object* v___x_3907_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3900_, 1);
v___x_3902_ = l_Std_Format_defWidth;
v___x_3903_ = l_Std_Format_pretty(v_a_3901_, v___x_3902_, v___x_3880_, v___x_3880_);
v___x_3904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v___x_3905_ = lean_string_append(v___x_3903_, v___x_3904_);
v_sz_3906_ = lean_array_size(v_a_3893_);
v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v___x_3841_, v_a_3893_, v_sz_3906_, v___x_3873_, v___x_3905_);
lean_dec(v_a_3893_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v___x_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3909_, 0, v_a_3908_);
v___x_3910_ = lean_box(0);
v___x_3911_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3909_);
lean_ctor_set(v___x_3911_, 1, v___x_3910_);
lean_ctor_set(v___x_3911_, 2, v___x_3910_);
lean_ctor_set(v___x_3911_, 3, v___x_3910_);
lean_ctor_set(v___x_3911_, 4, v___x_3910_);
lean_ctor_set(v___x_3911_, 5, v___x_3910_);
v___x_3912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0));
v___x_3913_ = 4;
v___x_3914_ = l_Lean_MessageData_nil;
v___x_3915_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_3842_, v___x_3911_, v___x_3910_, v___x_3912_, v___x_3910_, v___x_3913_, v___x_3914_, v___y_3882_, v___y_3884_);
lean_dec_ref(v___y_3882_);
return v___x_3915_;
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_dec_ref(v___y_3882_);
lean_dec(v_stx_3842_);
v_a_3916_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3907_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3907_);
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
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec(v_a_3893_);
lean_dec_ref(v___y_3882_);
lean_dec(v_stx_3842_);
v_a_3924_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3900_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3900_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_object* v___x_3932_; lean_object* v___x_3934_; 
lean_dec(v_a_3893_);
lean_dec_ref(v___y_3882_);
lean_dec(v_stx_3842_);
v___x_3932_ = lean_box(0);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3932_);
v___x_3934_ = v___x_3895_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
else
{
lean_object* v_a_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3944_; 
lean_dec_ref(v___y_3882_);
lean_dec(v_stx_3842_);
v_a_3937_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3939_ = v___x_3892_;
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_a_3937_);
lean_dec(v___x_3892_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3944_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3942_; 
if (v_isShared_3940_ == 0)
{
v___x_3942_ = v___x_3939_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
v___jp_3945_:
{
lean_object* v___x_3957_; 
v___x_3957_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v___y_3954_, v___y_3948_, v___y_3952_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec(v___y_3954_);
v___y_3882_ = v___y_3947_;
v___y_3883_ = v___y_3946_;
v___y_3884_ = v___y_3949_;
v___y_3885_ = v___y_3950_;
v___y_3886_ = v___y_3951_;
v___y_3887_ = v___y_3953_;
v___y_3888_ = v___y_3955_;
v___y_3889_ = v___x_3957_;
goto v___jp_3881_;
}
v___jp_3958_:
{
uint8_t v___x_3970_; 
v___x_3970_ = lean_nat_dec_le(v___y_3969_, v___y_3964_);
if (v___x_3970_ == 0)
{
lean_dec(v___y_3964_);
lean_inc(v___y_3969_);
v___y_3946_ = v___y_3960_;
v___y_3947_ = v___y_3959_;
v___y_3948_ = v___y_3961_;
v___y_3949_ = v___y_3962_;
v___y_3950_ = v___y_3963_;
v___y_3951_ = v___y_3965_;
v___y_3952_ = v___y_3969_;
v___y_3953_ = v___y_3967_;
v___y_3954_ = v___y_3966_;
v___y_3955_ = v___y_3968_;
v___y_3956_ = v___y_3969_;
goto v___jp_3945_;
}
else
{
v___y_3946_ = v___y_3960_;
v___y_3947_ = v___y_3959_;
v___y_3948_ = v___y_3961_;
v___y_3949_ = v___y_3962_;
v___y_3950_ = v___y_3963_;
v___y_3951_ = v___y_3965_;
v___y_3952_ = v___y_3969_;
v___y_3953_ = v___y_3967_;
v___y_3954_ = v___y_3966_;
v___y_3955_ = v___y_3968_;
v___y_3956_ = v___y_3964_;
goto v___jp_3945_;
}
}
v___jp_3974_:
{
lean_object* v___x_3984_; 
v___x_3984_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v___y_3977_, v___y_3983_, v___y_3978_);
lean_dec(v___y_3977_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v_a_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; 
v_a_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_a_3985_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3986_ = lean_array_mk(v_a_3985_);
v___x_3987_ = lean_array_get_size(v___x_3986_);
v___x_3988_ = lean_nat_dec_eq(v___x_3987_, v___x_3880_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; uint8_t v___x_3990_; 
v___x_3989_ = lean_nat_sub(v___x_3987_, v___x_3973_);
v___x_3990_ = lean_nat_dec_le(v___x_3880_, v___x_3989_);
if (v___x_3990_ == 0)
{
lean_inc(v___x_3989_);
v___y_3959_ = v___y_3976_;
v___y_3960_ = v___y_3975_;
v___y_3961_ = v___x_3986_;
v___y_3962_ = v___y_3978_;
v___y_3963_ = v___y_3979_;
v___y_3964_ = v___x_3989_;
v___y_3965_ = v___y_3980_;
v___y_3966_ = v___x_3987_;
v___y_3967_ = v___y_3981_;
v___y_3968_ = v___y_3982_;
v___y_3969_ = v___x_3989_;
goto v___jp_3958_;
}
else
{
v___y_3959_ = v___y_3976_;
v___y_3960_ = v___y_3975_;
v___y_3961_ = v___x_3986_;
v___y_3962_ = v___y_3978_;
v___y_3963_ = v___y_3979_;
v___y_3964_ = v___x_3989_;
v___y_3965_ = v___y_3980_;
v___y_3966_ = v___x_3987_;
v___y_3967_ = v___y_3981_;
v___y_3968_ = v___y_3982_;
v___y_3969_ = v___x_3880_;
goto v___jp_3958_;
}
}
else
{
v___y_3882_ = v___y_3976_;
v___y_3883_ = v___y_3975_;
v___y_3884_ = v___y_3978_;
v___y_3885_ = v___y_3979_;
v___y_3886_ = v___y_3980_;
v___y_3887_ = v___y_3981_;
v___y_3888_ = v___y_3982_;
v___y_3889_ = v___x_3986_;
goto v___jp_3881_;
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec_ref(v___y_3981_);
lean_dec_ref(v___y_3976_);
lean_dec(v_stx_3842_);
v_a_3991_ = lean_ctor_get(v___x_3984_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3984_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3984_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
v___jp_3999_:
{
uint8_t v___x_4008_; 
v___x_4008_ = 0;
v___y_3975_ = v___y_4001_;
v___y_3976_ = v___y_4000_;
v___y_3977_ = v___y_4002_;
v___y_3978_ = v___y_4003_;
v___y_3979_ = v___y_4004_;
v___y_3980_ = v___y_4005_;
v___y_3981_ = v___y_4006_;
v___y_3982_ = v___y_4007_;
v___y_3983_ = v___x_4008_;
goto v___jp_3974_;
}
v___jp_4009_:
{
if (lean_obj_tag(v___y_4013_) == 1)
{
lean_object* v_val_4019_; 
v_val_4019_ = lean_ctor_get(v___y_4013_, 0);
lean_inc(v_val_4019_);
lean_dec_ref_known(v___y_4013_, 1);
if (lean_obj_tag(v_val_4019_) == 1)
{
lean_dec_ref_known(v_val_4019_, 1);
v___y_3975_ = v___y_4011_;
v___y_3976_ = v___y_4010_;
v___y_3977_ = v___y_4018_;
v___y_3978_ = v___y_4012_;
v___y_3979_ = v___y_4014_;
v___y_3980_ = v___y_4015_;
v___y_3981_ = v___y_4016_;
v___y_3982_ = v___y_4017_;
v___y_3983_ = v___x_3843_;
goto v___jp_3974_;
}
else
{
lean_dec(v_val_4019_);
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4011_;
v___y_4002_ = v___y_4018_;
v___y_4003_ = v___y_4012_;
v___y_4004_ = v___y_4014_;
v___y_4005_ = v___y_4015_;
v___y_4006_ = v___y_4016_;
v___y_4007_ = v___y_4017_;
goto v___jp_3999_;
}
}
else
{
lean_dec(v___y_4013_);
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4011_;
v___y_4002_ = v___y_4018_;
v___y_4003_ = v___y_4012_;
v___y_4004_ = v___y_4014_;
v___y_4005_ = v___y_4015_;
v___y_4006_ = v___y_4016_;
v___y_4007_ = v___y_4017_;
goto v___jp_3999_;
}
}
v___jp_4020_:
{
lean_object* v___x_4029_; 
v___x_4029_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___redArg(v_val_3876_, v___y_4023_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4031_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v___x_4031_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_a_4030_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
if (lean_obj_tag(v___x_4031_) == 0)
{
if (lean_obj_tag(v_ids_x3f_4022_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4033_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v___x_4033_ = lean_box(0);
v___y_4010_ = v___y_4027_;
v___y_4011_ = v___y_4024_;
v___y_4012_ = v___y_4028_;
v___y_4013_ = v_m_x3f_4021_;
v___y_4014_ = v___y_4025_;
v___y_4015_ = v___y_4026_;
v___y_4016_ = v_a_4032_;
v___y_4017_ = v___y_4023_;
v___y_4018_ = v___x_4033_;
goto v___jp_4009_;
}
else
{
lean_object* v_a_4034_; lean_object* v_val_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4044_; 
v_a_4034_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4031_, 1);
v_val_4035_ = lean_ctor_get(v_ids_x3f_4022_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v_ids_x3f_4022_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4037_ = v_ids_x3f_4022_;
v_isShared_4038_ = v_isSharedCheck_4044_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_val_4035_);
lean_dec(v_ids_x3f_4022_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4044_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
size_t v_sz_4039_; lean_object* v___x_4040_; lean_object* v___x_4042_; 
v_sz_4039_ = lean_array_size(v_val_4035_);
v___x_4040_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(v_sz_4039_, v___x_3873_, v_val_4035_);
if (v_isShared_4038_ == 0)
{
lean_ctor_set(v___x_4037_, 0, v___x_4040_);
v___x_4042_ = v___x_4037_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4040_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
v___y_4010_ = v___y_4027_;
v___y_4011_ = v___y_4024_;
v___y_4012_ = v___y_4028_;
v___y_4013_ = v_m_x3f_4021_;
v___y_4014_ = v___y_4025_;
v___y_4015_ = v___y_4026_;
v___y_4016_ = v_a_4034_;
v___y_4017_ = v___y_4023_;
v___y_4018_ = v___x_4042_;
goto v___jp_4009_;
}
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec_ref(v___y_4027_);
lean_dec(v_ids_x3f_4022_);
lean_dec(v_m_x3f_4021_);
lean_dec(v_stx_3842_);
v_a_4045_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4031_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4031_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_dec_ref(v___y_4027_);
lean_dec(v_ids_x3f_4022_);
lean_dec(v_m_x3f_4021_);
lean_dec(v_stx_3842_);
v_a_4053_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4029_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4029_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
v___jp_4063_:
{
lean_object* v___x_4071_; lean_object* v_ids_x3f_4072_; lean_object* v___x_4074_; 
v___x_4071_ = l_Lean_Syntax_getArg(v___x_4062_, v___x_3869_);
lean_dec(v___x_4062_);
v_ids_x3f_4072_ = l_Lean_Syntax_getArgs(v___x_4071_);
lean_dec(v___x_4071_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 0, v_m_x3f_4064_);
v___x_4074_ = v___x_3878_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_m_x3f_4064_);
v___x_4074_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4075_, 0, v_ids_x3f_4072_);
v_m_x3f_4021_ = v___x_4074_;
v_ids_x3f_4022_ = v___x_4075_;
v___y_4023_ = v___y_4065_;
v___y_4024_ = v___y_4066_;
v___y_4025_ = v___y_4067_;
v___y_4026_ = v___y_4068_;
v___y_4027_ = v___y_4069_;
v___y_4028_ = v___y_4070_;
goto v___jp_4020_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed(lean_object* v___x_4089_, lean_object* v_stx_4090_, lean_object* v___x_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
uint8_t v___x_10628__boxed_4099_; uint8_t v___x_10629__boxed_4100_; lean_object* v_res_4101_; 
v___x_10628__boxed_4099_ = lean_unbox(v___x_4089_);
v___x_10629__boxed_4100_ = lean_unbox(v___x_4091_);
v_res_4101_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(v___x_10628__boxed_4099_, v_stx_4090_, v___x_10629__boxed_4100_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(lean_object* v_stx_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v___x_4111_; uint8_t v___x_4112_; uint8_t v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___f_4116_; lean_object* v___x_4117_; 
v___x_4111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1));
lean_inc(v_stx_4107_);
v___x_4112_ = l_Lean_Syntax_isOfKind(v_stx_4107_, v___x_4111_);
v___x_4113_ = 1;
v___x_4114_ = lean_box(v___x_4112_);
v___x_4115_ = lean_box(v___x_4113_);
v___f_4116_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4116_, 0, v___x_4114_);
lean_closure_set(v___f_4116_, 1, v_stx_4107_);
lean_closure_set(v___f_4116_, 2, v___x_4115_);
v___x_4117_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_4116_, v_a_4108_, v_a_4109_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed(lean_object* v_stx_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(v_stx_4118_, v_a_4119_, v_a_4120_);
lean_dec(v_a_4120_);
lean_dec_ref(v_a_4119_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(uint8_t v___x_4123_, lean_object* v_as_4124_, size_t v_sz_4125_, size_t v_i_4126_, lean_object* v_b_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v___x_4123_, v_as_4124_, v_sz_4125_, v_i_4126_, v_b_4127_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___boxed(lean_object* v___x_4136_, lean_object* v_as_4137_, lean_object* v_sz_4138_, lean_object* v_i_4139_, lean_object* v_b_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
uint8_t v___x_11115__boxed_4148_; size_t v_sz_boxed_4149_; size_t v_i_boxed_4150_; lean_object* v_res_4151_; 
v___x_11115__boxed_4148_ = lean_unbox(v___x_4136_);
v_sz_boxed_4149_ = lean_unbox_usize(v_sz_4138_);
lean_dec(v_sz_4138_);
v_i_boxed_4150_ = lean_unbox_usize(v_i_4139_);
lean_dec(v_i_4139_);
v_res_4151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(v___x_11115__boxed_4148_, v_as_4137_, v_sz_boxed_4149_, v_i_boxed_4150_, v_b_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec_ref(v___y_4141_);
lean_dec_ref(v_as_4137_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(lean_object* v_n_4152_, lean_object* v_as_4153_, lean_object* v_lo_4154_, lean_object* v_hi_4155_, lean_object* v_w_4156_, lean_object* v_hlo_4157_, lean_object* v_hhi_4158_){
_start:
{
lean_object* v___x_4159_; 
v___x_4159_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_4152_, v_as_4153_, v_lo_4154_, v_hi_4155_);
return v___x_4159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___boxed(lean_object* v_n_4160_, lean_object* v_as_4161_, lean_object* v_lo_4162_, lean_object* v_hi_4163_, lean_object* v_w_4164_, lean_object* v_hlo_4165_, lean_object* v_hhi_4166_){
_start:
{
lean_object* v_res_4167_; 
v_res_4167_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(v_n_4160_, v_as_4161_, v_lo_4162_, v_hi_4163_, v_w_4164_, v_hlo_4165_, v_hhi_4166_);
lean_dec(v_hi_4163_);
lean_dec(v_n_4160_);
return v_res_4167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(lean_object* v_n_4168_, lean_object* v_lo_4169_, lean_object* v_hi_4170_, lean_object* v_hhi_4171_, lean_object* v_pivot_4172_, lean_object* v_as_4173_, lean_object* v_i_4174_, lean_object* v_k_4175_, lean_object* v_ilo_4176_, lean_object* v_ik_4177_, lean_object* v_w_4178_){
_start:
{
lean_object* v___x_4179_; 
v___x_4179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_4170_, v_pivot_4172_, v_as_4173_, v_i_4174_, v_k_4175_);
return v___x_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___boxed(lean_object* v_n_4180_, lean_object* v_lo_4181_, lean_object* v_hi_4182_, lean_object* v_hhi_4183_, lean_object* v_pivot_4184_, lean_object* v_as_4185_, lean_object* v_i_4186_, lean_object* v_k_4187_, lean_object* v_ilo_4188_, lean_object* v_ik_4189_, lean_object* v_w_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(v_n_4180_, v_lo_4181_, v_hi_4182_, v_hhi_4183_, v_pivot_4184_, v_as_4185_, v_i_4186_, v_k_4187_, v_ilo_4188_, v_ik_4189_, v_w_4190_);
lean_dec(v_pivot_4184_);
lean_dec(v_hi_4182_);
lean_dec(v_lo_4181_);
lean_dec(v_n_4180_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(lean_object* v_ref_4192_, lean_object* v_msgData_4193_, uint8_t v_severity_4194_, uint8_t v_isSilent_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v___x_4203_; 
v___x_4203_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_4192_, v_msgData_4193_, v_severity_4194_, v_isSilent_4195_, v___y_4198_, v___y_4199_, v___y_4200_, v___y_4201_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4204_, lean_object* v_msgData_4205_, lean_object* v_severity_4206_, lean_object* v_isSilent_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
uint8_t v_severity_boxed_4215_; uint8_t v_isSilent_boxed_4216_; lean_object* v_res_4217_; 
v_severity_boxed_4215_ = lean_unbox(v_severity_4206_);
v_isSilent_boxed_4216_ = lean_unbox(v_isSilent_4207_);
v_res_4217_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(v_ref_4204_, v_msgData_4205_, v_severity_boxed_4215_, v_isSilent_boxed_4216_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
lean_dec(v___y_4213_);
lean_dec_ref(v___y_4212_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
lean_dec(v_ref_4204_);
return v_res_4217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1(){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4223_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4224_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1));
v___x_4225_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1));
v___x_4226_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed), 4, 0);
v___x_4227_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4223_, v___x_4224_, v___x_4225_, v___x_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___boxed(lean_object* v_a_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1();
return v_res_4229_;
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
