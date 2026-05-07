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
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Grind_grindExt;
lean_object* l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_getOrigins___redArg(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
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
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_elabConfigItems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "` is already in the `#grind_lint` skip set"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "` is already in the `#grind_lint` skip suffix set"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*12 + 32, .m_other = 12, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
static const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig = (const lean_object*)&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig___closed__0_value;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_34_; 
v___x_34_ = lean_nat_dec_le(v___x_32_, v___x_32_);
if (v___x_34_ == 0)
{
if (v___x_33_ == 0)
{
v___y_25_ = v_b_23_;
goto v___jp_24_;
}
else
{
size_t v___x_35_; size_t v___x_36_; lean_object* v___x_37_; 
v___x_35_ = ((size_t)0ULL);
v___x_36_ = lean_usize_of_nat(v___x_32_);
v___x_37_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0(v___x_30_, v___x_35_, v___x_36_, v_b_23_);
v___y_25_ = v___x_37_;
goto v___jp_24_;
}
}
else
{
size_t v___x_38_; size_t v___x_39_; lean_object* v___x_40_; 
v___x_38_ = ((size_t)0ULL);
v___x_39_ = lean_usize_of_nat(v___x_32_);
v___x_40_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__0(v___x_30_, v___x_38_, v___x_39_, v_b_23_);
v___y_25_ = v___x_40_;
goto v___jp_24_;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_41_, lean_object* v_i_42_, lean_object* v_stop_43_, lean_object* v_b_44_){
_start:
{
size_t v_i_boxed_45_; size_t v_stop_boxed_46_; lean_object* v_res_47_; 
v_i_boxed_45_ = lean_unbox_usize(v_i_42_);
lean_dec(v_i_42_);
v_stop_boxed_46_ = lean_unbox_usize(v_stop_43_);
lean_dec(v_stop_43_);
v_res_47_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(v_as_41_, v_i_boxed_45_, v_stop_boxed_46_, v_b_44_);
lean_dec_ref(v_as_41_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0(lean_object* v_initState_48_, lean_object* v_as_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; uint8_t v___x_52_; 
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_array_get_size(v_as_49_);
v___x_52_ = lean_nat_dec_lt(v___x_50_, v___x_51_);
if (v___x_52_ == 0)
{
return v_initState_48_;
}
else
{
uint8_t v___x_53_; 
v___x_53_ = lean_nat_dec_le(v___x_51_, v___x_51_);
if (v___x_53_ == 0)
{
if (v___x_52_ == 0)
{
return v_initState_48_;
}
else
{
size_t v___x_54_; size_t v___x_55_; lean_object* v___x_56_; 
v___x_54_ = ((size_t)0ULL);
v___x_55_ = lean_usize_of_nat(v___x_51_);
v___x_56_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(v_as_49_, v___x_54_, v___x_55_, v_initState_48_);
return v___x_56_;
}
}
else
{
size_t v___x_57_; size_t v___x_58_; lean_object* v___x_59_; 
v___x_57_ = ((size_t)0ULL);
v___x_58_ = lean_usize_of_nat(v___x_51_);
v___x_59_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0_spec__1(v_as_49_, v___x_57_, v___x_58_, v_initState_48_);
return v___x_59_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_60_, lean_object* v_as_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0(v_initState_60_, v_as_61_);
lean_dec_ref(v_as_61_);
return v_res_62_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = l_Lean_NameSet_empty;
v___x_109_ = lean_alloc_closure((void*)(l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__spec__0___boxed), 2, 1);
lean_closure_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___f_112_; lean_object* v___x_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_110_ = lean_box(2);
v___x_111_ = lean_box(0);
v___f_112_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_113_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
v___f_114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__20_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_116_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___f_114_);
lean_ctor_set(v___x_116_, 2, v___x_113_);
lean_ctor_set(v___x_116_, 3, v___f_112_);
lean_ctor_set(v___x_116_, 4, v___x_111_);
lean_ctor_set(v___x_116_, 5, v___x_110_);
lean_ctor_set(v___x_116_, 6, v___x_111_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__22_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
v___x_119_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2____boxed(lean_object* v_a_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_();
return v_res_121_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___f_128_; lean_object* v___x_129_; lean_object* v___f_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_126_ = lean_box(2);
v___x_127_ = lean_box(0);
v___f_128_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_129_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
v___f_130_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_131_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_));
v___x_132_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___f_130_);
lean_ctor_set(v___x_132_, 2, v___x_129_);
lean_ctor_set(v___x_132_, 3, v___f_128_);
lean_ctor_set(v___x_132_, 4, v___x_127_);
lean_ctor_set(v___x_132_, 5, v___x_126_);
lean_ctor_set(v___x_132_, 6, v___x_127_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_);
v___x_135_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2____boxed(lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_989560566____hygCtx___hyg_2_();
return v_res_137_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___f_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_142_ = lean_box(2);
v___x_143_ = lean_box(0);
v___f_144_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_145_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__21_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_);
v___f_146_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__0_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_147_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__1_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_));
v___x_148_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___f_146_);
lean_ctor_set(v___x_148_, 2, v___x_145_);
lean_ctor_set(v___x_148_, 3, v___f_144_);
lean_ctor_set(v___x_148_, 4, v___x_143_);
lean_ctor_set(v___x_148_, 5, v___x_142_);
lean_ctor_set(v___x_148_, 6, v___x_143_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__2_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_);
v___x_151_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2____boxed(lean_object* v_a_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn_00___x40_Lean_Elab_Tactic_Grind_Lint_2605288574____hygCtx___hyg_2_();
return v_res_153_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_154_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__0);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
lean_ctor_set(v___x_159_, 2, v___x_158_);
lean_ctor_set(v___x_159_, 3, v___x_158_);
lean_ctor_set(v___x_159_, 4, v___x_157_);
lean_ctor_set(v___x_159_, 5, v___x_157_);
lean_ctor_set(v___x_159_, 6, v___x_157_);
lean_ctor_set(v___x_159_, 7, v___x_157_);
lean_ctor_set(v___x_159_, 8, v___x_157_);
lean_ctor_set(v___x_159_, 9, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_160_ = lean_unsigned_to_nat(32u);
v___x_161_ = lean_mk_empty_array_with_capacity(v___x_160_);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_163_ = ((size_t)5ULL);
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_unsigned_to_nat(32u);
v___x_166_ = lean_mk_empty_array_with_capacity(v___x_165_);
v___x_167_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__3);
v___x_168_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_164_);
lean_ctor_set(v___x_168_, 3, v___x_164_);
lean_ctor_set_usize(v___x_168_, 4, v___x_163_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_169_ = lean_box(1);
v___x_170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__4);
v___x_171_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__1);
v___x_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
lean_ctor_set(v___x_172_, 2, v___x_169_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(lean_object* v_msgData_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v___x_177_; lean_object* v_env_178_; lean_object* v_options_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_177_ = lean_st_ref_get(v___y_175_);
v_env_178_ = lean_ctor_get(v___x_177_, 0);
lean_inc_ref(v_env_178_);
lean_dec(v___x_177_);
v_options_179_ = lean_ctor_get(v___y_174_, 2);
v___x_180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2);
v___x_181_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_179_);
v___x_182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_182_, 0, v_env_178_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
lean_ctor_set(v___x_182_, 2, v___x_181_);
lean_ctor_set(v___x_182_, 3, v_options_179_);
v___x_183_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_182_);
lean_ctor_set(v___x_183_, 1, v_msgData_173_);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_msgData_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(v_msgData_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(lean_object* v_msg_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v_ref_194_; lean_object* v___x_195_; lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_204_; 
v_ref_194_ = lean_ctor_get(v___y_191_, 5);
v___x_195_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0(v_msg_190_, v___y_191_, v___y_192_);
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_204_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
lean_inc(v_ref_194_);
v___x_200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_200_, 0, v_ref_194_);
lean_ctor_set(v___x_200_, 1, v_a_196_);
if (v_isShared_199_ == 0)
{
lean_ctor_set_tag(v___x_198_, 1);
lean_ctor_set(v___x_198_, 0, v___x_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg___boxed(lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v_msg_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_209_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1(void){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__0));
v___x_212_ = l_Lean_stringToMessageData(v___x_211_);
return v___x_212_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__2));
v___x_215_ = l_Lean_stringToMessageData(v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(lean_object* v_declName_216_, lean_object* v_a_217_, lean_object* v_a_218_){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = l_Lean_Meta_Grind_grindExt;
lean_inc(v_declName_216_);
v___x_221_ = l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(v___x_220_, v_declName_216_, v_a_218_);
if (lean_obj_tag(v___x_221_) == 0)
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_237_; 
v_a_222_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_237_ == 0)
{
v___x_224_ = v___x_221_;
v_isShared_225_ = v_isSharedCheck_237_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_221_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_237_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
uint8_t v___x_226_; 
v___x_226_ = lean_unbox(v_a_222_);
lean_dec(v_a_222_);
if (v___x_226_ == 0)
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
lean_del_object(v___x_224_);
v___x_227_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
v___x_228_ = l_Lean_MessageData_ofName(v_declName_216_);
v___x_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__3);
v___x_231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v___x_231_, v_a_217_, v_a_218_);
return v___x_232_;
}
else
{
lean_object* v___x_233_; lean_object* v___x_235_; 
lean_dec(v_declName_216_);
v___x_233_ = lean_box(0);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_233_);
v___x_235_ = v___x_224_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_233_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
else
{
lean_object* v_a_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_245_; 
lean_dec(v_declName_216_);
v_a_238_ = lean_ctor_get(v___x_221_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_221_);
if (v_isSharedCheck_245_ == 0)
{
v___x_240_ = v___x_221_;
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_a_238_);
lean_dec(v___x_221_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_245_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_243_; 
if (v_isShared_241_ == 0)
{
v___x_243_ = v___x_240_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_a_238_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___boxed(lean_object* v_declName_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_declName_246_, v_a_247_, v_a_248_);
lean_dec(v_a_248_);
lean_dec_ref(v_a_247_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0(lean_object* v_00_u03b1_251_, lean_object* v_msg_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___redArg(v_msg_252_, v___y_253_, v___y_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0___boxed(lean_object* v_00_u03b1_257_, lean_object* v_msg_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0(v_00_u03b1_257_, v_msg_258_, v___y_259_, v___y_260_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_262_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_263_ = lean_box(0);
v___x_264_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___x_263_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg(){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0);
v___x_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___boxed(lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(lean_object* v_00_u03b1_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___boxed(lean_object* v_00_u03b1_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3(v_00_u03b1_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
lean_object* v___x_287_; lean_object* v_env_288_; lean_object* v___x_289_; lean_object* v_mctx_290_; lean_object* v_lctx_291_; lean_object* v_options_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_287_ = lean_st_ref_get(v___y_285_);
v_env_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc_ref(v_env_288_);
lean_dec(v___x_287_);
v___x_289_ = lean_st_ref_get(v___y_283_);
v_mctx_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc_ref(v_mctx_290_);
lean_dec(v___x_289_);
v_lctx_291_ = lean_ctor_get(v___y_282_, 2);
v_options_292_ = lean_ctor_get(v___y_284_, 2);
lean_inc_ref(v_options_292_);
lean_inc_ref(v_lctx_291_);
v___x_293_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_293_, 0, v_env_288_);
lean_ctor_set(v___x_293_, 1, v_mctx_290_);
lean_ctor_set(v___x_293_, 2, v_lctx_291_);
lean_ctor_set(v___x_293_, 3, v_options_292_);
v___x_294_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v_msgData_281_);
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0___boxed(lean_object* v_msgData_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v_msgData_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
return v_res_302_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(lean_object* v_opts_303_, lean_object* v_opt_304_){
_start:
{
lean_object* v_name_305_; lean_object* v_defValue_306_; lean_object* v_map_307_; lean_object* v___x_308_; 
v_name_305_ = lean_ctor_get(v_opt_304_, 0);
v_defValue_306_ = lean_ctor_get(v_opt_304_, 1);
v_map_307_ = lean_ctor_get(v_opts_303_, 0);
v___x_308_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_307_, v_name_305_);
if (lean_obj_tag(v___x_308_) == 0)
{
uint8_t v___x_309_; 
v___x_309_ = lean_unbox(v_defValue_306_);
return v___x_309_;
}
else
{
lean_object* v_val_310_; 
v_val_310_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_val_310_);
lean_dec_ref(v___x_308_);
if (lean_obj_tag(v_val_310_) == 1)
{
uint8_t v_v_311_; 
v_v_311_ = lean_ctor_get_uint8(v_val_310_, 0);
lean_dec_ref(v_val_310_);
return v_v_311_;
}
else
{
uint8_t v___x_312_; 
lean_dec(v_val_310_);
v___x_312_ = lean_unbox(v_defValue_306_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_313_, lean_object* v_opt_314_){
_start:
{
uint8_t v_res_315_; lean_object* v_r_316_; 
v_res_315_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v_opts_313_, v_opt_314_);
lean_dec_ref(v_opt_314_);
lean_dec_ref(v_opts_313_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_box(1);
v___x_318_ = l_Lean_MessageData_ofFormat(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__2));
v___x_323_ = l_Lean_MessageData_ofFormat(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4(lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_325_) == 0)
{
return v_x_324_;
}
else
{
lean_object* v_head_326_; lean_object* v_tail_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_349_; 
v_head_326_ = lean_ctor_get(v_x_325_, 0);
v_tail_327_ = lean_ctor_get(v_x_325_, 1);
v_isSharedCheck_349_ = !lean_is_exclusive(v_x_325_);
if (v_isSharedCheck_349_ == 0)
{
v___x_329_ = v_x_325_;
v_isShared_330_ = v_isSharedCheck_349_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_tail_327_);
lean_inc(v_head_326_);
lean_dec(v_x_325_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_349_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v_before_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_347_; 
v_before_331_ = lean_ctor_get(v_head_326_, 0);
v_isSharedCheck_347_ = !lean_is_exclusive(v_head_326_);
if (v_isSharedCheck_347_ == 0)
{
lean_object* v_unused_348_; 
v_unused_348_ = lean_ctor_get(v_head_326_, 1);
lean_dec(v_unused_348_);
v___x_333_ = v_head_326_;
v_isShared_334_ = v_isSharedCheck_347_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_before_331_);
lean_dec(v_head_326_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_347_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 7);
lean_ctor_set(v___x_333_, 1, v___x_335_);
lean_ctor_set(v___x_333_, 0, v_x_324_);
v___x_337_ = v___x_333_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_x_324_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v___x_335_);
v___x_337_ = v_reuseFailAlloc_346_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__3);
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 7);
lean_ctor_set(v___x_329_, 1, v___x_338_);
lean_ctor_set(v___x_329_, 0, v___x_337_);
v___x_340_ = v___x_329_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_345_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_341_ = l_Lean_MessageData_ofSyntax(v_before_331_);
v___x_342_ = l_Lean_indentD(v___x_341_);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_340_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v_x_324_ = v___x_343_;
v_x_325_ = v_tail_327_;
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
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__1));
v___x_354_ = l_Lean_MessageData_ofFormat(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(lean_object* v_msgData_355_, lean_object* v_macroStack_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_options_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_options_359_ = lean_ctor_get(v___y_357_, 2);
v___x_360_ = l_Lean_Elab_pp_macroStack;
v___x_361_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v_options_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; 
lean_dec(v_macroStack_356_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v_msgData_355_);
return v___x_362_;
}
else
{
if (lean_obj_tag(v_macroStack_356_) == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v_msgData_355_);
return v___x_363_;
}
else
{
lean_object* v_head_364_; lean_object* v_after_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_380_; 
v_head_364_ = lean_ctor_get(v_macroStack_356_, 0);
lean_inc(v_head_364_);
v_after_365_ = lean_ctor_get(v_head_364_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_head_364_);
if (v_isSharedCheck_380_ == 0)
{
lean_object* v_unused_381_; 
v_unused_381_ = lean_ctor_get(v_head_364_, 0);
lean_dec(v_unused_381_);
v___x_367_ = v_head_364_;
v_isShared_368_ = v_isSharedCheck_380_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_after_365_);
lean_dec(v_head_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_380_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_369_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 7);
lean_ctor_set(v___x_367_, 1, v___x_369_);
lean_ctor_set(v___x_367_, 0, v_msgData_355_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_msgData_355_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_369_);
v___x_371_ = v_reuseFailAlloc_379_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v_msgData_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_372_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___closed__2);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = l_Lean_MessageData_ofSyntax(v_after_365_);
v___x_375_ = l_Lean_indentD(v___x_374_);
v_msgData_376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_376_, 0, v___x_373_);
lean_ctor_set(v_msgData_376_, 1, v___x_375_);
v___x_377_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__4(v_msgData_376_, v_macroStack_356_);
v___x_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
return v___x_378_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_382_, lean_object* v_macroStack_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(v_msgData_382_, v_macroStack_383_, v___y_384_);
lean_dec_ref(v___y_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v_a_397_; lean_object* v_macroStack_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v_a_401_; lean_object* v___x_403_; uint8_t v_isShared_404_; uint8_t v_isSharedCheck_409_; 
v_ref_395_ = lean_ctor_get(v___y_392_, 5);
v___x_396_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v_msg_387_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
v_a_397_ = lean_ctor_get(v___x_396_, 0);
lean_inc(v_a_397_);
lean_dec_ref(v___x_396_);
v_macroStack_398_ = lean_ctor_get(v___y_388_, 1);
v___x_399_ = l_Lean_Elab_getBetterRef(v_ref_395_, v_macroStack_398_);
lean_inc(v_macroStack_398_);
v___x_400_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(v_a_397_, v_macroStack_398_, v___y_392_);
v_a_401_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_409_ == 0)
{
v___x_403_ = v___x_400_;
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
else
{
lean_inc(v_a_401_);
lean_dec(v___x_400_);
v___x_403_ = lean_box(0);
v_isShared_404_ = v_isSharedCheck_409_;
goto v_resetjp_402_;
}
v_resetjp_402_:
{
lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_399_);
lean_ctor_set(v___x_405_, 1, v_a_401_);
if (v_isShared_404_ == 0)
{
lean_ctor_set_tag(v___x_403_, 1);
lean_ctor_set(v___x_403_, 0, v___x_405_);
v___x_407_ = v___x_403_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_405_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg___boxed(lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v_msg_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
lean_dec_ref(v___y_413_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_418_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0(void){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_419_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__0);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__1);
v___x_425_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
lean_ctor_set(v___x_425_, 2, v___x_424_);
lean_ctor_set(v___x_425_, 3, v___x_424_);
lean_ctor_set(v___x_425_, 4, v___x_424_);
lean_ctor_set(v___x_425_, 5, v___x_424_);
return v___x_425_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__4));
v___x_428_ = l_Lean_stringToMessageData(v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(lean_object* v_as_429_, size_t v_sz_430_, size_t v_i_431_, lean_object* v_b_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_lt(v_i_431_, v_sz_430_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v_b_432_);
return v___x_441_;
}
else
{
lean_object* v_a_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v_a_442_ = lean_array_uget_borrowed(v_as_429_, v_i_431_);
v___x_443_ = lean_box(0);
lean_inc(v_a_442_);
v___x_444_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_442_, v___x_443_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc_n(v_a_445_, 2);
lean_dec_ref(v___x_444_);
v___x_446_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_a_445_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v___x_447_; lean_object* v_env_448_; lean_object* v___x_449_; lean_object* v_toEnvExtension_450_; lean_object* v_asyncMode_451_; lean_object* v___x_452_; lean_object* v___y_454_; lean_object* v___y_455_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
lean_dec_ref(v___x_446_);
v___x_447_ = lean_st_ref_get(v___y_438_);
v_env_448_ = lean_ctor_get(v___x_447_, 0);
lean_inc_ref(v_env_448_);
lean_dec(v___x_447_);
v___x_449_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_450_ = lean_ctor_get(v___x_449_, 0);
v_asyncMode_451_ = lean_ctor_get(v_toEnvExtension_450_, 2);
v___x_452_ = lean_box(0);
v___x_497_ = lean_box(1);
v___x_498_ = lean_box(0);
v___x_499_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_497_, v___x_449_, v_env_448_, v_asyncMode_451_, v___x_498_);
v___x_500_ = l_Lean_NameSet_contains(v___x_499_, v_a_445_);
lean_dec(v___x_499_);
if (v___x_500_ == 0)
{
v___y_454_ = v___y_436_;
v___y_455_ = v___y_438_;
goto v___jp_453_;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_501_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v_a_445_);
v___x_502_ = l_Lean_MessageData_ofName(v_a_445_);
v___x_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__5);
v___x_505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_503_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v___x_505_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_dec_ref(v___x_506_);
v___y_454_ = v___y_436_;
v___y_455_ = v___y_438_;
goto v___jp_453_;
}
else
{
lean_dec(v_a_445_);
return v___x_506_;
}
}
v___jp_453_:
{
lean_object* v___x_456_; lean_object* v_toEnvExtension_457_; lean_object* v_env_458_; lean_object* v_nextMacroScope_459_; lean_object* v_ngen_460_; lean_object* v_auxDeclNGen_461_; lean_object* v_traceState_462_; lean_object* v_messages_463_; lean_object* v_infoState_464_; lean_object* v_snapshotTasks_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_495_; 
v___x_456_ = lean_st_ref_take(v___y_455_);
v_toEnvExtension_457_ = lean_ctor_get(v___x_449_, 0);
v_env_458_ = lean_ctor_get(v___x_456_, 0);
v_nextMacroScope_459_ = lean_ctor_get(v___x_456_, 1);
v_ngen_460_ = lean_ctor_get(v___x_456_, 2);
v_auxDeclNGen_461_ = lean_ctor_get(v___x_456_, 3);
v_traceState_462_ = lean_ctor_get(v___x_456_, 4);
v_messages_463_ = lean_ctor_get(v___x_456_, 6);
v_infoState_464_ = lean_ctor_get(v___x_456_, 7);
v_snapshotTasks_465_ = lean_ctor_get(v___x_456_, 8);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; 
v_unused_496_ = lean_ctor_get(v___x_456_, 5);
lean_dec(v_unused_496_);
v___x_467_ = v___x_456_;
v_isShared_468_ = v_isSharedCheck_495_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_snapshotTasks_465_);
lean_inc(v_infoState_464_);
lean_inc(v_messages_463_);
lean_inc(v_traceState_462_);
lean_inc(v_auxDeclNGen_461_);
lean_inc(v_ngen_460_);
lean_inc(v_nextMacroScope_459_);
lean_inc(v_env_458_);
lean_dec(v___x_456_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_495_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v_asyncMode_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v_asyncMode_469_ = lean_ctor_get(v_toEnvExtension_457_, 2);
v___x_470_ = lean_box(0);
v___x_471_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_449_, v_env_458_, v_a_445_, v_asyncMode_469_, v___x_470_);
v___x_472_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2);
if (v_isShared_468_ == 0)
{
lean_ctor_set(v___x_467_, 5, v___x_472_);
lean_ctor_set(v___x_467_, 0, v___x_471_);
v___x_474_ = v___x_467_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_nextMacroScope_459_);
lean_ctor_set(v_reuseFailAlloc_494_, 2, v_ngen_460_);
lean_ctor_set(v_reuseFailAlloc_494_, 3, v_auxDeclNGen_461_);
lean_ctor_set(v_reuseFailAlloc_494_, 4, v_traceState_462_);
lean_ctor_set(v_reuseFailAlloc_494_, 5, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_494_, 6, v_messages_463_);
lean_ctor_set(v_reuseFailAlloc_494_, 7, v_infoState_464_);
lean_ctor_set(v_reuseFailAlloc_494_, 8, v_snapshotTasks_465_);
v___x_474_ = v_reuseFailAlloc_494_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v_mctx_477_; lean_object* v_zetaDeltaFVarIds_478_; lean_object* v_postponed_479_; lean_object* v_diag_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_492_; 
v___x_475_ = lean_st_ref_set(v___y_455_, v___x_474_);
v___x_476_ = lean_st_ref_take(v___y_454_);
v_mctx_477_ = lean_ctor_get(v___x_476_, 0);
v_zetaDeltaFVarIds_478_ = lean_ctor_get(v___x_476_, 2);
v_postponed_479_ = lean_ctor_get(v___x_476_, 3);
v_diag_480_ = lean_ctor_get(v___x_476_, 4);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_492_ == 0)
{
lean_object* v_unused_493_; 
v_unused_493_ = lean_ctor_get(v___x_476_, 1);
lean_dec(v_unused_493_);
v___x_482_ = v___x_476_;
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_diag_480_);
lean_inc(v_postponed_479_);
lean_inc(v_zetaDeltaFVarIds_478_);
lean_inc(v_mctx_477_);
lean_dec(v___x_476_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v___x_484_; lean_object* v___x_486_; 
v___x_484_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v___x_484_);
v___x_486_ = v___x_482_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_mctx_477_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_484_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_zetaDeltaFVarIds_478_);
lean_ctor_set(v_reuseFailAlloc_491_, 3, v_postponed_479_);
lean_ctor_set(v_reuseFailAlloc_491_, 4, v_diag_480_);
v___x_486_ = v_reuseFailAlloc_491_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; size_t v___x_488_; size_t v___x_489_; 
v___x_487_ = lean_st_ref_set(v___y_454_, v___x_486_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_add(v_i_431_, v___x_488_);
v_i_431_ = v___x_489_;
v_b_432_ = v___x_452_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec(v_a_445_);
return v___x_446_;
}
}
else
{
lean_object* v_a_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_a_507_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_514_ == 0)
{
v___x_509_ = v___x_444_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_a_507_);
lean_dec(v___x_444_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_507_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___boxed(lean_object* v_as_515_, lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_b_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
size_t v_sz_boxed_526_; size_t v_i_boxed_527_; lean_object* v_res_528_; 
v_sz_boxed_526_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_527_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(v_as_515_, v_sz_boxed_526_, v_i_boxed_527_, v_b_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v_as_515_);
return v_res_528_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__0));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(lean_object* v_as_532_, size_t v_sz_533_, size_t v_i_534_, lean_object* v_b_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
uint8_t v___x_543_; 
v___x_543_ = lean_usize_dec_lt(v_i_534_, v_sz_533_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v_b_535_);
return v___x_544_;
}
else
{
lean_object* v___x_545_; lean_object* v_env_546_; lean_object* v___x_547_; lean_object* v_toEnvExtension_548_; lean_object* v_asyncMode_549_; lean_object* v___x_550_; lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_545_ = lean_st_ref_get(v___y_541_);
v_env_546_ = lean_ctor_get(v___x_545_, 0);
lean_inc_ref(v_env_546_);
lean_dec(v___x_545_);
v___x_547_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_548_ = lean_ctor_get(v___x_547_, 0);
v_asyncMode_549_ = lean_ctor_get(v_toEnvExtension_548_, 2);
v___x_550_ = lean_box(0);
v_a_551_ = lean_array_uget_borrowed(v_as_532_, v_i_534_);
v___x_552_ = l_Lean_TSyntax_getId(v_a_551_);
v___x_597_ = lean_box(1);
v___x_598_ = lean_box(0);
v___x_599_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_597_, v___x_547_, v_env_546_, v_asyncMode_549_, v___x_598_);
v___x_600_ = l_Lean_NameSet_contains(v___x_599_, v___x_552_);
lean_dec(v___x_599_);
if (v___x_600_ == 0)
{
v___y_554_ = v___y_539_;
v___y_555_ = v___y_541_;
goto v___jp_553_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_601_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v___x_552_);
v___x_602_ = l_Lean_MessageData_ofName(v___x_552_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_601_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___closed__1);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v___x_605_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_dec_ref(v___x_606_);
v___y_554_ = v___y_539_;
v___y_555_ = v___y_541_;
goto v___jp_553_;
}
else
{
lean_dec(v___x_552_);
return v___x_606_;
}
}
v___jp_553_:
{
lean_object* v___x_556_; lean_object* v_toEnvExtension_557_; lean_object* v_env_558_; lean_object* v_nextMacroScope_559_; lean_object* v_ngen_560_; lean_object* v_auxDeclNGen_561_; lean_object* v_traceState_562_; lean_object* v_messages_563_; lean_object* v_infoState_564_; lean_object* v_snapshotTasks_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_595_; 
v___x_556_ = lean_st_ref_take(v___y_555_);
v_toEnvExtension_557_ = lean_ctor_get(v___x_547_, 0);
v_env_558_ = lean_ctor_get(v___x_556_, 0);
v_nextMacroScope_559_ = lean_ctor_get(v___x_556_, 1);
v_ngen_560_ = lean_ctor_get(v___x_556_, 2);
v_auxDeclNGen_561_ = lean_ctor_get(v___x_556_, 3);
v_traceState_562_ = lean_ctor_get(v___x_556_, 4);
v_messages_563_ = lean_ctor_get(v___x_556_, 6);
v_infoState_564_ = lean_ctor_get(v___x_556_, 7);
v_snapshotTasks_565_ = lean_ctor_get(v___x_556_, 8);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v___x_556_, 5);
lean_dec(v_unused_596_);
v___x_567_ = v___x_556_;
v_isShared_568_ = v_isSharedCheck_595_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_snapshotTasks_565_);
lean_inc(v_infoState_564_);
lean_inc(v_messages_563_);
lean_inc(v_traceState_562_);
lean_inc(v_auxDeclNGen_561_);
lean_inc(v_ngen_560_);
lean_inc(v_nextMacroScope_559_);
lean_inc(v_env_558_);
lean_dec(v___x_556_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_595_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_asyncMode_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v_asyncMode_569_ = lean_ctor_get(v_toEnvExtension_557_, 2);
v___x_570_ = lean_box(0);
v___x_571_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_547_, v_env_558_, v___x_552_, v_asyncMode_569_, v___x_570_);
v___x_572_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 5, v___x_572_);
lean_ctor_set(v___x_567_, 0, v___x_571_);
v___x_574_ = v___x_567_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_nextMacroScope_559_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_ngen_560_);
lean_ctor_set(v_reuseFailAlloc_594_, 3, v_auxDeclNGen_561_);
lean_ctor_set(v_reuseFailAlloc_594_, 4, v_traceState_562_);
lean_ctor_set(v_reuseFailAlloc_594_, 5, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_594_, 6, v_messages_563_);
lean_ctor_set(v_reuseFailAlloc_594_, 7, v_infoState_564_);
lean_ctor_set(v_reuseFailAlloc_594_, 8, v_snapshotTasks_565_);
v___x_574_ = v_reuseFailAlloc_594_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v_mctx_577_; lean_object* v_zetaDeltaFVarIds_578_; lean_object* v_postponed_579_; lean_object* v_diag_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_592_; 
v___x_575_ = lean_st_ref_set(v___y_555_, v___x_574_);
v___x_576_ = lean_st_ref_take(v___y_554_);
v_mctx_577_ = lean_ctor_get(v___x_576_, 0);
v_zetaDeltaFVarIds_578_ = lean_ctor_get(v___x_576_, 2);
v_postponed_579_ = lean_ctor_get(v___x_576_, 3);
v_diag_580_ = lean_ctor_get(v___x_576_, 4);
v_isSharedCheck_592_ = !lean_is_exclusive(v___x_576_);
if (v_isSharedCheck_592_ == 0)
{
lean_object* v_unused_593_; 
v_unused_593_ = lean_ctor_get(v___x_576_, 1);
lean_dec(v_unused_593_);
v___x_582_ = v___x_576_;
v_isShared_583_ = v_isSharedCheck_592_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_diag_580_);
lean_inc(v_postponed_579_);
lean_inc(v_zetaDeltaFVarIds_578_);
lean_inc(v_mctx_577_);
lean_dec(v___x_576_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_592_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v___x_586_; 
v___x_584_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 1, v___x_584_);
v___x_586_ = v___x_582_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_mctx_577_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_584_);
lean_ctor_set(v_reuseFailAlloc_591_, 2, v_zetaDeltaFVarIds_578_);
lean_ctor_set(v_reuseFailAlloc_591_, 3, v_postponed_579_);
lean_ctor_set(v_reuseFailAlloc_591_, 4, v_diag_580_);
v___x_586_ = v_reuseFailAlloc_591_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; size_t v___x_588_; size_t v___x_589_; 
v___x_587_ = lean_st_ref_set(v___y_554_, v___x_586_);
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_add(v_i_534_, v___x_588_);
v_i_534_ = v___x_589_;
v_b_535_ = v___x_550_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2___boxed(lean_object* v_as_607_, lean_object* v_sz_608_, lean_object* v_i_609_, lean_object* v_b_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
size_t v_sz_boxed_618_; size_t v_i_boxed_619_; lean_object* v_res_620_; 
v_sz_boxed_618_ = lean_unbox_usize(v_sz_608_);
lean_dec(v_sz_608_);
v_i_boxed_619_ = lean_unbox_usize(v_i_609_);
lean_dec(v_i_609_);
v_res_620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(v_as_607_, v_sz_boxed_618_, v_i_boxed_619_, v_b_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec_ref(v_as_607_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(uint8_t v___y_621_, lean_object* v_ids_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
if (v___y_621_ == 0)
{
lean_object* v___x_630_; size_t v_sz_631_; size_t v___x_632_; lean_object* v___x_633_; 
v___x_630_ = lean_box(0);
v_sz_631_ = lean_array_size(v_ids_622_);
v___x_632_ = ((size_t)0ULL);
v___x_633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1(v_ids_622_, v_sz_631_, v___x_632_, v___x_630_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_640_; 
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_640_ == 0)
{
lean_object* v_unused_641_; 
v_unused_641_ = lean_ctor_get(v___x_633_, 0);
lean_dec(v_unused_641_);
v___x_635_ = v___x_633_;
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
else
{
lean_dec(v___x_633_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_640_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
lean_object* v___x_638_; 
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_630_);
v___x_638_ = v___x_635_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_630_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
else
{
return v___x_633_;
}
}
else
{
lean_object* v___x_642_; size_t v_sz_643_; size_t v___x_644_; lean_object* v___x_645_; 
v___x_642_ = lean_box(0);
v_sz_643_ = lean_array_size(v_ids_622_);
v___x_644_ = ((size_t)0ULL);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__2(v_ids_622_, v_sz_643_, v___x_644_, v___x_642_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_);
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_652_; 
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v___x_645_, 0);
lean_dec(v_unused_653_);
v___x_647_ = v___x_645_;
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
else
{
lean_dec(v___x_645_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_652_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_650_; 
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_642_);
v___x_650_ = v___x_647_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_642_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
return v___x_645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed(lean_object* v___y_654_, lean_object* v_ids_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
uint8_t v___y_8781__boxed_663_; lean_object* v_res_664_; 
v___y_8781__boxed_663_ = lean_unbox(v___y_654_);
v_res_664_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0(v___y_8781__boxed_663_, v_ids_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v_ids_655_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(lean_object* v_stx_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; uint8_t v___y_678_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___x_687_; uint8_t v___x_688_; lean_object* v_sfx_x3f_690_; lean_object* v___y_691_; lean_object* v___y_692_; 
v___x_687_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1));
lean_inc(v_stx_670_);
v___x_688_ = l_Lean_Syntax_isOfKind(v_stx_670_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_696_; 
lean_dec(v_stx_670_);
v___x_696_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
return v___x_696_;
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_697_ = lean_unsigned_to_nat(2u);
v___x_698_ = l_Lean_Syntax_getArg(v_stx_670_, v___x_697_);
v___x_699_ = l_Lean_Syntax_isNone(v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_700_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_698_);
v___x_701_ = l_Lean_Syntax_matchesNull(v___x_698_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; 
lean_dec(v___x_698_);
lean_dec(v_stx_670_);
v___x_702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
return v___x_702_;
}
else
{
lean_object* v___x_703_; lean_object* v_sfx_x3f_704_; lean_object* v___x_705_; 
v___x_703_ = lean_unsigned_to_nat(0u);
v_sfx_x3f_704_ = l_Lean_Syntax_getArg(v___x_698_, v___x_703_);
lean_dec(v___x_698_);
v___x_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_705_, 0, v_sfx_x3f_704_);
v_sfx_x3f_690_ = v___x_705_;
v___y_691_ = v_a_671_;
v___y_692_ = v_a_672_;
goto v___jp_689_;
}
}
else
{
lean_object* v___x_706_; 
lean_dec(v___x_698_);
v___x_706_ = lean_box(0);
v_sfx_x3f_690_ = v___x_706_;
v___y_691_ = v_a_671_;
v___y_692_ = v_a_672_;
goto v___jp_689_;
}
}
v___jp_674_:
{
lean_object* v___x_679_; lean_object* v___y_680_; lean_object* v___x_681_; 
v___x_679_ = lean_box(v___y_678_);
v___y_680_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___lam__0___boxed), 9, 2);
lean_closure_set(v___y_680_, 0, v___x_679_);
lean_closure_set(v___y_680_, 1, v___y_675_);
v___x_681_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_680_, v___y_676_, v___y_677_);
return v___x_681_;
}
v___jp_682_:
{
uint8_t v___x_686_; 
v___x_686_ = 0;
v___y_675_ = v___y_684_;
v___y_676_ = v___y_683_;
v___y_677_ = v___y_685_;
v___y_678_ = v___x_686_;
goto v___jp_674_;
}
v___jp_689_:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_ids_695_; 
v___x_693_ = lean_unsigned_to_nat(3u);
v___x_694_ = l_Lean_Syntax_getArg(v_stx_670_, v___x_693_);
lean_dec(v_stx_670_);
v_ids_695_ = l_Lean_Syntax_getArgs(v___x_694_);
lean_dec(v___x_694_);
if (lean_obj_tag(v_sfx_x3f_690_) == 0)
{
v___y_683_ = v___y_691_;
v___y_684_ = v_ids_695_;
v___y_685_ = v___y_692_;
goto v___jp_682_;
}
else
{
lean_dec_ref(v_sfx_x3f_690_);
if (v___x_688_ == 0)
{
v___y_683_ = v___y_691_;
v___y_684_ = v_ids_695_;
v___y_685_ = v___y_692_;
goto v___jp_682_;
}
else
{
v___y_675_ = v_ids_695_;
v___y_676_ = v___y_691_;
v___y_677_ = v___y_692_;
v___y_678_ = v___x_688_;
goto v___jp_674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed(lean_object* v_stx_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip(v_stx_707_, v_a_708_, v_a_709_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0(lean_object* v_00_u03b1_712_, lean_object* v_msg_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v_msg_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___boxed(lean_object* v_00_u03b1_722_, lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0(v_00_u03b1_722_, v_msg_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1(lean_object* v_msgData_732_, lean_object* v_macroStack_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___redArg(v_msgData_732_, v_macroStack_733_, v___y_738_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1___boxed(lean_object* v_msgData_742_, lean_object* v_macroStack_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1(v_msgData_742_, v_macroStack_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1(){
_start:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_757_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_758_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___closed__1));
v___x_759_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___closed__1));
v___x_760_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___boxed), 4, 0);
v___x_761_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_757_, v___x_758_, v___x_759_, v___x_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1___boxed(lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip__1();
return v_res_763_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__0));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(lean_object* v_as_767_, size_t v_sz_768_, size_t v_i_769_, lean_object* v_b_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
uint8_t v___x_778_; 
v___x_778_ = lean_usize_dec_lt(v_i_769_, v_sz_768_);
if (v___x_778_ == 0)
{
lean_object* v___x_779_; 
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v_b_770_);
return v___x_779_;
}
else
{
lean_object* v_a_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_a_780_ = lean_array_uget_borrowed(v_as_767_, v_i_769_);
v___x_781_ = lean_box(0);
lean_inc(v_a_780_);
v___x_782_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_780_, v___x_781_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc_n(v_a_783_, 2);
lean_dec_ref(v___x_782_);
v___x_784_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem(v_a_783_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v___x_785_; lean_object* v_env_786_; lean_object* v___x_787_; lean_object* v_toEnvExtension_788_; lean_object* v_asyncMode_789_; lean_object* v___x_790_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; 
lean_dec_ref(v___x_784_);
v___x_785_ = lean_st_ref_get(v___y_776_);
v_env_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc_ref(v_env_786_);
lean_dec(v___x_785_);
v___x_787_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_788_ = lean_ctor_get(v___x_787_, 0);
v_asyncMode_789_ = lean_ctor_get(v_toEnvExtension_788_, 2);
v___x_790_ = lean_box(0);
v___x_835_ = lean_box(1);
v___x_836_ = lean_box(0);
v___x_837_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_835_, v___x_787_, v_env_786_, v_asyncMode_789_, v___x_836_);
v___x_838_ = l_Lean_NameSet_contains(v___x_837_, v_a_783_);
lean_dec(v___x_837_);
if (v___x_838_ == 0)
{
v___y_792_ = v___y_774_;
v___y_793_ = v___y_776_;
goto v___jp_791_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_839_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
lean_inc(v_a_783_);
v___x_840_ = l_Lean_MessageData_ofName(v_a_783_);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___closed__1);
v___x_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0___redArg(v___x_843_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_dec_ref(v___x_844_);
v___y_792_ = v___y_774_;
v___y_793_ = v___y_776_;
goto v___jp_791_;
}
else
{
lean_dec(v_a_783_);
return v___x_844_;
}
}
v___jp_791_:
{
lean_object* v___x_794_; lean_object* v_toEnvExtension_795_; lean_object* v_env_796_; lean_object* v_nextMacroScope_797_; lean_object* v_ngen_798_; lean_object* v_auxDeclNGen_799_; lean_object* v_traceState_800_; lean_object* v_messages_801_; lean_object* v_infoState_802_; lean_object* v_snapshotTasks_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_833_; 
v___x_794_ = lean_st_ref_take(v___y_793_);
v_toEnvExtension_795_ = lean_ctor_get(v___x_787_, 0);
v_env_796_ = lean_ctor_get(v___x_794_, 0);
v_nextMacroScope_797_ = lean_ctor_get(v___x_794_, 1);
v_ngen_798_ = lean_ctor_get(v___x_794_, 2);
v_auxDeclNGen_799_ = lean_ctor_get(v___x_794_, 3);
v_traceState_800_ = lean_ctor_get(v___x_794_, 4);
v_messages_801_ = lean_ctor_get(v___x_794_, 6);
v_infoState_802_ = lean_ctor_get(v___x_794_, 7);
v_snapshotTasks_803_ = lean_ctor_get(v___x_794_, 8);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v___x_794_, 5);
lean_dec(v_unused_834_);
v___x_805_ = v___x_794_;
v_isShared_806_ = v_isSharedCheck_833_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_snapshotTasks_803_);
lean_inc(v_infoState_802_);
lean_inc(v_messages_801_);
lean_inc(v_traceState_800_);
lean_inc(v_auxDeclNGen_799_);
lean_inc(v_ngen_798_);
lean_inc(v_nextMacroScope_797_);
lean_inc(v_env_796_);
lean_dec(v___x_794_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_833_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_asyncMode_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
v_asyncMode_807_ = lean_ctor_get(v_toEnvExtension_795_, 2);
v___x_808_ = lean_box(0);
v___x_809_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_787_, v_env_796_, v_a_783_, v_asyncMode_807_, v___x_808_);
v___x_810_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__2);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 5, v___x_810_);
lean_ctor_set(v___x_805_, 0, v___x_809_);
v___x_812_ = v___x_805_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_nextMacroScope_797_);
lean_ctor_set(v_reuseFailAlloc_832_, 2, v_ngen_798_);
lean_ctor_set(v_reuseFailAlloc_832_, 3, v_auxDeclNGen_799_);
lean_ctor_set(v_reuseFailAlloc_832_, 4, v_traceState_800_);
lean_ctor_set(v_reuseFailAlloc_832_, 5, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_832_, 6, v_messages_801_);
lean_ctor_set(v_reuseFailAlloc_832_, 7, v_infoState_802_);
lean_ctor_set(v_reuseFailAlloc_832_, 8, v_snapshotTasks_803_);
v___x_812_ = v_reuseFailAlloc_832_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v_mctx_815_; lean_object* v_zetaDeltaFVarIds_816_; lean_object* v_postponed_817_; lean_object* v_diag_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_830_; 
v___x_813_ = lean_st_ref_set(v___y_793_, v___x_812_);
v___x_814_ = lean_st_ref_take(v___y_792_);
v_mctx_815_ = lean_ctor_get(v___x_814_, 0);
v_zetaDeltaFVarIds_816_ = lean_ctor_get(v___x_814_, 2);
v_postponed_817_ = lean_ctor_get(v___x_814_, 3);
v_diag_818_ = lean_ctor_get(v___x_814_, 4);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_830_ == 0)
{
lean_object* v_unused_831_; 
v_unused_831_ = lean_ctor_get(v___x_814_, 1);
lean_dec(v_unused_831_);
v___x_820_ = v___x_814_;
v_isShared_821_ = v_isSharedCheck_830_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_diag_818_);
lean_inc(v_postponed_817_);
lean_inc(v_zetaDeltaFVarIds_816_);
lean_inc(v_mctx_815_);
lean_dec(v___x_814_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_830_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_822_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__1___closed__3);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v___x_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_mctx_815_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_822_);
lean_ctor_set(v_reuseFailAlloc_829_, 2, v_zetaDeltaFVarIds_816_);
lean_ctor_set(v_reuseFailAlloc_829_, 3, v_postponed_817_);
lean_ctor_set(v_reuseFailAlloc_829_, 4, v_diag_818_);
v___x_824_ = v_reuseFailAlloc_829_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
lean_object* v___x_825_; size_t v___x_826_; size_t v___x_827_; 
v___x_825_ = lean_st_ref_set(v___y_792_, v___x_824_);
v___x_826_ = ((size_t)1ULL);
v___x_827_ = lean_usize_add(v_i_769_, v___x_826_);
v_i_769_ = v___x_827_;
v_b_770_ = v___x_790_;
goto _start;
}
}
}
}
}
}
else
{
lean_dec(v_a_783_);
return v___x_784_;
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_782_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_782_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0___boxed(lean_object* v_as_853_, lean_object* v_sz_854_, lean_object* v_i_855_, lean_object* v_b_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
size_t v_sz_boxed_864_; size_t v_i_boxed_865_; lean_object* v_res_866_; 
v_sz_boxed_864_ = lean_unbox_usize(v_sz_854_);
lean_dec(v_sz_854_);
v_i_boxed_865_ = lean_unbox_usize(v_i_855_);
lean_dec(v_i_855_);
v_res_866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(v_as_853_, v_sz_boxed_864_, v_i_boxed_865_, v_b_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_, v___y_862_);
lean_dec(v___y_862_);
lean_dec_ref(v___y_861_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec_ref(v_as_853_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(lean_object* v_ids_867_, size_t v_sz_868_, size_t v___x_869_, lean_object* v___x_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute_spec__0(v_ids_867_, v_sz_868_, v___x_869_, v___x_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v___x_878_, 0);
lean_dec(v_unused_886_);
v___x_880_ = v___x_878_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_dec(v___x_878_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_870_);
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_870_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
else
{
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed(lean_object* v_ids_887_, lean_object* v_sz_888_, lean_object* v___x_889_, lean_object* v___x_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
size_t v_sz_boxed_898_; size_t v___x_3710__boxed_899_; lean_object* v_res_900_; 
v_sz_boxed_898_ = lean_unbox_usize(v_sz_888_);
lean_dec(v_sz_888_);
v___x_3710__boxed_899_ = lean_unbox_usize(v___x_889_);
lean_dec(v___x_889_);
v_res_900_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0(v_ids_887_, v_sz_boxed_898_, v___x_3710__boxed_899_, v___x_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
lean_dec(v___y_896_);
lean_dec_ref(v___y_895_);
lean_dec(v___y_894_);
lean_dec_ref(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec_ref(v_ids_887_);
return v_res_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(lean_object* v_stx_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1));
lean_inc(v_stx_908_);
v___x_913_ = l_Lean_Syntax_isOfKind(v_stx_908_, v___x_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
lean_dec(v_stx_908_);
v___x_914_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg();
return v___x_914_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v_ids_917_; lean_object* v___x_918_; size_t v_sz_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___f_922_; lean_object* v___x_923_; 
v___x_915_ = lean_unsigned_to_nat(2u);
v___x_916_ = l_Lean_Syntax_getArg(v_stx_908_, v___x_915_);
lean_dec(v_stx_908_);
v_ids_917_ = l_Lean_Syntax_getArgs(v___x_916_);
lean_dec(v___x_916_);
v___x_918_ = lean_box(0);
v_sz_919_ = lean_array_size(v_ids_917_);
v___x_920_ = lean_box_usize(v_sz_919_);
v___x_921_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed__const__1));
v___f_922_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___lam__0___boxed), 11, 4);
lean_closure_set(v___f_922_, 0, v_ids_917_);
lean_closure_set(v___f_922_, 1, v___x_920_);
lean_closure_set(v___f_922_, 2, v___x_921_);
lean_closure_set(v___f_922_, 3, v___x_918_);
v___x_923_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_922_, v_a_909_, v_a_910_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed(lean_object* v_stx_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute(v_stx_924_, v_a_925_, v_a_926_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1(){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_934_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_935_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___closed__1));
v___x_936_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___closed__1));
v___x_937_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___boxed), 4, 0);
v___x_938_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_934_, v___x_935_, v___x_936_, v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1___boxed(lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintMute__1();
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(lean_object* v_items_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_defaultConfig));
v___x_964_ = l_Lean_Elab_Tactic_Grind_elabConfigItems(v___x_963_, v_items_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig___boxed(lean_object* v_items_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(v_items_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_);
lean_dec(v_a_971_);
lean_dec_ref(v_a_970_);
lean_dec(v_a_969_);
lean_dec_ref(v_a_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec_ref(v_items_965_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(lean_object* v_init_974_, lean_object* v_x_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
if (lean_obj_tag(v_x_975_) == 0)
{
lean_object* v_k_981_; lean_object* v_l_982_; lean_object* v_r_983_; lean_object* v___x_984_; 
v_k_981_ = lean_ctor_get(v_x_975_, 1);
lean_inc(v_k_981_);
v_l_982_ = lean_ctor_get(v_x_975_, 3);
lean_inc(v_l_982_);
v_r_983_ = lean_ctor_get(v_x_975_, 4);
lean_inc(v_r_983_);
lean_dec_ref(v_x_975_);
v___x_984_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_init_974_, v_l_982_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v_a_986_; lean_object* v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref(v___x_984_);
v_a_986_ = lean_ctor_get(v_a_985_, 0);
lean_inc_n(v_a_986_, 2);
lean_dec(v_a_985_);
v___x_987_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_a_986_, v_k_981_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
if (lean_obj_tag(v___x_987_) == 0)
{
lean_object* v_a_988_; 
lean_dec(v_a_986_);
v_a_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_a_988_);
lean_dec_ref(v___x_987_);
v_init_974_ = v_a_988_;
v_x_975_ = v_r_983_;
goto _start;
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1002_; 
v_a_990_ = lean_ctor_get(v___x_987_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_987_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_992_ = v___x_987_;
v_isShared_993_ = v_isSharedCheck_1002_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_987_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1002_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
uint8_t v___y_995_; uint8_t v___x_1000_; 
v___x_1000_ = l_Lean_Exception_isInterrupt(v_a_990_);
if (v___x_1000_ == 0)
{
uint8_t v___x_1001_; 
lean_inc(v_a_990_);
v___x_1001_ = l_Lean_Exception_isRuntime(v_a_990_);
v___y_995_ = v___x_1001_;
goto v___jp_994_;
}
else
{
v___y_995_ = v___x_1000_;
goto v___jp_994_;
}
v___jp_994_:
{
if (v___y_995_ == 0)
{
lean_del_object(v___x_992_);
lean_dec(v_a_990_);
v_init_974_ = v_a_986_;
v_x_975_ = v_r_983_;
goto _start;
}
else
{
lean_object* v___x_998_; 
lean_dec(v_a_986_);
lean_dec(v_r_983_);
if (v_isShared_993_ == 0)
{
v___x_998_ = v___x_992_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_990_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
}
else
{
lean_dec(v_r_983_);
lean_dec(v_k_981_);
return v___x_984_;
}
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1003_, 0, v_init_974_);
v___x_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0___boxed(lean_object* v_init_1005_, lean_object* v_x_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_init_1005_, v_x_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(lean_object* v_config_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Meta_Grind_mkDefaultParams(v_config_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1088_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1088_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1088_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v_config_1025_; lean_object* v_extensions_1026_; lean_object* v_extra_1027_; lean_object* v_extraInj_1028_; lean_object* v_extraFacts_1029_; lean_object* v_symPrios_1030_; lean_object* v_norm_1031_; lean_object* v_normProcs_1032_; lean_object* v_anchorRefs_x3f_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1087_; 
v___x_1024_ = lean_st_ref_get(v_a_1017_);
v_config_1025_ = lean_ctor_get(v_a_1020_, 0);
v_extensions_1026_ = lean_ctor_get(v_a_1020_, 1);
v_extra_1027_ = lean_ctor_get(v_a_1020_, 2);
v_extraInj_1028_ = lean_ctor_get(v_a_1020_, 3);
v_extraFacts_1029_ = lean_ctor_get(v_a_1020_, 4);
v_symPrios_1030_ = lean_ctor_get(v_a_1020_, 5);
v_norm_1031_ = lean_ctor_get(v_a_1020_, 6);
v_normProcs_1032_ = lean_ctor_get(v_a_1020_, 7);
v_anchorRefs_x3f_1033_ = lean_ctor_get(v_a_1020_, 8);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_a_1020_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1035_ = v_a_1020_;
v_isShared_1036_ = v_isSharedCheck_1087_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_anchorRefs_x3f_1033_);
lean_inc(v_normProcs_1032_);
lean_inc(v_norm_1031_);
lean_inc(v_symPrios_1030_);
lean_inc(v_extraFacts_1029_);
lean_inc(v_extraInj_1028_);
lean_inc(v_extra_1027_);
lean_inc(v_extensions_1026_);
lean_inc(v_config_1025_);
lean_dec(v_a_1020_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1087_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___y_1038_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_ematch_1048_; lean_object* v_env_1049_; lean_object* v___x_1050_; lean_object* v_toEnvExtension_1051_; lean_object* v_asyncMode_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1045_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = lean_array_get_borrowed(v___x_1045_, v_extensions_1026_, v___x_1046_);
v_ematch_1048_ = lean_ctor_get(v___x_1047_, 3);
v_env_1049_ = lean_ctor_get(v___x_1024_, 0);
lean_inc_ref(v_env_1049_);
lean_dec(v___x_1024_);
v___x_1050_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_muteExt;
v_toEnvExtension_1051_ = lean_ctor_get(v___x_1050_, 0);
v_asyncMode_1052_ = lean_ctor_get(v_toEnvExtension_1051_, 2);
v___x_1053_ = lean_box(1);
v___x_1054_ = lean_box(0);
v___x_1055_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1053_, v___x_1050_, v_env_1049_, v_asyncMode_1052_, v___x_1054_);
lean_inc_ref(v_ematch_1048_);
v___x_1056_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams_spec__0(v_ematch_1048_, v___x_1055_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v_a_1059_; lean_object* v_a_1078_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref(v___x_1056_);
v_a_1078_ = lean_ctor_get(v_a_1057_, 0);
lean_inc(v_a_1078_);
lean_dec(v_a_1057_);
v_a_1059_ = v_a_1078_;
goto v___jp_1058_;
v___jp_1058_:
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_array_get_size(v_extensions_1026_);
v___x_1061_ = lean_nat_dec_lt(v___x_1046_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec_ref(v_a_1059_);
v___y_1038_ = v_extensions_1026_;
goto v___jp_1037_;
}
else
{
lean_object* v_v_1062_; lean_object* v_casesTypes_1063_; lean_object* v_extThms_1064_; lean_object* v_funCC_1065_; lean_object* v_inj_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1076_; 
v_v_1062_ = lean_array_fget(v_extensions_1026_, v___x_1046_);
v_casesTypes_1063_ = lean_ctor_get(v_v_1062_, 0);
v_extThms_1064_ = lean_ctor_get(v_v_1062_, 1);
v_funCC_1065_ = lean_ctor_get(v_v_1062_, 2);
v_inj_1066_ = lean_ctor_get(v_v_1062_, 4);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_v_1062_);
if (v_isSharedCheck_1076_ == 0)
{
lean_object* v_unused_1077_; 
v_unused_1077_ = lean_ctor_get(v_v_1062_, 3);
lean_dec(v_unused_1077_);
v___x_1068_ = v_v_1062_;
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_inj_1066_);
lean_inc(v_funCC_1065_);
lean_inc(v_extThms_1064_);
lean_inc(v_casesTypes_1063_);
lean_dec(v_v_1062_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1076_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v_xs_x27_1071_; lean_object* v___x_1073_; 
v___x_1070_ = lean_box(0);
v_xs_x27_1071_ = lean_array_fset(v_extensions_1026_, v___x_1046_, v___x_1070_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 3, v_a_1059_);
v___x_1073_ = v___x_1068_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_casesTypes_1063_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v_extThms_1064_);
lean_ctor_set(v_reuseFailAlloc_1075_, 2, v_funCC_1065_);
lean_ctor_set(v_reuseFailAlloc_1075_, 3, v_a_1059_);
lean_ctor_set(v_reuseFailAlloc_1075_, 4, v_inj_1066_);
v___x_1073_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_array_fset(v_xs_x27_1071_, v___x_1046_, v___x_1073_);
v___y_1038_ = v___x_1074_;
goto v___jp_1037_;
}
}
}
}
}
else
{
lean_object* v_a_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1086_; 
lean_del_object(v___x_1035_);
lean_dec(v_anchorRefs_x3f_1033_);
lean_dec_ref(v_normProcs_1032_);
lean_dec_ref(v_norm_1031_);
lean_dec_ref(v_symPrios_1030_);
lean_dec_ref(v_extraFacts_1029_);
lean_dec_ref(v_extraInj_1028_);
lean_dec_ref(v_extra_1027_);
lean_dec_ref(v_extensions_1026_);
lean_dec_ref(v_config_1025_);
lean_del_object(v___x_1022_);
v_a_1079_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1081_ = v___x_1056_;
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_a_1079_);
lean_dec(v___x_1056_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1086_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1084_; 
if (v_isShared_1082_ == 0)
{
v___x_1084_ = v___x_1081_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
v___jp_1037_:
{
lean_object* v___x_1040_; 
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 1, v___y_1038_);
v___x_1040_ = v___x_1035_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_config_1025_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v___y_1038_);
lean_ctor_set(v_reuseFailAlloc_1044_, 2, v_extra_1027_);
lean_ctor_set(v_reuseFailAlloc_1044_, 3, v_extraInj_1028_);
lean_ctor_set(v_reuseFailAlloc_1044_, 4, v_extraFacts_1029_);
lean_ctor_set(v_reuseFailAlloc_1044_, 5, v_symPrios_1030_);
lean_ctor_set(v_reuseFailAlloc_1044_, 6, v_norm_1031_);
lean_ctor_set(v_reuseFailAlloc_1044_, 7, v_normProcs_1032_);
lean_ctor_set(v_reuseFailAlloc_1044_, 8, v_anchorRefs_x3f_1033_);
v___x_1040_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1042_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1040_);
v___x_1042_ = v___x_1022_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
}
else
{
return v___x_1019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams___boxed(lean_object* v_config_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_config_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_);
lean_dec(v_a_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(lean_object* v_x_1096_, lean_object* v_____s_1097_){
_start:
{
lean_object* v_snd_1098_; lean_object* v_r_1099_; lean_object* v___x_1100_; 
v_snd_1098_ = lean_ctor_get(v_x_1096_, 1);
v_r_1099_ = lean_nat_add(v_____s_1097_, v_snd_1098_);
v___x_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1100_, 0, v_r_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0___boxed(lean_object* v_x_1101_, lean_object* v_____s_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___lam__0(v_x_1101_, v_____s_1102_);
lean_dec(v_____s_1102_);
lean_dec_ref(v_x_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0(lean_object* v_f_1104_, lean_object* v_s_1105_, lean_object* v_a_1106_, lean_object* v_b_1107_){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_a_1106_);
lean_ctor_set(v___x_1108_, 1, v_b_1107_);
v___x_1109_ = lean_apply_2(v_f_1104_, v___x_1108_, v_s_1105_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1109_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1109_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1109_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1109_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_1126_, lean_object* v_keys_1127_, lean_object* v_vals_1128_, lean_object* v_i_1129_, lean_object* v_acc_1130_){
_start:
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = lean_array_get_size(v_keys_1127_);
v___x_1132_ = lean_nat_dec_lt(v_i_1129_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec(v_i_1129_);
lean_dec_ref(v_f_1126_);
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v_acc_1130_);
return v___x_1133_;
}
else
{
lean_object* v_k_1134_; lean_object* v_v_1135_; lean_object* v___x_1136_; 
v_k_1134_ = lean_array_fget_borrowed(v_keys_1127_, v_i_1129_);
v_v_1135_ = lean_array_fget_borrowed(v_vals_1128_, v_i_1129_);
lean_inc_ref(v_f_1126_);
lean_inc(v_v_1135_);
lean_inc(v_k_1134_);
v___x_1136_ = lean_apply_3(v_f_1126_, v_acc_1130_, v_k_1134_, v_v_1135_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_dec(v_i_1129_);
lean_dec_ref(v_f_1126_);
return v___x_1136_;
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref(v___x_1136_);
v___x_1138_ = lean_unsigned_to_nat(1u);
v___x_1139_ = lean_nat_add(v_i_1129_, v___x_1138_);
lean_dec(v_i_1129_);
v_i_1129_ = v___x_1139_;
v_acc_1130_ = v_a_1137_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_1141_, lean_object* v_keys_1142_, lean_object* v_vals_1143_, lean_object* v_i_1144_, lean_object* v_acc_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1141_, v_keys_1142_, v_vals_1143_, v_i_1144_, v_acc_1145_);
lean_dec_ref(v_vals_1143_);
lean_dec_ref(v_keys_1142_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1147_, lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
if (lean_obj_tag(v_x_1148_) == 0)
{
lean_object* v_es_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1170_; 
v_es_1150_ = lean_ctor_get(v_x_1148_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_x_1148_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1152_ = v_x_1148_;
v_isShared_1153_ = v_isSharedCheck_1170_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_es_1150_);
lean_dec(v_x_1148_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1170_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1154_ = lean_unsigned_to_nat(0u);
v___x_1155_ = lean_array_get_size(v_es_1150_);
v___x_1156_ = lean_nat_dec_lt(v___x_1154_, v___x_1155_);
if (v___x_1156_ == 0)
{
lean_object* v___x_1158_; 
lean_dec_ref(v_es_1150_);
lean_dec_ref(v_f_1147_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 1);
lean_ctor_set(v___x_1152_, 0, v_x_1149_);
v___x_1158_ = v___x_1152_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_x_1149_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_nat_dec_le(v___x_1155_, v___x_1155_);
if (v___x_1160_ == 0)
{
if (v___x_1156_ == 0)
{
lean_object* v___x_1162_; 
lean_dec_ref(v_es_1150_);
lean_dec_ref(v_f_1147_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 1);
lean_ctor_set(v___x_1152_, 0, v_x_1149_);
v___x_1162_ = v___x_1152_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_x_1149_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
else
{
size_t v___x_1164_; size_t v___x_1165_; lean_object* v___x_1166_; 
lean_del_object(v___x_1152_);
v___x_1164_ = ((size_t)0ULL);
v___x_1165_ = lean_usize_of_nat(v___x_1155_);
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1147_, v_es_1150_, v___x_1164_, v___x_1165_, v_x_1149_);
lean_dec_ref(v_es_1150_);
return v___x_1166_;
}
}
else
{
size_t v___x_1167_; size_t v___x_1168_; lean_object* v___x_1169_; 
lean_del_object(v___x_1152_);
v___x_1167_ = ((size_t)0ULL);
v___x_1168_ = lean_usize_of_nat(v___x_1155_);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1147_, v_es_1150_, v___x_1167_, v___x_1168_, v_x_1149_);
lean_dec_ref(v_es_1150_);
return v___x_1169_;
}
}
}
}
else
{
lean_object* v_ks_1171_; lean_object* v_vs_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v_ks_1171_ = lean_ctor_get(v_x_1148_, 0);
lean_inc_ref(v_ks_1171_);
v_vs_1172_ = lean_ctor_get(v_x_1148_, 1);
lean_inc_ref(v_vs_1172_);
lean_dec_ref(v_x_1148_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1147_, v_ks_1171_, v_vs_1172_, v___x_1173_, v_x_1149_);
lean_dec_ref(v_vs_1172_);
lean_dec_ref(v_ks_1171_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_1175_, lean_object* v_as_1176_, size_t v_i_1177_, size_t v_stop_1178_, lean_object* v_b_1179_){
_start:
{
lean_object* v_a_1181_; lean_object* v___y_1186_; uint8_t v___x_1188_; 
v___x_1188_ = lean_usize_dec_eq(v_i_1177_, v_stop_1178_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; 
v___x_1189_ = lean_array_uget_borrowed(v_as_1176_, v_i_1177_);
switch(lean_obj_tag(v___x_1189_))
{
case 0:
{
lean_object* v_key_1190_; lean_object* v_val_1191_; lean_object* v___x_1192_; 
v_key_1190_ = lean_ctor_get(v___x_1189_, 0);
v_val_1191_ = lean_ctor_get(v___x_1189_, 1);
lean_inc_ref(v_f_1175_);
lean_inc(v_val_1191_);
lean_inc(v_key_1190_);
v___x_1192_ = lean_apply_3(v_f_1175_, v_b_1179_, v_key_1190_, v_val_1191_);
v___y_1186_ = v___x_1192_;
goto v___jp_1185_;
}
case 1:
{
lean_object* v_node_1193_; lean_object* v___x_1194_; 
v_node_1193_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_node_1193_);
lean_inc_ref(v_f_1175_);
v___x_1194_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1175_, v_node_1193_, v_b_1179_);
v___y_1186_ = v___x_1194_;
goto v___jp_1185_;
}
default: 
{
v_a_1181_ = v_b_1179_;
goto v___jp_1180_;
}
}
}
else
{
lean_object* v___x_1195_; 
lean_dec_ref(v_f_1175_);
v___x_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1195_, 0, v_b_1179_);
return v___x_1195_;
}
v___jp_1180_:
{
size_t v___x_1182_; size_t v___x_1183_; 
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_add(v_i_1177_, v___x_1182_);
v_i_1177_ = v___x_1183_;
v_b_1179_ = v_a_1181_;
goto _start;
}
v___jp_1185_:
{
if (lean_obj_tag(v___y_1186_) == 0)
{
lean_dec_ref(v_f_1175_);
return v___y_1186_;
}
else
{
lean_object* v_a_1187_; 
v_a_1187_ = lean_ctor_get(v___y_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref(v___y_1186_);
v_a_1181_ = v_a_1187_;
goto v___jp_1180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_1196_, lean_object* v_as_1197_, lean_object* v_i_1198_, lean_object* v_stop_1199_, lean_object* v_b_1200_){
_start:
{
size_t v_i_boxed_1201_; size_t v_stop_boxed_1202_; lean_object* v_res_1203_; 
v_i_boxed_1201_ = lean_unbox_usize(v_i_1198_);
lean_dec(v_i_1198_);
v_stop_boxed_1202_ = lean_unbox_usize(v_stop_1199_);
lean_dec(v_stop_1199_);
v_res_1203_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1196_, v_as_1197_, v_i_boxed_1201_, v_stop_boxed_1202_, v_b_1200_);
lean_dec_ref(v_as_1197_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(lean_object* v_map_1204_, lean_object* v_init_1205_, lean_object* v_f_1206_){
_start:
{
lean_object* v___f_1207_; lean_object* v___x_1208_; lean_object* v_a_1209_; 
v___f_1207_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1207_, 0, v_f_1206_);
lean_inc_ref(v_map_1204_);
v___x_1208_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v___f_1207_, v_map_1204_, v_init_1205_);
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref(v___x_1208_);
return v_a_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg___boxed(lean_object* v_map_1210_, lean_object* v_init_1211_, lean_object* v_f_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_map_1210_, v_init_1211_, v_f_1212_);
lean_dec_ref(v_map_1210_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(lean_object* v_cs_1215_){
_start:
{
lean_object* v___f_1216_; lean_object* v_r_1217_; lean_object* v___x_1218_; 
v___f_1216_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___closed__0));
v_r_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_cs_1215_, v_r_1217_, v___f_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum___boxed(lean_object* v_cs_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(v_cs_1219_);
lean_dec_ref(v_cs_1219_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(lean_object* v_00_u03c3_1221_, lean_object* v_00_u03b2_1222_, lean_object* v_map_1223_, lean_object* v_init_1224_, lean_object* v_f_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___redArg(v_map_1223_, v_init_1224_, v_f_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0___boxed(lean_object* v_00_u03c3_1227_, lean_object* v_00_u03b2_1228_, lean_object* v_map_1229_, lean_object* v_init_1230_, lean_object* v_f_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0(v_00_u03c3_1227_, v_00_u03b2_1228_, v_map_1229_, v_init_1230_, v_f_1231_);
lean_dec_ref(v_map_1229_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0___redArg(lean_object* v_map_1233_, lean_object* v_f_1234_, lean_object* v_init_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1234_, v_map_1233_, v_init_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0(lean_object* v_00_u03c3_1237_, lean_object* v_00_u03c3_1238_, lean_object* v_00_u03b2_1239_, lean_object* v_map_1240_, lean_object* v_f_1241_, lean_object* v_init_1242_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1241_, v_map_1240_, v_init_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_1244_, lean_object* v_00_u03c3_1245_, lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_f_1248_, lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1___redArg(v_f_1248_, v_x_1249_, v_x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1252_, lean_object* v_00_u03b2_1253_, lean_object* v_00_u03c3_1254_, lean_object* v_00_u03c3_1255_, lean_object* v_f_1256_, lean_object* v_as_1257_, size_t v_i_1258_, size_t v_stop_1259_, lean_object* v_b_1260_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___redArg(v_f_1256_, v_as_1257_, v_i_1258_, v_stop_1259_, v_b_1260_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1262_, lean_object* v_00_u03b2_1263_, lean_object* v_00_u03c3_1264_, lean_object* v_00_u03c3_1265_, lean_object* v_f_1266_, lean_object* v_as_1267_, lean_object* v_i_1268_, lean_object* v_stop_1269_, lean_object* v_b_1270_){
_start:
{
size_t v_i_boxed_1271_; size_t v_stop_boxed_1272_; lean_object* v_res_1273_; 
v_i_boxed_1271_ = lean_unbox_usize(v_i_1268_);
lean_dec(v_i_1268_);
v_stop_boxed_1272_ = lean_unbox_usize(v_stop_1269_);
lean_dec(v_stop_1269_);
v_res_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1262_, v_00_u03b2_1263_, v_00_u03c3_1264_, v_00_u03c3_1265_, v_f_1266_, v_as_1267_, v_i_boxed_1271_, v_stop_boxed_1272_, v_b_1270_);
lean_dec_ref(v_as_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_1274_, lean_object* v_00_u03c3_1275_, lean_object* v_00_u03b1_1276_, lean_object* v_00_u03b2_1277_, lean_object* v_f_1278_, lean_object* v_keys_1279_, lean_object* v_vals_1280_, lean_object* v_heq_1281_, lean_object* v_i_1282_, lean_object* v_acc_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___redArg(v_f_1278_, v_keys_1279_, v_vals_1280_, v_i_1282_, v_acc_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1285_, lean_object* v_00_u03c3_1286_, lean_object* v_00_u03b1_1287_, lean_object* v_00_u03b2_1288_, lean_object* v_f_1289_, lean_object* v_keys_1290_, lean_object* v_vals_1291_, lean_object* v_heq_1292_, lean_object* v_i_1293_, lean_object* v_acc_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_1285_, v_00_u03c3_1286_, v_00_u03b1_1287_, v_00_u03b2_1288_, v_f_1289_, v_keys_1290_, v_vals_1291_, v_heq_1292_, v_i_1293_, v_acc_1294_);
lean_dec_ref(v_vals_1291_);
lean_dec_ref(v_keys_1290_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(lean_object* v_as_1296_, size_t v_i_1297_, size_t v_stop_1298_, lean_object* v_b_1299_){
_start:
{
lean_object* v___y_1301_; uint8_t v___x_1305_; 
v___x_1305_ = lean_usize_dec_eq(v_i_1297_, v_stop_1298_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v_fst_1307_; 
v___x_1306_ = lean_array_uget(v_as_1296_, v_i_1297_);
v_fst_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_fst_1307_);
if (lean_obj_tag(v_fst_1307_) == 0)
{
lean_object* v_snd_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1317_; 
v_snd_1308_ = lean_ctor_get(v___x_1306_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1306_, 0);
lean_dec(v_unused_1318_);
v___x_1310_ = v___x_1306_;
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_snd_1308_);
lean_dec(v___x_1306_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1317_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v_declName_1312_; lean_object* v___x_1314_; 
v_declName_1312_ = lean_ctor_get(v_fst_1307_, 0);
lean_inc(v_declName_1312_);
lean_dec_ref(v_fst_1307_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v_declName_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_declName_1312_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_snd_1308_);
v___x_1314_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_array_push(v_b_1299_, v___x_1314_);
v___y_1301_ = v___x_1315_;
goto v___jp_1300_;
}
}
}
else
{
lean_dec(v_fst_1307_);
lean_dec(v___x_1306_);
v___y_1301_ = v_b_1299_;
goto v___jp_1300_;
}
}
else
{
return v_b_1299_;
}
v___jp_1300_:
{
size_t v___x_1302_; size_t v___x_1303_; 
v___x_1302_ = ((size_t)1ULL);
v___x_1303_ = lean_usize_add(v_i_1297_, v___x_1302_);
v_i_1297_ = v___x_1303_;
v_b_1299_ = v___y_1301_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6___boxed(lean_object* v_as_1319_, lean_object* v_i_1320_, lean_object* v_stop_1321_, lean_object* v_b_1322_){
_start:
{
size_t v_i_boxed_1323_; size_t v_stop_boxed_1324_; lean_object* v_res_1325_; 
v_i_boxed_1323_ = lean_unbox_usize(v_i_1320_);
lean_dec(v_i_1320_);
v_stop_boxed_1324_ = lean_unbox_usize(v_stop_1321_);
lean_dec(v_stop_1321_);
v_res_1325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1319_, v_i_boxed_1323_, v_stop_boxed_1324_, v_b_1322_);
lean_dec_ref(v_as_1319_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(lean_object* v_as_1328_, lean_object* v_start_1329_, lean_object* v_stop_1330_){
_start:
{
lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1331_ = ((lean_object*)(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___closed__0));
v___x_1332_ = lean_nat_dec_lt(v_start_1329_, v_stop_1330_);
if (v___x_1332_ == 0)
{
return v___x_1331_;
}
else
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
v___x_1333_ = lean_array_get_size(v_as_1328_);
v___x_1334_ = lean_nat_dec_le(v_stop_1330_, v___x_1333_);
if (v___x_1334_ == 0)
{
uint8_t v___x_1335_; 
v___x_1335_ = lean_nat_dec_lt(v_start_1329_, v___x_1333_);
if (v___x_1335_ == 0)
{
return v___x_1331_;
}
else
{
size_t v___x_1336_; size_t v___x_1337_; lean_object* v___x_1338_; 
v___x_1336_ = lean_usize_of_nat(v_start_1329_);
v___x_1337_ = lean_usize_of_nat(v___x_1333_);
v___x_1338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1328_, v___x_1336_, v___x_1337_, v___x_1331_);
return v___x_1338_;
}
}
else
{
size_t v___x_1339_; size_t v___x_1340_; lean_object* v___x_1341_; 
v___x_1339_ = lean_usize_of_nat(v_start_1329_);
v___x_1340_ = lean_usize_of_nat(v_stop_1330_);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3_spec__6(v_as_1328_, v___x_1339_, v___x_1340_, v___x_1331_);
return v___x_1341_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3___boxed(lean_object* v_as_1342_, lean_object* v_start_1343_, lean_object* v_stop_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(v_as_1342_, v_start_1343_, v_stop_1344_);
lean_dec(v_stop_1344_);
lean_dec(v_start_1343_);
lean_dec_ref(v_as_1342_);
return v_res_1345_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(lean_object* v_x_1346_, lean_object* v_x_1347_){
_start:
{
lean_object* v_fst_1348_; lean_object* v_snd_1349_; lean_object* v_fst_1350_; lean_object* v_snd_1351_; uint8_t v___x_1352_; 
v_fst_1348_ = lean_ctor_get(v_x_1346_, 0);
v_snd_1349_ = lean_ctor_get(v_x_1346_, 1);
v_fst_1350_ = lean_ctor_get(v_x_1347_, 0);
v_snd_1351_ = lean_ctor_get(v_x_1347_, 1);
v___x_1352_ = lean_nat_dec_eq(v_snd_1349_, v_snd_1351_);
if (v___x_1352_ == 0)
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_nat_dec_lt(v_snd_1351_, v_snd_1349_);
return v___x_1353_;
}
else
{
uint8_t v___x_1354_; 
v___x_1354_ = l_Lean_Name_lt(v_fst_1348_, v_fst_1350_);
return v___x_1354_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0___boxed(lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
uint8_t v_res_1357_; lean_object* v_r_1358_; 
v_res_1357_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v_x_1355_, v_x_1356_);
lean_dec_ref(v_x_1356_);
lean_dec_ref(v_x_1355_);
v_r_1358_ = lean_box(v_res_1357_);
return v_r_1358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(lean_object* v_hi_1359_, lean_object* v_pivot_1360_, lean_object* v_as_1361_, lean_object* v_i_1362_, lean_object* v_k_1363_){
_start:
{
uint8_t v___y_1365_; uint8_t v___x_1374_; 
v___x_1374_ = lean_nat_dec_lt(v_k_1363_, v_hi_1359_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_dec(v_k_1363_);
v___x_1375_ = lean_array_fswap(v_as_1361_, v_i_1362_, v_hi_1359_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_i_1362_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; lean_object* v_fst_1378_; lean_object* v_snd_1379_; lean_object* v_fst_1380_; lean_object* v_snd_1381_; uint8_t v___x_1382_; 
v___x_1377_ = lean_array_fget_borrowed(v_as_1361_, v_k_1363_);
v_fst_1378_ = lean_ctor_get(v___x_1377_, 0);
v_snd_1379_ = lean_ctor_get(v___x_1377_, 1);
v_fst_1380_ = lean_ctor_get(v_pivot_1360_, 0);
v_snd_1381_ = lean_ctor_get(v_pivot_1360_, 1);
v___x_1382_ = lean_nat_dec_eq(v_snd_1379_, v_snd_1381_);
if (v___x_1382_ == 0)
{
uint8_t v___x_1383_; 
v___x_1383_ = lean_nat_dec_lt(v_snd_1381_, v_snd_1379_);
v___y_1365_ = v___x_1383_;
goto v___jp_1364_;
}
else
{
uint8_t v___x_1384_; 
v___x_1384_ = l_Lean_Name_lt(v_fst_1378_, v_fst_1380_);
v___y_1365_ = v___x_1384_;
goto v___jp_1364_;
}
}
v___jp_1364_:
{
if (v___y_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = lean_unsigned_to_nat(1u);
v___x_1367_ = lean_nat_add(v_k_1363_, v___x_1366_);
lean_dec(v_k_1363_);
v_k_1363_ = v___x_1367_;
goto _start;
}
else
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
v___x_1369_ = lean_array_fswap(v_as_1361_, v_i_1362_, v_k_1363_);
v___x_1370_ = lean_unsigned_to_nat(1u);
v___x_1371_ = lean_nat_add(v_i_1362_, v___x_1370_);
lean_dec(v_i_1362_);
v___x_1372_ = lean_nat_add(v_k_1363_, v___x_1370_);
lean_dec(v_k_1363_);
v_as_1361_ = v___x_1369_;
v_i_1362_ = v___x_1371_;
v_k_1363_ = v___x_1372_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg___boxed(lean_object* v_hi_1385_, lean_object* v_pivot_1386_, lean_object* v_as_1387_, lean_object* v_i_1388_, lean_object* v_k_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_1385_, v_pivot_1386_, v_as_1387_, v_i_1388_, v_k_1389_);
lean_dec_ref(v_pivot_1386_);
lean_dec(v_hi_1385_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(lean_object* v_n_1391_, lean_object* v_as_1392_, lean_object* v_lo_1393_, lean_object* v_hi_1394_){
_start:
{
lean_object* v___y_1396_; uint8_t v___x_1406_; 
v___x_1406_ = lean_nat_dec_lt(v_lo_1393_, v_hi_1394_);
if (v___x_1406_ == 0)
{
lean_dec(v_lo_1393_);
return v_as_1392_;
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_mid_1409_; lean_object* v___y_1411_; lean_object* v___y_1417_; lean_object* v___x_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v___x_1407_ = lean_nat_add(v_lo_1393_, v_hi_1394_);
v___x_1408_ = lean_unsigned_to_nat(1u);
v_mid_1409_ = lean_nat_shiftr(v___x_1407_, v___x_1408_);
lean_dec(v___x_1407_);
v___x_1422_ = lean_array_fget_borrowed(v_as_1392_, v_mid_1409_);
v___x_1423_ = lean_array_fget_borrowed(v_as_1392_, v_lo_1393_);
v___x_1424_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1422_, v___x_1423_);
if (v___x_1424_ == 0)
{
v___y_1417_ = v_as_1392_;
goto v___jp_1416_;
}
else
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_array_fswap(v_as_1392_, v_lo_1393_, v_mid_1409_);
v___y_1417_ = v___x_1425_;
goto v___jp_1416_;
}
v___jp_1410_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; uint8_t v___x_1414_; 
v___x_1412_ = lean_array_fget_borrowed(v___y_1411_, v_mid_1409_);
v___x_1413_ = lean_array_fget_borrowed(v___y_1411_, v_hi_1394_);
v___x_1414_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1412_, v___x_1413_);
if (v___x_1414_ == 0)
{
lean_dec(v_mid_1409_);
v___y_1396_ = v___y_1411_;
goto v___jp_1395_;
}
else
{
lean_object* v___x_1415_; 
v___x_1415_ = lean_array_fswap(v___y_1411_, v_mid_1409_, v_hi_1394_);
lean_dec(v_mid_1409_);
v___y_1396_ = v___x_1415_;
goto v___jp_1395_;
}
}
v___jp_1416_:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v___x_1418_ = lean_array_fget_borrowed(v___y_1417_, v_hi_1394_);
v___x_1419_ = lean_array_fget_borrowed(v___y_1417_, v_lo_1393_);
v___x_1420_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___lam__0(v___x_1418_, v___x_1419_);
if (v___x_1420_ == 0)
{
v___y_1411_ = v___y_1417_;
goto v___jp_1410_;
}
else
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_array_fswap(v___y_1417_, v_lo_1393_, v_hi_1394_);
v___y_1411_ = v___x_1421_;
goto v___jp_1410_;
}
}
}
v___jp_1395_:
{
lean_object* v_pivot_1397_; lean_object* v___x_1398_; lean_object* v_fst_1399_; lean_object* v_snd_1400_; uint8_t v___x_1401_; 
v_pivot_1397_ = lean_array_fget(v___y_1396_, v_hi_1394_);
lean_inc_n(v_lo_1393_, 2);
v___x_1398_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_1394_, v_pivot_1397_, v___y_1396_, v_lo_1393_, v_lo_1393_);
lean_dec(v_pivot_1397_);
v_fst_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_fst_1399_);
v_snd_1400_ = lean_ctor_get(v___x_1398_, 1);
lean_inc(v_snd_1400_);
lean_dec_ref(v___x_1398_);
v___x_1401_ = lean_nat_dec_le(v_hi_1394_, v_fst_1399_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_1391_, v_snd_1400_, v_lo_1393_, v_fst_1399_);
v___x_1403_ = lean_unsigned_to_nat(1u);
v___x_1404_ = lean_nat_add(v_fst_1399_, v___x_1403_);
lean_dec(v_fst_1399_);
v_as_1392_ = v___x_1402_;
v_lo_1393_ = v___x_1404_;
goto _start;
}
else
{
lean_dec(v_fst_1399_);
lean_dec(v_lo_1393_);
return v_snd_1400_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg___boxed(lean_object* v_n_1426_, lean_object* v_as_1427_, lean_object* v_lo_1428_, lean_object* v_hi_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_1426_, v_as_1427_, v_lo_1428_, v_hi_1429_);
lean_dec(v_hi_1429_);
lean_dec(v_n_1426_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___lam__0(lean_object* v_ps_1431_, lean_object* v_k_1432_, lean_object* v_v_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_k_1432_);
lean_ctor_set(v___x_1434_, 1, v_v_1433_);
v___x_1435_ = lean_array_push(v_ps_1431_, v___x_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0(lean_object* v_f_1436_, lean_object* v_x1_1437_, lean_object* v_x2_1438_, lean_object* v_x3_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_apply_3(v_f_1436_, v_x1_1437_, v_x2_1438_, v_x3_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(lean_object* v_f_1441_, lean_object* v_keys_1442_, lean_object* v_vals_1443_, lean_object* v_i_1444_, lean_object* v_acc_1445_){
_start:
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = lean_array_get_size(v_keys_1442_);
v___x_1447_ = lean_nat_dec_lt(v_i_1444_, v___x_1446_);
if (v___x_1447_ == 0)
{
lean_dec(v_i_1444_);
lean_dec(v_f_1441_);
return v_acc_1445_;
}
else
{
lean_object* v_k_1448_; lean_object* v_v_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; 
v_k_1448_ = lean_array_fget_borrowed(v_keys_1442_, v_i_1444_);
v_v_1449_ = lean_array_fget_borrowed(v_vals_1443_, v_i_1444_);
lean_inc(v_f_1441_);
lean_inc(v_v_1449_);
lean_inc(v_k_1448_);
v___x_1450_ = lean_apply_3(v_f_1441_, v_acc_1445_, v_k_1448_, v_v_1449_);
v___x_1451_ = lean_unsigned_to_nat(1u);
v___x_1452_ = lean_nat_add(v_i_1444_, v___x_1451_);
lean_dec(v_i_1444_);
v_i_1444_ = v___x_1452_;
v_acc_1445_ = v___x_1450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_f_1454_, lean_object* v_keys_1455_, lean_object* v_vals_1456_, lean_object* v_i_1457_, lean_object* v_acc_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_1454_, v_keys_1455_, v_vals_1456_, v_i_1457_, v_acc_1458_);
lean_dec_ref(v_vals_1456_);
lean_dec_ref(v_keys_1455_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_f_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
if (lean_obj_tag(v_x_1461_) == 0)
{
lean_object* v_es_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v_es_1463_ = lean_ctor_get(v_x_1461_, 0);
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = lean_array_get_size(v_es_1463_);
v___x_1466_ = lean_nat_dec_lt(v___x_1464_, v___x_1465_);
if (v___x_1466_ == 0)
{
lean_dec(v_f_1460_);
return v_x_1462_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = lean_nat_dec_le(v___x_1465_, v___x_1465_);
if (v___x_1467_ == 0)
{
if (v___x_1466_ == 0)
{
lean_dec(v_f_1460_);
return v_x_1462_;
}
else
{
size_t v___x_1468_; size_t v___x_1469_; lean_object* v___x_1470_; 
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = lean_usize_of_nat(v___x_1465_);
v___x_1470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_1460_, v_es_1463_, v___x_1468_, v___x_1469_, v_x_1462_);
return v___x_1470_;
}
}
else
{
size_t v___x_1471_; size_t v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = ((size_t)0ULL);
v___x_1472_ = lean_usize_of_nat(v___x_1465_);
v___x_1473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_1460_, v_es_1463_, v___x_1471_, v___x_1472_, v_x_1462_);
return v___x_1473_;
}
}
}
else
{
lean_object* v_ks_1474_; lean_object* v_vs_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; 
v_ks_1474_ = lean_ctor_get(v_x_1461_, 0);
v_vs_1475_ = lean_ctor_get(v_x_1461_, 1);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_1460_, v_ks_1474_, v_vs_1475_, v___x_1476_, v_x_1462_);
return v___x_1477_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(lean_object* v_f_1478_, lean_object* v_as_1479_, size_t v_i_1480_, size_t v_stop_1481_, lean_object* v_b_1482_){
_start:
{
lean_object* v___y_1484_; uint8_t v___x_1488_; 
v___x_1488_ = lean_usize_dec_eq(v_i_1480_, v_stop_1481_);
if (v___x_1488_ == 0)
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_array_uget_borrowed(v_as_1479_, v_i_1480_);
switch(lean_obj_tag(v___x_1489_))
{
case 0:
{
lean_object* v_key_1490_; lean_object* v_val_1491_; lean_object* v___x_1492_; 
v_key_1490_ = lean_ctor_get(v___x_1489_, 0);
v_val_1491_ = lean_ctor_get(v___x_1489_, 1);
lean_inc(v_f_1478_);
lean_inc(v_val_1491_);
lean_inc(v_key_1490_);
v___x_1492_ = lean_apply_3(v_f_1478_, v_b_1482_, v_key_1490_, v_val_1491_);
v___y_1484_ = v___x_1492_;
goto v___jp_1483_;
}
case 1:
{
lean_object* v_node_1493_; lean_object* v___x_1494_; 
v_node_1493_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_f_1478_);
v___x_1494_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_1478_, v_node_1493_, v_b_1482_);
v___y_1484_ = v___x_1494_;
goto v___jp_1483_;
}
default: 
{
v___y_1484_ = v_b_1482_;
goto v___jp_1483_;
}
}
}
else
{
lean_dec(v_f_1478_);
return v_b_1482_;
}
v___jp_1483_:
{
size_t v___x_1485_; size_t v___x_1486_; 
v___x_1485_ = ((size_t)1ULL);
v___x_1486_ = lean_usize_add(v_i_1480_, v___x_1485_);
v_i_1480_ = v___x_1486_;
v_b_1482_ = v___y_1484_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg___boxed(lean_object* v_f_1495_, lean_object* v_as_1496_, lean_object* v_i_1497_, lean_object* v_stop_1498_, lean_object* v_b_1499_){
_start:
{
size_t v_i_boxed_1500_; size_t v_stop_boxed_1501_; lean_object* v_res_1502_; 
v_i_boxed_1500_ = lean_unbox_usize(v_i_1497_);
lean_dec(v_i_1497_);
v_stop_boxed_1501_ = lean_unbox_usize(v_stop_1498_);
lean_dec(v_stop_1498_);
v_res_1502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_1495_, v_as_1496_, v_i_boxed_1500_, v_stop_boxed_1501_, v_b_1499_);
lean_dec_ref(v_as_1496_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_f_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_1503_, v_x_1504_, v_x_1505_);
lean_dec_ref(v_x_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(lean_object* v_map_1507_, lean_object* v_f_1508_, lean_object* v_init_1509_){
_start:
{
lean_object* v___f_1510_; lean_object* v___x_1511_; 
v___f_1510_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1510_, 0, v_f_1508_);
v___x_1511_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v___f_1510_, v_map_1507_, v_init_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg___boxed(lean_object* v_map_1512_, lean_object* v_f_1513_, lean_object* v_init_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_map_1512_, v_f_1513_, v_init_1514_);
lean_dec_ref(v_map_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(lean_object* v_m_1519_){
_start:
{
lean_object* v___f_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___f_1520_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__0));
v___x_1521_ = ((lean_object*)(l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___closed__1));
v___x_1522_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_m_1519_, v___f_1520_, v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg___boxed(lean_object* v_m_1523_){
_start:
{
lean_object* v_res_1524_; 
v_res_1524_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_m_1523_);
lean_dec_ref(v_m_1523_);
return v_res_1524_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__0));
v___x_1527_ = l_Lean_stringToMessageData(v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1529_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__2));
v___x_1530_ = l_Lean_stringToMessageData(v___x_1529_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__4));
v___x_1533_ = l_Lean_stringToMessageData(v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1535_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__6));
v___x_1536_ = l_Lean_stringToMessageData(v___x_1535_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__8));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__10));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__12));
v___x_1545_ = l_Lean_stringToMessageData(v___x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(lean_object* v_msg_1546_, lean_object* v_declHint_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; lean_object* v_env_1551_; uint8_t v___x_1552_; 
v___x_1550_ = lean_st_ref_get(v___y_1548_);
v_env_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc_ref(v_env_1551_);
lean_dec(v___x_1550_);
v___x_1552_ = l_Lean_Name_isAnonymous(v_declHint_1547_);
if (v___x_1552_ == 0)
{
uint8_t v_isExporting_1553_; 
v_isExporting_1553_ = lean_ctor_get_uint8(v_env_1551_, sizeof(void*)*8);
if (v_isExporting_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec_ref(v_env_1551_);
lean_dec(v_declHint_1547_);
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v_msg_1546_);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; uint8_t v___x_1556_; 
lean_inc_ref(v_env_1551_);
v___x_1555_ = l_Lean_Environment_setExporting(v_env_1551_, v___x_1552_);
lean_inc(v_declHint_1547_);
lean_inc_ref(v___x_1555_);
v___x_1556_ = l_Lean_Environment_contains(v___x_1555_, v_declHint_1547_, v_isExporting_1553_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; 
lean_dec_ref(v___x_1555_);
lean_dec_ref(v_env_1551_);
lean_dec(v_declHint_1547_);
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v_msg_1546_);
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v_c_1563_; lean_object* v___x_1564_; 
v___x_1558_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__2);
v___x_1559_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem_spec__0_spec__0___closed__5);
v___x_1560_ = l_Lean_Options_empty;
v___x_1561_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1555_);
lean_ctor_set(v___x_1561_, 1, v___x_1558_);
lean_ctor_set(v___x_1561_, 2, v___x_1559_);
lean_ctor_set(v___x_1561_, 3, v___x_1560_);
lean_inc(v_declHint_1547_);
v___x_1562_ = l_Lean_MessageData_ofConstName(v_declHint_1547_, v___x_1552_);
v_c_1563_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1563_, 0, v___x_1561_);
lean_ctor_set(v_c_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1551_, v_declHint_1547_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
lean_dec_ref(v_env_1551_);
lean_dec(v_declHint_1547_);
v___x_1565_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v_c_1563_);
v___x_1567_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__3);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
v___x_1569_ = l_Lean_MessageData_note(v___x_1568_);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_msg_1546_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
return v___x_1571_;
}
else
{
lean_object* v_val_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1607_; 
v_val_1572_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1574_ = v___x_1564_;
v_isShared_1575_ = v_isSharedCheck_1607_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_val_1572_);
lean_dec(v___x_1564_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1607_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v_mod_1579_; uint8_t v___x_1580_; 
v___x_1576_ = lean_box(0);
v___x_1577_ = l_Lean_Environment_header(v_env_1551_);
lean_dec_ref(v_env_1551_);
v___x_1578_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1577_);
v_mod_1579_ = lean_array_get(v___x_1576_, v___x_1578_, v_val_1572_);
lean_dec(v_val_1572_);
lean_dec_ref(v___x_1578_);
v___x_1580_ = l_Lean_isPrivateName(v_declHint_1547_);
lean_dec(v_declHint_1547_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1581_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__5);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
lean_ctor_set(v___x_1582_, 1, v_c_1563_);
v___x_1583_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__7);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = l_Lean_MessageData_ofName(v_mod_1579_);
v___x_1586_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1584_);
lean_ctor_set(v___x_1586_, 1, v___x_1585_);
v___x_1587_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__9);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = l_Lean_MessageData_note(v___x_1588_);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_msg_1546_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1590_);
v___x_1592_ = v___x_1574_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v___x_1594_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__1);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
lean_ctor_set(v___x_1595_, 1, v_c_1563_);
v___x_1596_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__11);
v___x_1597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1595_);
lean_ctor_set(v___x_1597_, 1, v___x_1596_);
v___x_1598_ = l_Lean_MessageData_ofName(v_mod_1579_);
v___x_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___closed__13);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1599_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = l_Lean_MessageData_note(v___x_1601_);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v_msg_1546_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1603_);
v___x_1605_ = v___x_1574_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
return v___x_1605_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1608_; 
lean_dec_ref(v_env_1551_);
lean_dec(v_declHint_1547_);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_msg_1546_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg___boxed(lean_object* v_msg_1609_, lean_object* v_declHint_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_1609_, v_declHint_1610_, v___y_1611_);
lean_dec(v___y_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(lean_object* v_msg_1614_, lean_object* v_declHint_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1631_; 
v___x_1621_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_1614_, v_declHint_1615_, v___y_1619_);
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1624_ = v___x_1621_;
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1621_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1626_ = l_Lean_unknownIdentifierMessageTag;
v___x_1627_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1626_);
lean_ctor_set(v___x_1627_, 1, v_a_1622_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 0, v___x_1627_);
v___x_1629_ = v___x_1624_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16___boxed(lean_object* v_msg_1632_, lean_object* v_declHint_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(v_msg_1632_, v_declHint_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec_ref(v___y_1634_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(lean_object* v_msg_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_ref_1646_; lean_object* v___x_1647_; lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1656_; 
v_ref_1646_ = lean_ctor_get(v___y_1643_, 5);
v___x_1647_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v_msg_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_);
v_a_1648_ = lean_ctor_get(v___x_1647_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1647_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1650_ = v___x_1647_;
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1647_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1656_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
lean_inc(v_ref_1646_);
v___x_1652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1652_, 0, v_ref_1646_);
lean_ctor_set(v___x_1652_, 1, v_a_1648_);
if (v_isShared_1651_ == 0)
{
lean_ctor_set_tag(v___x_1650_, 1);
lean_ctor_set(v___x_1650_, 0, v___x_1652_);
v___x_1654_ = v___x_1650_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg___boxed(lean_object* v_msg_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(lean_object* v_ref_1664_, lean_object* v_msg_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v_fileName_1671_; lean_object* v_fileMap_1672_; lean_object* v_options_1673_; lean_object* v_currRecDepth_1674_; lean_object* v_maxRecDepth_1675_; lean_object* v_ref_1676_; lean_object* v_currNamespace_1677_; lean_object* v_openDecls_1678_; lean_object* v_initHeartbeats_1679_; lean_object* v_maxHeartbeats_1680_; lean_object* v_quotContext_1681_; lean_object* v_currMacroScope_1682_; uint8_t v_diag_1683_; lean_object* v_cancelTk_x3f_1684_; uint8_t v_suppressElabErrors_1685_; lean_object* v_inheritedTraceOptions_1686_; lean_object* v_ref_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_fileName_1671_ = lean_ctor_get(v___y_1668_, 0);
v_fileMap_1672_ = lean_ctor_get(v___y_1668_, 1);
v_options_1673_ = lean_ctor_get(v___y_1668_, 2);
v_currRecDepth_1674_ = lean_ctor_get(v___y_1668_, 3);
v_maxRecDepth_1675_ = lean_ctor_get(v___y_1668_, 4);
v_ref_1676_ = lean_ctor_get(v___y_1668_, 5);
v_currNamespace_1677_ = lean_ctor_get(v___y_1668_, 6);
v_openDecls_1678_ = lean_ctor_get(v___y_1668_, 7);
v_initHeartbeats_1679_ = lean_ctor_get(v___y_1668_, 8);
v_maxHeartbeats_1680_ = lean_ctor_get(v___y_1668_, 9);
v_quotContext_1681_ = lean_ctor_get(v___y_1668_, 10);
v_currMacroScope_1682_ = lean_ctor_get(v___y_1668_, 11);
v_diag_1683_ = lean_ctor_get_uint8(v___y_1668_, sizeof(void*)*14);
v_cancelTk_x3f_1684_ = lean_ctor_get(v___y_1668_, 12);
v_suppressElabErrors_1685_ = lean_ctor_get_uint8(v___y_1668_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1686_ = lean_ctor_get(v___y_1668_, 13);
v_ref_1687_ = l_Lean_replaceRef(v_ref_1664_, v_ref_1676_);
lean_inc_ref(v_inheritedTraceOptions_1686_);
lean_inc(v_cancelTk_x3f_1684_);
lean_inc(v_currMacroScope_1682_);
lean_inc(v_quotContext_1681_);
lean_inc(v_maxHeartbeats_1680_);
lean_inc(v_initHeartbeats_1679_);
lean_inc(v_openDecls_1678_);
lean_inc(v_currNamespace_1677_);
lean_inc(v_maxRecDepth_1675_);
lean_inc(v_currRecDepth_1674_);
lean_inc_ref(v_options_1673_);
lean_inc_ref(v_fileMap_1672_);
lean_inc_ref(v_fileName_1671_);
v___x_1688_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1688_, 0, v_fileName_1671_);
lean_ctor_set(v___x_1688_, 1, v_fileMap_1672_);
lean_ctor_set(v___x_1688_, 2, v_options_1673_);
lean_ctor_set(v___x_1688_, 3, v_currRecDepth_1674_);
lean_ctor_set(v___x_1688_, 4, v_maxRecDepth_1675_);
lean_ctor_set(v___x_1688_, 5, v_ref_1687_);
lean_ctor_set(v___x_1688_, 6, v_currNamespace_1677_);
lean_ctor_set(v___x_1688_, 7, v_openDecls_1678_);
lean_ctor_set(v___x_1688_, 8, v_initHeartbeats_1679_);
lean_ctor_set(v___x_1688_, 9, v_maxHeartbeats_1680_);
lean_ctor_set(v___x_1688_, 10, v_quotContext_1681_);
lean_ctor_set(v___x_1688_, 11, v_currMacroScope_1682_);
lean_ctor_set(v___x_1688_, 12, v_cancelTk_x3f_1684_);
lean_ctor_set(v___x_1688_, 13, v_inheritedTraceOptions_1686_);
lean_ctor_set_uint8(v___x_1688_, sizeof(void*)*14, v_diag_1683_);
lean_ctor_set_uint8(v___x_1688_, sizeof(void*)*14 + 1, v_suppressElabErrors_1685_);
v___x_1689_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_1665_, v___y_1666_, v___y_1667_, v___x_1688_, v___y_1669_);
lean_dec_ref(v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg___boxed(lean_object* v_ref_1690_, lean_object* v_msg_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_1690_, v_msg_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v_ref_1690_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(lean_object* v_ref_1698_, lean_object* v_msg_1699_, lean_object* v_declHint_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; lean_object* v_a_1707_; lean_object* v___x_1708_; 
v___x_1706_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16(v_msg_1699_, v_declHint_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
lean_inc(v_a_1707_);
lean_dec_ref(v___x_1706_);
v___x_1708_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_1698_, v_a_1707_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg___boxed(lean_object* v_ref_1709_, lean_object* v_msg_1710_, lean_object* v_declHint_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_1709_, v_msg_1710_, v_declHint_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_);
lean_dec(v___y_1715_);
lean_dec_ref(v___y_1714_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v_ref_1709_);
return v_res_1717_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__0));
v___x_1720_ = l_Lean_stringToMessageData(v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(lean_object* v_ref_1721_, lean_object* v_constName_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
lean_object* v___x_1728_; uint8_t v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1728_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___closed__1);
v___x_1729_ = 0;
lean_inc(v_constName_1722_);
v___x_1730_ = l_Lean_MessageData_ofConstName(v_constName_1722_, v___x_1729_);
v___x_1731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1728_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
v___x_1732_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_checkEMatchTheorem___closed__1);
v___x_1733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1731_);
lean_ctor_set(v___x_1733_, 1, v___x_1732_);
v___x_1734_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_1721_, v___x_1733_, v_constName_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_ref_1735_, lean_object* v_constName_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_1735_, v_constName_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_ref_1735_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(lean_object* v_constName_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_ref_1749_; lean_object* v___x_1750_; 
v_ref_1749_ = lean_ctor_get(v___y_1746_, 5);
v___x_1750_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_1749_, v_constName_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_constName_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(lean_object* v_constName_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1764_; lean_object* v_env_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; 
v___x_1764_ = lean_st_ref_get(v___y_1762_);
v_env_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc_ref(v_env_1765_);
lean_dec(v___x_1764_);
v___x_1766_ = 0;
lean_inc(v_constName_1758_);
v___x_1767_ = l_Lean_Environment_findConstVal_x3f(v_env_1765_, v_constName_1758_, v___x_1766_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
return v___x_1768_;
}
else
{
lean_object* v_val_1769_; lean_object* v___x_1771_; uint8_t v_isShared_1772_; uint8_t v_isSharedCheck_1776_; 
lean_dec(v_constName_1758_);
v_val_1769_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1771_ = v___x_1767_;
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
else
{
lean_inc(v_val_1769_);
lean_dec(v___x_1767_);
v___x_1771_ = lean_box(0);
v_isShared_1772_ = v_isSharedCheck_1776_;
goto v_resetjp_1770_;
}
v_resetjp_1770_:
{
lean_object* v___x_1774_; 
if (v_isShared_1772_ == 0)
{
lean_ctor_set_tag(v___x_1771_, 0);
v___x_1774_ = v___x_1771_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_val_1769_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2___boxed(lean_object* v_constName_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(v_constName_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_);
lean_dec(v___y_1781_);
lean_dec_ref(v___y_1780_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
if (lean_obj_tag(v_a_1784_) == 0)
{
lean_object* v___x_1786_; 
v___x_1786_ = l_List_reverse___redArg(v_a_1785_);
return v___x_1786_;
}
else
{
lean_object* v_head_1787_; lean_object* v_tail_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1797_; 
v_head_1787_ = lean_ctor_get(v_a_1784_, 0);
v_tail_1788_ = lean_ctor_get(v_a_1784_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_a_1784_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1790_ = v_a_1784_;
v_isShared_1791_ = v_isSharedCheck_1797_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_tail_1788_);
lean_inc(v_head_1787_);
lean_dec(v_a_1784_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1797_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = l_Lean_mkLevelParam(v_head_1787_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v_a_1785_);
lean_ctor_set(v___x_1790_, 0, v___x_1792_);
v___x_1794_ = v___x_1790_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_a_1785_);
v___x_1794_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
v_a_1784_ = v_tail_1788_;
v_a_1785_ = v___x_1794_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(lean_object* v_constName_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
lean_object* v___x_1804_; 
lean_inc(v_constName_1798_);
v___x_1804_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2(v_constName_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1816_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1816_ == 0)
{
v___x_1807_ = v___x_1804_;
v_isShared_1808_ = v_isSharedCheck_1816_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_a_1805_);
lean_dec(v___x_1804_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1816_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v_levelParams_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v_levelParams_1809_ = lean_ctor_get(v_a_1805_, 1);
lean_inc(v_levelParams_1809_);
lean_dec(v_a_1805_);
v___x_1810_ = lean_box(0);
v___x_1811_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__3(v_levelParams_1809_, v___x_1810_);
v___x_1812_ = l_Lean_mkConst(v_constName_1798_, v___x_1811_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 0, v___x_1812_);
v___x_1814_ = v___x_1807_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1812_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
lean_dec(v_constName_1798_);
v_a_1817_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1804_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1804_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1___boxed(lean_object* v_constName_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(v_constName_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1831_;
}
}
static double _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1835_; double v___x_1836_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = lean_float_of_nat(v___x_1835_);
return v___x_1836_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5(void){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__4));
v___x_1840_ = l_Lean_stringToMessageData(v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(size_t v_sz_1843_, size_t v_i_1844_, lean_object* v_bs_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_usize_dec_lt(v_i_1844_, v_sz_1843_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v_bs_1845_);
return v___x_1852_;
}
else
{
lean_object* v_v_1853_; lean_object* v_fst_1854_; lean_object* v_snd_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1891_; 
v_v_1853_ = lean_array_uget(v_bs_1845_, v_i_1844_);
v_fst_1854_ = lean_ctor_get(v_v_1853_, 0);
v_snd_1855_ = lean_ctor_get(v_v_1853_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_v_1853_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1857_ = v_v_1853_;
v_isShared_1858_ = v_isSharedCheck_1891_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_snd_1855_);
lean_inc(v_fst_1854_);
lean_dec(v_v_1853_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1891_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; 
v___x_1859_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1(v_fst_1854_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_a_1860_; lean_object* v___x_1861_; lean_object* v_bs_x27_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; double v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1871_; 
v_a_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_a_1860_);
lean_dec_ref(v___x_1859_);
v___x_1861_ = lean_unsigned_to_nat(0u);
v_bs_x27_1862_ = lean_array_uset(v_bs_1845_, v_i_1844_, v___x_1861_);
v___x_1863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1));
v___x_1864_ = lean_box(0);
v___x_1865_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2);
v___x_1866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
v___x_1867_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1867_, 0, v___x_1863_);
lean_ctor_set(v___x_1867_, 1, v___x_1864_);
lean_ctor_set(v___x_1867_, 2, v___x_1866_);
lean_ctor_set_float(v___x_1867_, sizeof(void*)*3, v___x_1865_);
lean_ctor_set_float(v___x_1867_, sizeof(void*)*3 + 8, v___x_1865_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*3 + 16, v___x_1851_);
v___x_1868_ = l_Lean_MessageData_ofConst(v_a_1860_);
v___x_1869_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__5);
if (v_isShared_1858_ == 0)
{
lean_ctor_set_tag(v___x_1857_, 7);
lean_ctor_set(v___x_1857_, 1, v___x_1869_);
lean_ctor_set(v___x_1857_, 0, v___x_1868_);
v___x_1871_ = v___x_1857_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v___x_1869_);
v___x_1871_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; size_t v___x_1878_; size_t v___x_1879_; lean_object* v___x_1880_; 
v___x_1872_ = l_Nat_reprFast(v_snd_1855_);
v___x_1873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1872_);
v___x_1874_ = l_Lean_MessageData_ofFormat(v___x_1873_);
v___x_1875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1871_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
v___x_1876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__6));
v___x_1877_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1867_);
lean_ctor_set(v___x_1877_, 1, v___x_1875_);
lean_ctor_set(v___x_1877_, 2, v___x_1876_);
v___x_1878_ = ((size_t)1ULL);
v___x_1879_ = lean_usize_add(v_i_1844_, v___x_1878_);
v___x_1880_ = lean_array_uset(v_bs_x27_1862_, v_i_1844_, v___x_1877_);
v_i_1844_ = v___x_1879_;
v_bs_1845_ = v___x_1880_;
goto _start;
}
}
else
{
lean_object* v_a_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1890_; 
lean_del_object(v___x_1857_);
lean_dec(v_snd_1855_);
lean_dec_ref(v_bs_1845_);
v_a_1883_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1885_ = v___x_1859_;
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_a_1883_);
lean_dec(v___x_1859_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1890_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1886_ == 0)
{
v___x_1888_ = v___x_1885_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1883_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___boxed(lean_object* v_sz_1892_, lean_object* v_i_1893_, lean_object* v_bs_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
size_t v_sz_boxed_1900_; size_t v_i_boxed_1901_; lean_object* v_res_1902_; 
v_sz_boxed_1900_ = lean_unbox_usize(v_sz_1892_);
lean_dec(v_sz_1892_);
v_i_boxed_1901_ = lean_unbox_usize(v_i_1893_);
lean_dec(v_i_1893_);
v_res_1902_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(v_sz_boxed_1900_, v_i_boxed_1901_, v_bs_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
lean_dec(v___y_1896_);
lean_dec_ref(v___y_1895_);
return v_res_1902_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0(void){
_start:
{
lean_object* v___x_1903_; uint8_t v___x_1904_; double v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
v___x_1904_ = 1;
v___x_1905_ = lean_float_once(&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__2);
v___x_1906_ = lean_box(0);
v___x_1907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__1));
v___x_1908_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
lean_ctor_set(v___x_1908_, 1, v___x_1906_);
lean_ctor_set(v___x_1908_, 2, v___x_1903_);
lean_ctor_set_float(v___x_1908_, sizeof(void*)*3, v___x_1905_);
lean_ctor_set_float(v___x_1908_, sizeof(void*)*3 + 8, v___x_1905_);
lean_ctor_set_uint8(v___x_1908_, sizeof(void*)*3 + 16, v___x_1904_);
return v___x_1908_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__2));
v___x_1913_ = l_Lean_MessageData_ofFormat(v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(lean_object* v_thms_1914_, lean_object* v_a_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_, lean_object* v_a_1918_){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___y_1923_; lean_object* v___x_1946_; lean_object* v_data_1947_; lean_object* v___x_1948_; lean_object* v___y_1950_; lean_object* v___y_1951_; uint8_t v___x_1953_; 
v___x_1920_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_thms_1914_);
v___x_1921_ = lean_unsigned_to_nat(0u);
v___x_1946_ = lean_array_get_size(v___x_1920_);
v_data_1947_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__3(v___x_1920_, v___x_1921_, v___x_1946_);
lean_dec_ref(v___x_1920_);
v___x_1948_ = lean_array_get_size(v_data_1947_);
v___x_1953_ = lean_nat_dec_eq(v___x_1948_, v___x_1921_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___y_1957_; uint8_t v___x_1959_; 
v___x_1954_ = lean_unsigned_to_nat(1u);
v___x_1955_ = lean_nat_sub(v___x_1948_, v___x_1954_);
v___x_1959_ = lean_nat_dec_le(v___x_1921_, v___x_1955_);
if (v___x_1959_ == 0)
{
lean_inc(v___x_1955_);
v___y_1957_ = v___x_1955_;
goto v___jp_1956_;
}
else
{
v___y_1957_ = v___x_1921_;
goto v___jp_1956_;
}
v___jp_1956_:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_nat_dec_le(v___y_1957_, v___x_1955_);
if (v___x_1958_ == 0)
{
lean_dec(v___x_1955_);
lean_inc(v___y_1957_);
v___y_1950_ = v___y_1957_;
v___y_1951_ = v___y_1957_;
goto v___jp_1949_;
}
else
{
v___y_1950_ = v___y_1957_;
v___y_1951_ = v___x_1955_;
goto v___jp_1949_;
}
}
}
else
{
v___y_1923_ = v_data_1947_;
goto v___jp_1922_;
}
v___jp_1922_:
{
size_t v_sz_1924_; size_t v___x_1925_; lean_object* v___x_1926_; 
v_sz_1924_ = lean_array_size(v___y_1923_);
v___x_1925_ = ((size_t)0ULL);
v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2(v_sz_1924_, v___x_1925_, v___y_1923_, v_a_1915_, v_a_1916_, v_a_1917_, v_a_1918_);
if (lean_obj_tag(v___x_1926_) == 0)
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1937_; 
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1929_ = v___x_1926_;
v_isShared_1930_ = v_isSharedCheck_1937_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1937_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1931_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__0);
v___x_1932_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___closed__3);
v___x_1933_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
lean_ctor_set(v___x_1933_, 2, v_a_1927_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1933_);
v___x_1935_ = v___x_1929_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
v_a_1938_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1926_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1926_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
v___jp_1949_:
{
lean_object* v___x_1952_; 
v___x_1952_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v___x_1948_, v_data_1947_, v___y_1950_, v___y_1951_);
lean_dec(v___y_1951_);
v___y_1923_ = v___x_1952_;
goto v___jp_1922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData___boxed(lean_object* v_thms_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(v_thms_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec_ref(v_thms_1960_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(lean_object* v_00_u03b2_1967_, lean_object* v_m_1968_){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___redArg(v_m_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0___boxed(lean_object* v_00_u03b2_1970_, lean_object* v_m_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0(v_00_u03b2_1970_, v_m_1971_);
lean_dec_ref(v_m_1971_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(lean_object* v_n_1973_, lean_object* v_as_1974_, lean_object* v_lo_1975_, lean_object* v_hi_1976_, lean_object* v_w_1977_, lean_object* v_hlo_1978_, lean_object* v_hhi_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___redArg(v_n_1973_, v_as_1974_, v_lo_1975_, v_hi_1976_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4___boxed(lean_object* v_n_1981_, lean_object* v_as_1982_, lean_object* v_lo_1983_, lean_object* v_hi_1984_, lean_object* v_w_1985_, lean_object* v_hlo_1986_, lean_object* v_hhi_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4(v_n_1981_, v_as_1982_, v_lo_1983_, v_hi_1984_, v_w_1985_, v_hlo_1986_, v_hhi_1987_);
lean_dec(v_hi_1984_);
lean_dec(v_n_1981_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(lean_object* v_00_u03c3_1989_, lean_object* v_00_u03b2_1990_, lean_object* v_map_1991_, lean_object* v_f_1992_, lean_object* v_init_1993_){
_start:
{
lean_object* v___x_1994_; 
v___x_1994_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___redArg(v_map_1991_, v_f_1992_, v_init_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0___boxed(lean_object* v_00_u03c3_1995_, lean_object* v_00_u03b2_1996_, lean_object* v_map_1997_, lean_object* v_f_1998_, lean_object* v_init_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0(v_00_u03c3_1995_, v_00_u03b2_1996_, v_map_1997_, v_f_1998_, v_init_1999_);
lean_dec_ref(v_map_1997_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(lean_object* v_n_2001_, lean_object* v_lo_2002_, lean_object* v_hi_2003_, lean_object* v_hhi_2004_, lean_object* v_pivot_2005_, lean_object* v_as_2006_, lean_object* v_i_2007_, lean_object* v_k_2008_, lean_object* v_ilo_2009_, lean_object* v_ik_2010_, lean_object* v_w_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___redArg(v_hi_2003_, v_pivot_2005_, v_as_2006_, v_i_2007_, v_k_2008_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8___boxed(lean_object* v_n_2013_, lean_object* v_lo_2014_, lean_object* v_hi_2015_, lean_object* v_hhi_2016_, lean_object* v_pivot_2017_, lean_object* v_as_2018_, lean_object* v_i_2019_, lean_object* v_k_2020_, lean_object* v_ilo_2021_, lean_object* v_ik_2022_, lean_object* v_w_2023_){
_start:
{
lean_object* v_res_2024_; 
v_res_2024_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__4_spec__8(v_n_2013_, v_lo_2014_, v_hi_2015_, v_hhi_2016_, v_pivot_2017_, v_as_2018_, v_i_2019_, v_k_2020_, v_ilo_2021_, v_ik_2022_, v_w_2023_);
lean_dec_ref(v_pivot_2017_);
lean_dec(v_hi_2015_);
lean_dec(v_lo_2014_);
lean_dec(v_n_2013_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(lean_object* v_map_2025_, lean_object* v_f_2026_, lean_object* v_init_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2026_, v_map_2025_, v_init_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_map_2029_, lean_object* v_f_2030_, lean_object* v_init_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___redArg(v_map_2029_, v_f_2030_, v_init_2031_);
lean_dec_ref(v_map_2029_);
return v_res_2032_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_2033_, lean_object* v_00_u03b2_2034_, lean_object* v_map_2035_, lean_object* v_f_2036_, lean_object* v_init_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2036_, v_map_2035_, v_init_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_2039_, lean_object* v_00_u03b2_2040_, lean_object* v_map_2041_, lean_object* v_f_2042_, lean_object* v_init_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1(v_00_u03c3_2039_, v_00_u03b2_2040_, v_map_2041_, v_f_2042_, v_init_2043_);
lean_dec_ref(v_map_2041_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_2045_, lean_object* v_constName_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
return v___x_2052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2053_, lean_object* v_constName_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4(v_00_u03b1_2053_, v_constName_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec(v___y_2056_);
lean_dec_ref(v___y_2055_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03c3_2061_, lean_object* v_00_u03b1_2062_, lean_object* v_00_u03b2_2063_, lean_object* v_f_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___redArg(v_f_2064_, v_x_2065_, v_x_2066_);
return v___x_2067_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03c3_2068_, lean_object* v_00_u03b1_2069_, lean_object* v_00_u03b2_2070_, lean_object* v_f_2071_, lean_object* v_x_2072_, lean_object* v_x_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6(v_00_u03c3_2068_, v_00_u03b1_2069_, v_00_u03b2_2070_, v_f_2071_, v_x_2072_, v_x_2073_);
lean_dec_ref(v_x_2072_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(lean_object* v_00_u03b1_2075_, lean_object* v_ref_2076_, lean_object* v_constName_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___redArg(v_ref_2076_, v_constName_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b1_2084_, lean_object* v_ref_2085_, lean_object* v_constName_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9(v_00_u03b1_2084_, v_ref_2085_, v_constName_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
lean_dec(v___y_2088_);
lean_dec_ref(v___y_2087_);
lean_dec(v_ref_2085_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(lean_object* v_00_u03b1_2093_, lean_object* v_00_u03b2_2094_, lean_object* v_00_u03c3_2095_, lean_object* v_f_2096_, lean_object* v_as_2097_, size_t v_i_2098_, size_t v_stop_2099_, lean_object* v_b_2100_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___redArg(v_f_2096_, v_as_2097_, v_i_2098_, v_stop_2099_, v_b_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11___boxed(lean_object* v_00_u03b1_2102_, lean_object* v_00_u03b2_2103_, lean_object* v_00_u03c3_2104_, lean_object* v_f_2105_, lean_object* v_as_2106_, lean_object* v_i_2107_, lean_object* v_stop_2108_, lean_object* v_b_2109_){
_start:
{
size_t v_i_boxed_2110_; size_t v_stop_boxed_2111_; lean_object* v_res_2112_; 
v_i_boxed_2110_ = lean_unbox_usize(v_i_2107_);
lean_dec(v_i_2107_);
v_stop_boxed_2111_ = lean_unbox_usize(v_stop_2108_);
lean_dec(v_stop_2108_);
v_res_2112_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__11(v_00_u03b1_2102_, v_00_u03b2_2103_, v_00_u03c3_2104_, v_f_2105_, v_as_2106_, v_i_boxed_2110_, v_stop_boxed_2111_, v_b_2109_);
lean_dec_ref(v_as_2106_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(lean_object* v_00_u03c3_2113_, lean_object* v_00_u03b1_2114_, lean_object* v_00_u03b2_2115_, lean_object* v_f_2116_, lean_object* v_keys_2117_, lean_object* v_vals_2118_, lean_object* v_heq_2119_, lean_object* v_i_2120_, lean_object* v_acc_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___redArg(v_f_2116_, v_keys_2117_, v_vals_2118_, v_i_2120_, v_acc_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03c3_2123_, lean_object* v_00_u03b1_2124_, lean_object* v_00_u03b2_2125_, lean_object* v_f_2126_, lean_object* v_keys_2127_, lean_object* v_vals_2128_, lean_object* v_heq_2129_, lean_object* v_i_2130_, lean_object* v_acc_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_PersistentHashMap_toArray___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__0_spec__0_spec__1_spec__6_spec__12(v_00_u03c3_2123_, v_00_u03b1_2124_, v_00_u03b2_2125_, v_f_2126_, v_keys_2127_, v_vals_2128_, v_heq_2129_, v_i_2130_, v_acc_2131_);
lean_dec_ref(v_vals_2128_);
lean_dec_ref(v_keys_2127_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(lean_object* v_00_u03b1_2133_, lean_object* v_ref_2134_, lean_object* v_msg_2135_, lean_object* v_declHint_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___redArg(v_ref_2134_, v_msg_2135_, v_declHint_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15___boxed(lean_object* v_00_u03b1_2143_, lean_object* v_ref_2144_, lean_object* v_msg_2145_, lean_object* v_declHint_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15(v_00_u03b1_2143_, v_ref_2144_, v_msg_2145_, v_declHint_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v_ref_2144_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(lean_object* v_msg_2153_, lean_object* v_declHint_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___redArg(v_msg_2153_, v_declHint_2154_, v___y_2158_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17___boxed(lean_object* v_msg_2161_, lean_object* v_declHint_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__16_spec__17(v_msg_2161_, v_declHint_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(lean_object* v_00_u03b1_2169_, lean_object* v_ref_2170_, lean_object* v_msg_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
lean_object* v___x_2177_; 
v___x_2177_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___redArg(v_ref_2170_, v_msg_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17___boxed(lean_object* v_00_u03b1_2178_, lean_object* v_ref_2179_, lean_object* v_msg_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17(v_00_u03b1_2178_, v_ref_2179_, v_msg_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v_ref_2179_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(lean_object* v_00_u03b1_2187_, lean_object* v_msg_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___redArg(v_msg_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19___boxed(lean_object* v_00_u03b1_2195_, lean_object* v_msg_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4_spec__9_spec__15_spec__17_spec__19(v_00_u03b1_2195_, v_msg_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(lean_object* v_k_2203_, lean_object* v_b_2204_, lean_object* v_c_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
lean_inc(v___y_2209_);
lean_inc_ref(v___y_2208_);
lean_inc(v___y_2207_);
lean_inc_ref(v___y_2206_);
v___x_2211_ = lean_apply_7(v_k_2203_, v_b_2204_, v_c_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, lean_box(0));
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed(lean_object* v_k_2212_, lean_object* v_b_2213_, lean_object* v_c_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0(v_k_2212_, v_b_2213_, v_c_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(lean_object* v_type_2221_, lean_object* v_k_2222_, uint8_t v_cleanupAnnotations_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
lean_object* v___f_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___f_2229_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_2229_, 0, v_k_2222_);
v___x_2230_ = 0;
v___x_2231_ = lean_box(0);
v___x_2232_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_2230_, v___x_2231_, v_type_2221_, v___f_2229_, v_cleanupAnnotations_2223_, v___x_2230_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
else
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2248_; 
v_a_2241_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2243_ = v___x_2232_;
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2232_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2248_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
lean_object* v___x_2246_; 
if (v_isShared_2244_ == 0)
{
v___x_2246_ = v___x_2243_;
goto v_reusejp_2245_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_a_2241_);
v___x_2246_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2245_;
}
v_reusejp_2245_:
{
return v___x_2246_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg___boxed(lean_object* v_type_2249_, lean_object* v_k_2250_, lean_object* v_cleanupAnnotations_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2257_; lean_object* v_res_2258_; 
v_cleanupAnnotations_boxed_2257_ = lean_unbox(v_cleanupAnnotations_2251_);
v_res_2258_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v_type_2249_, v_k_2250_, v_cleanupAnnotations_boxed_2257_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(lean_object* v_00_u03b1_2259_, lean_object* v_type_2260_, lean_object* v_k_2261_, uint8_t v_cleanupAnnotations_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v_type_2260_, v_k_2261_, v_cleanupAnnotations_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___boxed(lean_object* v_00_u03b1_2269_, lean_object* v_type_2270_, lean_object* v_k_2271_, lean_object* v_cleanupAnnotations_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_2278_; lean_object* v_res_2279_; 
v_cleanupAnnotations_boxed_2278_ = lean_unbox(v_cleanupAnnotations_2272_);
v_res_2279_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2(v_00_u03b1_2269_, v_type_2270_, v_k_2271_, v_cleanupAnnotations_boxed_2278_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
return v_res_2279_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2283_ = lean_box(0);
v___x_2284_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__1));
v___x_2285_ = l_Lean_mkConst(v___x_2284_, v___x_2283_);
return v___x_2285_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__2);
v___x_2287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(lean_object* v_x_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
v___x_2294_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___closed__3);
v___x_2295_ = 0;
v___x_2296_ = lean_box(0);
v___x_2297_ = l_Lean_Meta_mkFreshExprMVar(v___x_2294_, v___x_2295_, v___x_2296_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2306_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2306_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
v___x_2302_ = l_Lean_Expr_mvarId_x21(v_a_2298_);
lean_dec(v_a_2298_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2302_);
v___x_2304_ = v___x_2300_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
v_a_2307_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2297_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2297_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0___boxed(lean_object* v_x_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__0(v_x_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec_ref(v_x_2315_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(lean_object* v_k_2322_, lean_object* v_b_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
lean_inc(v___y_2327_);
lean_inc_ref(v___y_2326_);
lean_inc(v___y_2325_);
lean_inc_ref(v___y_2324_);
v___x_2329_ = lean_apply_6(v_k_2322_, v_b_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, lean_box(0));
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_2330_, lean_object* v_b_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0(v_k_2330_, v_b_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(lean_object* v_name_2338_, uint8_t v_bi_2339_, lean_object* v_type_2340_, lean_object* v_k_2341_, uint8_t v_kind_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v___f_2348_; lean_object* v___x_2349_; 
v___f_2348_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2348_, 0, v_k_2341_);
v___x_2349_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_2338_, v_bi_2339_, v_type_2340_, v___f_2348_, v_kind_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2357_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2352_ = v___x_2349_;
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_a_2350_);
lean_dec(v___x_2349_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2357_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2355_; 
if (v_isShared_2353_ == 0)
{
v___x_2355_ = v___x_2352_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2350_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2349_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2349_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_name_2366_, lean_object* v_bi_2367_, lean_object* v_type_2368_, lean_object* v_k_2369_, lean_object* v_kind_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
uint8_t v_bi_boxed_2376_; uint8_t v_kind_boxed_2377_; lean_object* v_res_2378_; 
v_bi_boxed_2376_ = lean_unbox(v_bi_2367_);
v_kind_boxed_2377_ = lean_unbox(v_kind_2370_);
v_res_2378_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2366_, v_bi_boxed_2376_, v_type_2368_, v_k_2369_, v_kind_boxed_2377_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
return v_res_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(lean_object* v_name_2379_, lean_object* v_type_2380_, lean_object* v_k_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v___x_2387_; uint8_t v___x_2388_; lean_object* v___x_2389_; 
v___x_2387_ = 0;
v___x_2388_ = 0;
v___x_2389_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2379_, v___x_2387_, v_type_2380_, v_k_2381_, v___x_2388_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg___boxed(lean_object* v_name_2390_, lean_object* v_type_2391_, lean_object* v_k_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v_name_2390_, v_type_2391_, v_k_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(lean_object* v___f_2402_, lean_object* v_x_2403_, lean_object* v_type_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2410_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___closed__1));
v___x_2411_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v___x_2410_, v_type_2404_, v___f_2402_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1___boxed(lean_object* v___f_2412_, lean_object* v_x_2413_, lean_object* v_type_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___lam__1(v___f_2412_, v_x_2413_, v_type_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec_ref(v_x_2413_);
return v_res_2420_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(uint8_t v___y_2427_, uint8_t v_suppressElabErrors_2428_, lean_object* v_x_2429_){
_start:
{
if (lean_obj_tag(v_x_2429_) == 1)
{
lean_object* v_pre_2430_; 
v_pre_2430_ = lean_ctor_get(v_x_2429_, 0);
switch(lean_obj_tag(v_pre_2430_))
{
case 1:
{
lean_object* v_pre_2431_; 
v_pre_2431_ = lean_ctor_get(v_pre_2430_, 0);
switch(lean_obj_tag(v_pre_2431_))
{
case 0:
{
lean_object* v_str_2432_; lean_object* v_str_2433_; lean_object* v___x_2434_; uint8_t v___x_2435_; 
v_str_2432_ = lean_ctor_get(v_x_2429_, 1);
v_str_2433_ = lean_ctor_get(v_pre_2430_, 1);
v___x_2434_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__6_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_2435_ = lean_string_dec_eq(v_str_2433_, v___x_2434_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; uint8_t v___x_2437_; 
v___x_2436_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__8_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_2437_ = lean_string_dec_eq(v_str_2433_, v___x_2436_);
if (v___x_2437_ == 0)
{
return v___y_2427_;
}
else
{
lean_object* v___x_2438_; uint8_t v___x_2439_; 
v___x_2438_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__0));
v___x_2439_ = lean_string_dec_eq(v_str_2432_, v___x_2438_);
if (v___x_2439_ == 0)
{
return v___y_2427_;
}
else
{
return v_suppressElabErrors_2428_;
}
}
}
else
{
lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2440_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__1));
v___x_2441_ = lean_string_dec_eq(v_str_2432_, v___x_2440_);
if (v___x_2441_ == 0)
{
return v___y_2427_;
}
else
{
return v_suppressElabErrors_2428_;
}
}
}
case 1:
{
lean_object* v_pre_2442_; 
v_pre_2442_ = lean_ctor_get(v_pre_2431_, 0);
if (lean_obj_tag(v_pre_2442_) == 0)
{
lean_object* v_str_2443_; lean_object* v_str_2444_; lean_object* v_str_2445_; lean_object* v___x_2446_; uint8_t v___x_2447_; 
v_str_2443_ = lean_ctor_get(v_x_2429_, 1);
v_str_2444_ = lean_ctor_get(v_pre_2430_, 1);
v_str_2445_ = lean_ctor_get(v_pre_2431_, 1);
v___x_2446_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__2));
v___x_2447_ = lean_string_dec_eq(v_str_2445_, v___x_2446_);
if (v___x_2447_ == 0)
{
return v___y_2427_;
}
else
{
lean_object* v___x_2448_; uint8_t v___x_2449_; 
v___x_2448_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__3));
v___x_2449_ = lean_string_dec_eq(v_str_2444_, v___x_2448_);
if (v___x_2449_ == 0)
{
return v___y_2427_;
}
else
{
lean_object* v___x_2450_; uint8_t v___x_2451_; 
v___x_2450_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__4));
v___x_2451_ = lean_string_dec_eq(v_str_2443_, v___x_2450_);
if (v___x_2451_ == 0)
{
return v___y_2427_;
}
else
{
return v_suppressElabErrors_2428_;
}
}
}
}
else
{
return v___y_2427_;
}
}
default: 
{
return v___y_2427_;
}
}
}
case 0:
{
lean_object* v_str_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
v_str_2452_ = lean_ctor_get(v_x_2429_, 1);
v___x_2453_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___closed__5));
v___x_2454_ = lean_string_dec_eq(v_str_2452_, v___x_2453_);
if (v___x_2454_ == 0)
{
return v___y_2427_;
}
else
{
return v_suppressElabErrors_2428_;
}
}
default: 
{
return v___y_2427_;
}
}
}
else
{
return v___y_2427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed(lean_object* v___y_2455_, lean_object* v_suppressElabErrors_2456_, lean_object* v_x_2457_){
_start:
{
uint8_t v___y_5356__boxed_2458_; uint8_t v_suppressElabErrors_boxed_2459_; uint8_t v_res_2460_; lean_object* v_r_2461_; 
v___y_5356__boxed_2458_ = lean_unbox(v___y_2455_);
v_suppressElabErrors_boxed_2459_ = lean_unbox(v_suppressElabErrors_2456_);
v_res_2460_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0(v___y_5356__boxed_2458_, v_suppressElabErrors_boxed_2459_, v_x_2457_);
lean_dec(v_x_2457_);
v_r_2461_ = lean_box(v_res_2460_);
return v_r_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(lean_object* v_ref_2462_, lean_object* v_msgData_2463_, uint8_t v_severity_2464_, uint8_t v_isSilent_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
uint8_t v___y_2472_; lean_object* v___y_2473_; lean_object* v___y_2474_; lean_object* v___y_2475_; uint8_t v___y_2476_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___y_2508_; uint8_t v___y_2509_; lean_object* v___y_2510_; uint8_t v___y_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; uint8_t v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2533_; uint8_t v___y_2534_; uint8_t v___y_2535_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; uint8_t v___y_2539_; lean_object* v___y_2540_; lean_object* v___y_2544_; uint8_t v___y_2545_; lean_object* v___y_2546_; lean_object* v___y_2547_; lean_object* v___y_2548_; uint8_t v___y_2549_; uint8_t v___y_2550_; uint8_t v___x_2555_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v___y_2560_; uint8_t v___y_2561_; uint8_t v___y_2562_; uint8_t v___y_2563_; uint8_t v___y_2565_; uint8_t v___x_2580_; 
v___x_2555_ = 2;
v___x_2580_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2464_, v___x_2555_);
if (v___x_2580_ == 0)
{
v___y_2565_ = v___x_2580_;
goto v___jp_2564_;
}
else
{
uint8_t v___x_2581_; 
lean_inc_ref(v_msgData_2463_);
v___x_2581_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2463_);
v___y_2565_ = v___x_2581_;
goto v___jp_2564_;
}
v___jp_2471_:
{
lean_object* v___x_2481_; lean_object* v_currNamespace_2482_; lean_object* v_openDecls_2483_; lean_object* v_env_2484_; lean_object* v_nextMacroScope_2485_; lean_object* v_ngen_2486_; lean_object* v_auxDeclNGen_2487_; lean_object* v_traceState_2488_; lean_object* v_cache_2489_; lean_object* v_messages_2490_; lean_object* v_infoState_2491_; lean_object* v_snapshotTasks_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2506_; 
v___x_2481_ = lean_st_ref_take(v___y_2480_);
v_currNamespace_2482_ = lean_ctor_get(v___y_2479_, 6);
v_openDecls_2483_ = lean_ctor_get(v___y_2479_, 7);
v_env_2484_ = lean_ctor_get(v___x_2481_, 0);
v_nextMacroScope_2485_ = lean_ctor_get(v___x_2481_, 1);
v_ngen_2486_ = lean_ctor_get(v___x_2481_, 2);
v_auxDeclNGen_2487_ = lean_ctor_get(v___x_2481_, 3);
v_traceState_2488_ = lean_ctor_get(v___x_2481_, 4);
v_cache_2489_ = lean_ctor_get(v___x_2481_, 5);
v_messages_2490_ = lean_ctor_get(v___x_2481_, 6);
v_infoState_2491_ = lean_ctor_get(v___x_2481_, 7);
v_snapshotTasks_2492_ = lean_ctor_get(v___x_2481_, 8);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2494_ = v___x_2481_;
v_isShared_2495_ = v_isSharedCheck_2506_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_snapshotTasks_2492_);
lean_inc(v_infoState_2491_);
lean_inc(v_messages_2490_);
lean_inc(v_cache_2489_);
lean_inc(v_traceState_2488_);
lean_inc(v_auxDeclNGen_2487_);
lean_inc(v_ngen_2486_);
lean_inc(v_nextMacroScope_2485_);
lean_inc(v_env_2484_);
lean_dec(v___x_2481_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2506_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2501_; 
lean_inc(v_openDecls_2483_);
lean_inc(v_currNamespace_2482_);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v_currNamespace_2482_);
lean_ctor_set(v___x_2496_, 1, v_openDecls_2483_);
v___x_2497_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v___y_2478_);
lean_inc_ref(v___y_2475_);
lean_inc_ref(v___y_2477_);
v___x_2498_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_2498_, 0, v___y_2477_);
lean_ctor_set(v___x_2498_, 1, v___y_2474_);
lean_ctor_set(v___x_2498_, 2, v___y_2473_);
lean_ctor_set(v___x_2498_, 3, v___y_2475_);
lean_ctor_set(v___x_2498_, 4, v___x_2497_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*5, v___y_2476_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*5 + 1, v___y_2472_);
lean_ctor_set_uint8(v___x_2498_, sizeof(void*)*5 + 2, v_isSilent_2465_);
v___x_2499_ = l_Lean_MessageLog_add(v___x_2498_, v_messages_2490_);
if (v_isShared_2495_ == 0)
{
lean_ctor_set(v___x_2494_, 6, v___x_2499_);
v___x_2501_ = v___x_2494_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_env_2484_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v_nextMacroScope_2485_);
lean_ctor_set(v_reuseFailAlloc_2505_, 2, v_ngen_2486_);
lean_ctor_set(v_reuseFailAlloc_2505_, 3, v_auxDeclNGen_2487_);
lean_ctor_set(v_reuseFailAlloc_2505_, 4, v_traceState_2488_);
lean_ctor_set(v_reuseFailAlloc_2505_, 5, v_cache_2489_);
lean_ctor_set(v_reuseFailAlloc_2505_, 6, v___x_2499_);
lean_ctor_set(v_reuseFailAlloc_2505_, 7, v_infoState_2491_);
lean_ctor_set(v_reuseFailAlloc_2505_, 8, v_snapshotTasks_2492_);
v___x_2501_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2502_ = lean_st_ref_set(v___y_2480_, v___x_2501_);
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
}
v___jp_2507_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2531_; 
v___x_2516_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_2463_);
v___x_2517_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v___x_2516_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
v_a_2518_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2520_ = v___x_2517_;
v_isShared_2521_ = v_isSharedCheck_2531_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2517_);
v___x_2520_ = lean_box(0);
v_isShared_2521_ = v_isSharedCheck_2531_;
goto v_resetjp_2519_;
}
v_resetjp_2519_:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_inc_ref_n(v___y_2513_, 2);
v___x_2522_ = l_Lean_FileMap_toPosition(v___y_2513_, v___y_2510_);
lean_dec(v___y_2510_);
v___x_2523_ = l_Lean_FileMap_toPosition(v___y_2513_, v___y_2515_);
lean_dec(v___y_2515_);
v___x_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
v___x_2525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
if (v___y_2514_ == 0)
{
lean_del_object(v___x_2520_);
lean_dec_ref(v___y_2508_);
v___y_2472_ = v___y_2509_;
v___y_2473_ = v___x_2524_;
v___y_2474_ = v___x_2522_;
v___y_2475_ = v___x_2525_;
v___y_2476_ = v___y_2511_;
v___y_2477_ = v___y_2512_;
v___y_2478_ = v_a_2518_;
v___y_2479_ = v___y_2468_;
v___y_2480_ = v___y_2469_;
goto v___jp_2471_;
}
else
{
uint8_t v___x_2526_; 
lean_inc(v_a_2518_);
v___x_2526_ = l_Lean_MessageData_hasTag(v___y_2508_, v_a_2518_);
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2529_; 
lean_dec_ref(v___x_2524_);
lean_dec_ref(v___x_2522_);
lean_dec(v_a_2518_);
v___x_2527_ = lean_box(0);
if (v_isShared_2521_ == 0)
{
lean_ctor_set(v___x_2520_, 0, v___x_2527_);
v___x_2529_ = v___x_2520_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v___x_2527_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
else
{
lean_del_object(v___x_2520_);
v___y_2472_ = v___y_2509_;
v___y_2473_ = v___x_2524_;
v___y_2474_ = v___x_2522_;
v___y_2475_ = v___x_2525_;
v___y_2476_ = v___y_2511_;
v___y_2477_ = v___y_2512_;
v___y_2478_ = v_a_2518_;
v___y_2479_ = v___y_2468_;
v___y_2480_ = v___y_2469_;
goto v___jp_2471_;
}
}
}
}
v___jp_2532_:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_Syntax_getTailPos_x3f(v___y_2537_, v___y_2535_);
lean_dec(v___y_2537_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_inc(v___y_2540_);
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2534_;
v___y_2510_ = v___y_2540_;
v___y_2511_ = v___y_2535_;
v___y_2512_ = v___y_2536_;
v___y_2513_ = v___y_2538_;
v___y_2514_ = v___y_2539_;
v___y_2515_ = v___y_2540_;
goto v___jp_2507_;
}
else
{
lean_object* v_val_2542_; 
v_val_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_val_2542_);
lean_dec_ref(v___x_2541_);
v___y_2508_ = v___y_2533_;
v___y_2509_ = v___y_2534_;
v___y_2510_ = v___y_2540_;
v___y_2511_ = v___y_2535_;
v___y_2512_ = v___y_2536_;
v___y_2513_ = v___y_2538_;
v___y_2514_ = v___y_2539_;
v___y_2515_ = v_val_2542_;
goto v___jp_2507_;
}
}
v___jp_2543_:
{
lean_object* v_ref_2551_; lean_object* v___x_2552_; 
v_ref_2551_ = l_Lean_replaceRef(v_ref_2462_, v___y_2546_);
v___x_2552_ = l_Lean_Syntax_getPos_x3f(v_ref_2551_, v___y_2545_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_unsigned_to_nat(0u);
v___y_2533_ = v___y_2544_;
v___y_2534_ = v___y_2550_;
v___y_2535_ = v___y_2545_;
v___y_2536_ = v___y_2547_;
v___y_2537_ = v_ref_2551_;
v___y_2538_ = v___y_2548_;
v___y_2539_ = v___y_2549_;
v___y_2540_ = v___x_2553_;
goto v___jp_2532_;
}
else
{
lean_object* v_val_2554_; 
v_val_2554_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_val_2554_);
lean_dec_ref(v___x_2552_);
v___y_2533_ = v___y_2544_;
v___y_2534_ = v___y_2550_;
v___y_2535_ = v___y_2545_;
v___y_2536_ = v___y_2547_;
v___y_2537_ = v_ref_2551_;
v___y_2538_ = v___y_2548_;
v___y_2539_ = v___y_2549_;
v___y_2540_ = v_val_2554_;
goto v___jp_2532_;
}
}
v___jp_2556_:
{
if (v___y_2563_ == 0)
{
v___y_2544_ = v___y_2557_;
v___y_2545_ = v___y_2562_;
v___y_2546_ = v___y_2558_;
v___y_2547_ = v___y_2559_;
v___y_2548_ = v___y_2560_;
v___y_2549_ = v___y_2561_;
v___y_2550_ = v_severity_2464_;
goto v___jp_2543_;
}
else
{
v___y_2544_ = v___y_2557_;
v___y_2545_ = v___y_2562_;
v___y_2546_ = v___y_2558_;
v___y_2547_ = v___y_2559_;
v___y_2548_ = v___y_2560_;
v___y_2549_ = v___y_2561_;
v___y_2550_ = v___x_2555_;
goto v___jp_2543_;
}
}
v___jp_2564_:
{
if (v___y_2565_ == 0)
{
lean_object* v_fileName_2566_; lean_object* v_fileMap_2567_; lean_object* v_options_2568_; lean_object* v_ref_2569_; uint8_t v_suppressElabErrors_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___f_2573_; uint8_t v___x_2574_; uint8_t v___x_2575_; 
v_fileName_2566_ = lean_ctor_get(v___y_2468_, 0);
v_fileMap_2567_ = lean_ctor_get(v___y_2468_, 1);
v_options_2568_ = lean_ctor_get(v___y_2468_, 2);
v_ref_2569_ = lean_ctor_get(v___y_2468_, 5);
v_suppressElabErrors_2570_ = lean_ctor_get_uint8(v___y_2468_, sizeof(void*)*14 + 1);
v___x_2571_ = lean_box(v___y_2565_);
v___x_2572_ = lean_box(v_suppressElabErrors_2570_);
v___f_2573_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2573_, 0, v___x_2571_);
lean_closure_set(v___f_2573_, 1, v___x_2572_);
v___x_2574_ = 1;
v___x_2575_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2464_, v___x_2574_);
if (v___x_2575_ == 0)
{
v___y_2557_ = v___f_2573_;
v___y_2558_ = v_ref_2569_;
v___y_2559_ = v_fileName_2566_;
v___y_2560_ = v_fileMap_2567_;
v___y_2561_ = v_suppressElabErrors_2570_;
v___y_2562_ = v___y_2565_;
v___y_2563_ = v___x_2575_;
goto v___jp_2556_;
}
else
{
lean_object* v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = l_Lean_warningAsError;
v___x_2577_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v_options_2568_, v___x_2576_);
v___y_2557_ = v___f_2573_;
v___y_2558_ = v_ref_2569_;
v___y_2559_ = v_fileName_2566_;
v___y_2560_ = v_fileMap_2567_;
v___y_2561_ = v_suppressElabErrors_2570_;
v___y_2562_ = v___y_2565_;
v___y_2563_ = v___x_2577_;
goto v___jp_2556_;
}
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; 
lean_dec_ref(v_msgData_2463_);
v___x_2578_ = lean_box(0);
v___x_2579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
return v___x_2579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___boxed(lean_object* v_ref_2582_, lean_object* v_msgData_2583_, lean_object* v_severity_2584_, lean_object* v_isSilent_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
uint8_t v_severity_boxed_2591_; uint8_t v_isSilent_boxed_2592_; lean_object* v_res_2593_; 
v_severity_boxed_2591_ = lean_unbox(v_severity_2584_);
v_isSilent_boxed_2592_ = lean_unbox(v_isSilent_2585_);
v_res_2593_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(v_ref_2582_, v_msgData_2583_, v_severity_boxed_2591_, v_isSilent_boxed_2592_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v_ref_2582_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(lean_object* v_msgData_2594_, uint8_t v_severity_2595_, uint8_t v_isSilent_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v_ref_2602_; lean_object* v___x_2603_; 
v_ref_2602_ = lean_ctor_get(v___y_2599_, 5);
v___x_2603_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5(v_ref_2602_, v_msgData_2594_, v_severity_2595_, v_isSilent_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4___boxed(lean_object* v_msgData_2604_, lean_object* v_severity_2605_, lean_object* v_isSilent_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
uint8_t v_severity_boxed_2612_; uint8_t v_isSilent_boxed_2613_; lean_object* v_res_2614_; 
v_severity_boxed_2612_ = lean_unbox(v_severity_2605_);
v_isSilent_boxed_2613_ = lean_unbox(v_isSilent_2606_);
v_res_2614_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(v_msgData_2604_, v_severity_boxed_2612_, v_isSilent_boxed_2613_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(lean_object* v_msgData_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
uint8_t v___x_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = 0;
v___x_2622_ = 0;
v___x_2623_ = l_Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4(v_msgData_2615_, v___x_2621_, v___x_2622_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3___boxed(lean_object* v_msgData_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v_msgData_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(lean_object* v_constName_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v___x_2637_; lean_object* v_env_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; 
v___x_2637_ = lean_st_ref_get(v___y_2635_);
v_env_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc_ref(v_env_2638_);
lean_dec(v___x_2637_);
v___x_2639_ = 0;
lean_inc(v_constName_2631_);
v___x_2640_ = l_Lean_Environment_find_x3f(v_env_2638_, v_constName_2631_, v___x_2639_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__1_spec__2_spec__4___redArg(v_constName_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
return v___x_2641_;
}
else
{
lean_object* v_val_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2649_; 
lean_dec(v_constName_2631_);
v_val_2642_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2649_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2644_ = v___x_2640_;
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_val_2642_);
lean_dec(v___x_2640_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2649_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2647_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set_tag(v___x_2644_, 0);
v___x_2647_ = v___x_2644_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_val_2642_);
v___x_2647_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1___boxed(lean_object* v_constName_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(v_constName_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2656_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v___x_2662_ = l_Lean_stringToMessageData(v___x_2661_);
return v___x_2662_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__4));
v___x_2665_ = l_Lean_stringToMessageData(v___x_2664_);
return v___x_2665_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__6));
v___x_2668_ = l_Lean_stringToMessageData(v___x_2667_);
return v___x_2668_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__8));
v___x_2671_ = l_Lean_stringToMessageData(v___x_2670_);
return v___x_2671_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11(void){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__10));
v___x_2674_ = l_Lean_stringToMessageData(v___x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(lean_object* v_declName_2675_, lean_object* v_params_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v___x_2682_; 
lean_inc(v_declName_2675_);
v___x_2682_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__1(v_declName_2675_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___f_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; lean_object* v___x_2687_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref(v___x_2682_);
v___f_2684_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__1));
v___x_2685_ = l_Lean_ConstantInfo_type(v_a_2683_);
lean_dec(v_a_2683_);
v___x_2686_ = 0;
v___x_2687_ = l_Lean_Meta_forallTelescope___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__2___redArg(v___x_2685_, v___f_2684_, v___x_2686_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v_a_2688_; lean_object* v___x_2689_; 
v_a_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc(v_a_2688_);
lean_dec_ref(v___x_2687_);
lean_inc_ref(v_params_2676_);
v___x_2689_ = l_Lean_Meta_Grind_main(v_a_2688_, v_params_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2778_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2692_ = v___x_2689_;
v_isShared_2693_ = v_isSharedCheck_2778_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2778_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v_counters_2694_; lean_object* v_config_2695_; lean_object* v_thm_2696_; lean_object* v_instances_2697_; lean_object* v_min_2698_; lean_object* v_detailed_2699_; lean_object* v___x_2700_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; uint8_t v___x_2736_; 
v_counters_2694_ = lean_ctor_get(v_a_2690_, 3);
lean_inc_ref(v_counters_2694_);
lean_dec(v_a_2690_);
v_config_2695_ = lean_ctor_get(v_params_2676_, 0);
lean_inc_ref(v_config_2695_);
lean_dec_ref(v_params_2676_);
v_thm_2696_ = lean_ctor_get(v_counters_2694_, 0);
lean_inc_ref(v_thm_2696_);
lean_dec_ref(v_counters_2694_);
v_instances_2697_ = lean_ctor_get(v_config_2695_, 3);
lean_inc(v_instances_2697_);
v_min_2698_ = lean_ctor_get(v_config_2695_, 9);
lean_inc(v_min_2698_);
v_detailed_2699_ = lean_ctor_get(v_config_2695_, 10);
lean_inc(v_detailed_2699_);
lean_dec_ref(v_config_2695_);
v___x_2700_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_sum(v_thm_2696_);
v___x_2736_ = lean_nat_dec_lt(v_min_2698_, v___x_2700_);
if (v___x_2736_ == 0)
{
lean_dec(v_instances_2697_);
v___y_2708_ = v_a_2677_;
v___y_2709_ = v_a_2678_;
v___y_2710_ = v_a_2679_;
v___y_2711_ = v_a_2680_;
goto v___jp_2707_;
}
else
{
uint8_t v___x_2737_; 
v___x_2737_ = lean_nat_dec_le(v_instances_2697_, v___x_2700_);
lean_dec(v_instances_2697_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2738_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5);
lean_inc(v_declName_2675_);
v___x_2739_ = l_Lean_MessageData_ofName(v_declName_2675_);
v___x_2740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__7);
v___x_2742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
lean_inc(v___x_2700_);
v___x_2743_ = l_Nat_reprFast(v___x_2700_);
v___x_2744_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
v___x_2745_ = l_Lean_MessageData_ofFormat(v___x_2744_);
v___x_2746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2742_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9);
v___x_2748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2748_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_dec_ref(v___x_2749_);
v___y_2708_ = v_a_2677_;
v___y_2709_ = v_a_2678_;
v___y_2710_ = v_a_2679_;
v___y_2711_ = v_a_2680_;
goto v___jp_2707_;
}
else
{
lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2757_; 
lean_dec(v___x_2700_);
lean_dec(v_detailed_2699_);
lean_dec(v_min_2698_);
lean_dec_ref(v_thm_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_declName_2675_);
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2752_ = v___x_2749_;
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_dec(v___x_2749_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2757_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2755_; 
if (v_isShared_2753_ == 0)
{
v___x_2755_ = v___x_2752_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_a_2750_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
else
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2758_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__5);
lean_inc(v_declName_2675_);
v___x_2759_ = l_Lean_MessageData_ofName(v_declName_2675_);
v___x_2760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2759_);
v___x_2761_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__11);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
lean_inc(v___x_2700_);
v___x_2763_ = l_Nat_reprFast(v___x_2700_);
v___x_2764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2763_);
v___x_2765_ = l_Lean_MessageData_ofFormat(v___x_2764_);
v___x_2766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2762_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__9);
v___x_2768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2766_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2768_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_dec_ref(v___x_2769_);
v___y_2708_ = v_a_2677_;
v___y_2709_ = v_a_2678_;
v___y_2710_ = v_a_2679_;
v___y_2711_ = v_a_2680_;
goto v___jp_2707_;
}
else
{
lean_object* v_a_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2777_; 
lean_dec(v___x_2700_);
lean_dec(v_detailed_2699_);
lean_dec(v_min_2698_);
lean_dec_ref(v_thm_2696_);
lean_del_object(v___x_2692_);
lean_dec(v_declName_2675_);
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2772_ = v___x_2769_;
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_a_2770_);
lean_dec(v___x_2769_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2777_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2775_; 
if (v_isShared_2773_ == 0)
{
v___x_2775_ = v___x_2772_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v_a_2770_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
}
v___jp_2701_:
{
uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; 
v___x_2702_ = lean_nat_dec_lt(v_min_2698_, v___x_2700_);
lean_dec(v___x_2700_);
lean_dec(v_min_2698_);
v___x_2703_ = lean_box(v___x_2702_);
if (v_isShared_2693_ == 0)
{
lean_ctor_set(v___x_2692_, 0, v___x_2703_);
v___x_2705_ = v___x_2692_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
v___jp_2707_:
{
uint8_t v___x_2712_; 
v___x_2712_ = lean_nat_dec_lt(v_detailed_2699_, v___x_2700_);
lean_dec(v_detailed_2699_);
if (v___x_2712_ == 0)
{
lean_dec_ref(v_thm_2696_);
lean_dec(v_declName_2675_);
goto v___jp_2701_;
}
else
{
lean_object* v___x_2713_; 
v___x_2713_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData(v_thm_2696_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
lean_dec_ref(v_thm_2696_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref(v___x_2713_);
v___x_2715_ = l_Lean_MessageData_ofName(v_declName_2675_);
v___x_2716_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__3);
v___x_2717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2715_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v___x_2718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v_a_2714_);
v___x_2719_ = l_Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3(v___x_2718_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_dec_ref(v___x_2719_);
goto v___jp_2701_;
}
else
{
lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2727_; 
lean_dec(v___x_2700_);
lean_dec(v_min_2698_);
lean_del_object(v___x_2692_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2722_ = v___x_2719_;
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2727_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2725_; 
if (v_isShared_2723_ == 0)
{
v___x_2725_ = v___x_2722_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_a_2720_);
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
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec(v___x_2700_);
lean_dec(v_min_2698_);
lean_del_object(v___x_2692_);
lean_dec(v_declName_2675_);
v_a_2728_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2713_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2713_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
lean_dec_ref(v_params_2676_);
lean_dec(v_declName_2675_);
v_a_2779_ = lean_ctor_get(v___x_2689_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2689_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2781_ = v___x_2689_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2689_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
v___x_2784_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
return v___x_2784_;
}
}
}
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec_ref(v_params_2676_);
lean_dec(v_declName_2675_);
v_a_2787_ = lean_ctor_get(v___x_2687_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___x_2687_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___x_2687_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___x_2687_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v_params_2676_);
lean_dec(v_declName_2675_);
v_a_2795_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2682_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2682_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___boxed(lean_object* v_declName_2803_, lean_object* v_params_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_declName_2803_, v_params_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
lean_dec(v_a_2808_);
lean_dec_ref(v_a_2807_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(lean_object* v_00_u03b1_2811_, lean_object* v_name_2812_, uint8_t v_bi_2813_, lean_object* v_type_2814_, lean_object* v_k_2815_, uint8_t v_kind_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___redArg(v_name_2812_, v_bi_2813_, v_type_2814_, v_k_2815_, v_kind_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2823_, lean_object* v_name_2824_, lean_object* v_bi_2825_, lean_object* v_type_2826_, lean_object* v_k_2827_, lean_object* v_kind_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_){
_start:
{
uint8_t v_bi_boxed_2834_; uint8_t v_kind_boxed_2835_; lean_object* v_res_2836_; 
v_bi_boxed_2834_ = lean_unbox(v_bi_2825_);
v_kind_boxed_2835_ = lean_unbox(v_kind_2828_);
v_res_2836_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0_spec__0(v_00_u03b1_2823_, v_name_2824_, v_bi_boxed_2834_, v_type_2826_, v_k_2827_, v_kind_boxed_2835_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(lean_object* v_00_u03b1_2837_, lean_object* v_name_2838_, lean_object* v_type_2839_, lean_object* v_k_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___redArg(v_name_2838_, v_type_2839_, v_k_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0___boxed(lean_object* v_00_u03b1_2847_, lean_object* v_name_2848_, lean_object* v_type_2849_, lean_object* v_k_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__0(v_00_u03b1_2847_, v_name_2848_, v_type_2849_, v_k_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg(){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
v___x_2858_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__3___redArg___closed__0);
v___x_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg___boxed(lean_object* v___y_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(lean_object* v_00_u03b1_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___boxed(lean_object* v_00_u03b1_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0(v_00_u03b1_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
lean_dec(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec(v___y_2875_);
lean_dec_ref(v___y_2874_);
lean_dec(v___y_2873_);
lean_dec_ref(v___y_2872_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(lean_object* v_a_2880_, lean_object* v_as_2881_, size_t v_sz_2882_, size_t v_i_2883_, uint8_t v_b_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
uint8_t v___x_2890_; 
v___x_2890_ = lean_usize_dec_lt(v_i_2883_, v_sz_2882_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_dec_ref(v_a_2880_);
v___x_2891_ = lean_box(v_b_2884_);
v___x_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2891_);
return v___x_2892_;
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v_a_2893_ = lean_array_uget_borrowed(v_as_2881_, v_i_2883_);
v___x_2894_ = lean_box(0);
lean_inc(v_a_2893_);
v___x_2895_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v_a_2893_, v___x_2894_, v___y_2887_, v___y_2888_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref(v___x_2895_);
lean_inc_ref(v_a_2880_);
v___x_2897_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_a_2896_, v_a_2880_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; uint8_t v_a_2900_; uint8_t v___x_2904_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___x_2897_);
v___x_2904_ = lean_unbox(v_a_2898_);
if (v___x_2904_ == 0)
{
lean_dec(v_a_2898_);
v_a_2900_ = v_b_2884_;
goto v___jp_2899_;
}
else
{
uint8_t v___x_2905_; 
v___x_2905_ = lean_unbox(v_a_2898_);
lean_dec(v_a_2898_);
v_a_2900_ = v___x_2905_;
goto v___jp_2899_;
}
v___jp_2899_:
{
size_t v___x_2901_; size_t v___x_2902_; 
v___x_2901_ = ((size_t)1ULL);
v___x_2902_ = lean_usize_add(v_i_2883_, v___x_2901_);
v_i_2883_ = v___x_2902_;
v_b_2884_ = v_a_2900_;
goto _start;
}
}
else
{
lean_dec_ref(v_a_2880_);
return v___x_2897_;
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec_ref(v_a_2880_);
v_a_2906_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2895_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2895_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg___boxed(lean_object* v_a_2914_, lean_object* v_as_2915_, lean_object* v_sz_2916_, lean_object* v_i_2917_, lean_object* v_b_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
size_t v_sz_boxed_2924_; size_t v_i_boxed_2925_; uint8_t v_b_boxed_2926_; lean_object* v_res_2927_; 
v_sz_boxed_2924_ = lean_unbox_usize(v_sz_2916_);
lean_dec(v_sz_2916_);
v_i_boxed_2925_ = lean_unbox_usize(v_i_2917_);
lean_dec(v_i_2917_);
v_b_boxed_2926_ = lean_unbox(v_b_2918_);
v_res_2927_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_2914_, v_as_2915_, v_sz_boxed_2924_, v_i_boxed_2925_, v_b_boxed_2926_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_);
lean_dec(v___y_2922_);
lean_dec_ref(v___y_2921_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec_ref(v_as_2915_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(size_t v_sz_2935_, size_t v_i_2936_, lean_object* v_bs_2937_){
_start:
{
uint8_t v___x_2938_; 
v___x_2938_ = lean_usize_dec_lt(v_i_2936_, v_sz_2935_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; 
v___x_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_bs_2937_);
return v___x_2939_;
}
else
{
lean_object* v_v_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v_v_2940_ = lean_array_uget(v_bs_2937_, v_i_2936_);
v___x_2941_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__2));
lean_inc(v_v_2940_);
v___x_2942_ = l_Lean_Syntax_isOfKind(v_v_2940_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec(v_v_2940_);
lean_dec_ref(v_bs_2937_);
v___x_2943_ = lean_box(0);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; lean_object* v_bs_x27_2945_; size_t v___x_2946_; size_t v___x_2947_; lean_object* v___x_2948_; 
v___x_2944_ = lean_unsigned_to_nat(0u);
v_bs_x27_2945_ = lean_array_uset(v_bs_2937_, v_i_2936_, v___x_2944_);
v___x_2946_ = ((size_t)1ULL);
v___x_2947_ = lean_usize_add(v_i_2936_, v___x_2946_);
v___x_2948_ = lean_array_uset(v_bs_x27_2945_, v_i_2936_, v_v_2940_);
v_i_2936_ = v___x_2947_;
v_bs_2937_ = v___x_2948_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___boxed(lean_object* v_sz_2950_, lean_object* v_i_2951_, lean_object* v_bs_2952_){
_start:
{
size_t v_sz_boxed_2953_; size_t v_i_boxed_2954_; lean_object* v_res_2955_; 
v_sz_boxed_2953_ = lean_unbox_usize(v_sz_2950_);
lean_dec(v_sz_2950_);
v_i_boxed_2954_ = lean_unbox_usize(v_i_2951_);
lean_dec(v_i_2951_);
v_res_2955_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_boxed_2953_, v_i_boxed_2954_, v_bs_2952_);
return v_res_2955_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__9));
v___x_2972_ = l_String_toRawSubstring_x27(v___x_2971_);
return v___x_2972_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13(void){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_Array_mkArray0(lean_box(0));
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(uint8_t v___x_2979_, lean_object* v_stx_2980_, lean_object* v___x_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_){
_start:
{
if (v___x_2979_ == 0)
{
lean_object* v___x_2989_; 
lean_dec_ref(v___x_2981_);
lean_dec(v_stx_2980_);
v___x_2989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_2989_;
}
else
{
lean_object* v_fileName_2990_; lean_object* v_fileMap_2991_; lean_object* v_options_2992_; lean_object* v_currRecDepth_2993_; lean_object* v_maxRecDepth_2994_; lean_object* v_ref_2995_; lean_object* v_currNamespace_2996_; lean_object* v_openDecls_2997_; lean_object* v_initHeartbeats_2998_; lean_object* v_quotContext_2999_; lean_object* v_currMacroScope_3000_; uint8_t v_diag_3001_; lean_object* v_cancelTk_x3f_3002_; uint8_t v_suppressElabErrors_3003_; lean_object* v_inheritedTraceOptions_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; size_t v_sz_3008_; size_t v___x_3009_; lean_object* v___x_3010_; 
v_fileName_2990_ = lean_ctor_get(v___y_2986_, 0);
v_fileMap_2991_ = lean_ctor_get(v___y_2986_, 1);
v_options_2992_ = lean_ctor_get(v___y_2986_, 2);
v_currRecDepth_2993_ = lean_ctor_get(v___y_2986_, 3);
v_maxRecDepth_2994_ = lean_ctor_get(v___y_2986_, 4);
v_ref_2995_ = lean_ctor_get(v___y_2986_, 5);
v_currNamespace_2996_ = lean_ctor_get(v___y_2986_, 6);
v_openDecls_2997_ = lean_ctor_get(v___y_2986_, 7);
v_initHeartbeats_2998_ = lean_ctor_get(v___y_2986_, 8);
v_quotContext_2999_ = lean_ctor_get(v___y_2986_, 10);
v_currMacroScope_3000_ = lean_ctor_get(v___y_2986_, 11);
v_diag_3001_ = lean_ctor_get_uint8(v___y_2986_, sizeof(void*)*14);
v_cancelTk_x3f_3002_ = lean_ctor_get(v___y_2986_, 12);
v_suppressElabErrors_3003_ = lean_ctor_get_uint8(v___y_2986_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3004_ = lean_ctor_get(v___y_2986_, 13);
v___x_3005_ = lean_unsigned_to_nat(2u);
v___x_3006_ = l_Lean_Syntax_getArg(v_stx_2980_, v___x_3005_);
v___x_3007_ = l_Lean_Syntax_getArgs(v___x_3006_);
lean_dec(v___x_3006_);
v_sz_3008_ = lean_array_size(v___x_3007_);
v___x_3009_ = ((size_t)0ULL);
v___x_3010_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_3008_, v___x_3009_, v___x_3007_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v___x_3011_; 
lean_dec_ref(v___x_2981_);
lean_dec(v_stx_2980_);
v___x_3011_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3011_;
}
else
{
lean_object* v_val_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; 
v_val_3012_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_val_3012_);
lean_dec_ref(v___x_3010_);
v___x_3013_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inheritedTraceOptions_3004_);
lean_inc(v_cancelTk_x3f_3002_);
lean_inc(v_currMacroScope_3000_);
lean_inc(v_quotContext_2999_);
lean_inc(v_initHeartbeats_2998_);
lean_inc(v_openDecls_2997_);
lean_inc(v_currNamespace_2996_);
lean_inc(v_ref_2995_);
lean_inc(v_maxRecDepth_2994_);
lean_inc(v_currRecDepth_2993_);
lean_inc_ref(v_options_2992_);
lean_inc_ref(v_fileMap_2991_);
lean_inc_ref(v_fileName_2990_);
v___x_3014_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3014_, 0, v_fileName_2990_);
lean_ctor_set(v___x_3014_, 1, v_fileMap_2991_);
lean_ctor_set(v___x_3014_, 2, v_options_2992_);
lean_ctor_set(v___x_3014_, 3, v_currRecDepth_2993_);
lean_ctor_set(v___x_3014_, 4, v_maxRecDepth_2994_);
lean_ctor_set(v___x_3014_, 5, v_ref_2995_);
lean_ctor_set(v___x_3014_, 6, v_currNamespace_2996_);
lean_ctor_set(v___x_3014_, 7, v_openDecls_2997_);
lean_ctor_set(v___x_3014_, 8, v_initHeartbeats_2998_);
lean_ctor_set(v___x_3014_, 9, v___x_3013_);
lean_ctor_set(v___x_3014_, 10, v_quotContext_2999_);
lean_ctor_set(v___x_3014_, 11, v_currMacroScope_3000_);
lean_ctor_set(v___x_3014_, 12, v_cancelTk_x3f_3002_);
lean_ctor_set(v___x_3014_, 13, v_inheritedTraceOptions_3004_);
lean_ctor_set_uint8(v___x_3014_, sizeof(void*)*14, v_diag_3001_);
lean_ctor_set_uint8(v___x_3014_, sizeof(void*)*14 + 1, v_suppressElabErrors_3003_);
v___x_3015_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(v_val_3012_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___x_3014_, v___y_2987_);
lean_dec(v_val_3012_);
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_object* v_a_3016_; lean_object* v___x_3017_; 
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref(v___x_3015_);
v___x_3017_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_a_3016_, v___y_2984_, v___y_2985_, v___x_3014_, v___y_2987_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v_ids_3021_; uint8_t v___x_3022_; size_t v_sz_3023_; lean_object* v___x_3024_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = lean_unsigned_to_nat(3u);
v___x_3020_ = l_Lean_Syntax_getArg(v_stx_2980_, v___x_3019_);
v_ids_3021_ = l_Lean_Syntax_getArgs(v___x_3020_);
lean_dec(v___x_3020_);
v___x_3022_ = 0;
v_sz_3023_ = lean_array_size(v_ids_3021_);
v___x_3024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_3018_, v_ids_3021_, v_sz_3023_, v___x_3009_, v___x_3022_, v___y_2984_, v___y_2985_, v___x_3014_, v___y_2987_);
lean_dec_ref(v_ids_3021_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3071_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3027_ = v___x_3024_;
v_isShared_3028_ = v_isSharedCheck_3071_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_3024_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3071_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
uint8_t v___x_3029_; 
v___x_3029_ = lean_unbox(v_a_3025_);
lean_dec(v_a_3025_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3032_; 
lean_dec_ref(v___x_3014_);
lean_dec_ref(v___x_2981_);
lean_dec(v_stx_2980_);
v___x_3030_ = lean_box(0);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3030_);
v___x_3032_ = v___x_3027_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v___x_3030_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
else
{
lean_object* v_map_3034_; lean_object* v___x_3035_; uint8_t v___y_3037_; lean_object* v___x_3064_; 
v_map_3034_ = lean_ctor_get(v_options_2992_, 0);
v___x_3035_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__3));
v___x_3064_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3034_, v___x_3035_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_del_object(v___x_3027_);
v___y_3037_ = v___x_3022_;
goto v___jp_3036_;
}
else
{
lean_object* v_val_3065_; 
v_val_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_val_3065_);
lean_dec_ref(v___x_3064_);
if (lean_obj_tag(v_val_3065_) == 1)
{
uint8_t v_v_3066_; 
v_v_3066_ = lean_ctor_get_uint8(v_val_3065_, 0);
lean_dec_ref(v_val_3065_);
if (v_v_3066_ == 0)
{
lean_del_object(v___x_3027_);
v___y_3037_ = v_v_3066_;
goto v___jp_3036_;
}
else
{
lean_object* v___x_3067_; lean_object* v___x_3069_; 
lean_dec_ref(v___x_3014_);
lean_dec_ref(v___x_2981_);
lean_dec(v_stx_2980_);
v___x_3067_ = lean_box(0);
if (v_isShared_3028_ == 0)
{
lean_ctor_set(v___x_3027_, 0, v___x_3067_);
v___x_3069_ = v___x_3027_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v___x_3067_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
else
{
lean_dec(v_val_3065_);
lean_del_object(v___x_3027_);
v___y_3037_ = v___x_3022_;
goto v___jp_3036_;
}
}
v___jp_3036_:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; lean_object* v___x_3063_; 
v___x_3038_ = l_Lean_SourceInfo_fromRef(v_ref_2995_, v___y_3037_);
v___x_3039_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5));
v___x_3040_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1___closed__0));
v___x_3041_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__6));
v___x_3042_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__7));
lean_inc_ref(v___x_2981_);
v___x_3043_ = l_Lean_Name_mkStr4(v___x_2981_, v___x_3040_, v___x_3041_, v___x_3042_);
v___x_3044_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__8));
v___x_3045_ = l_Lean_Name_mkStr4(v___x_2981_, v___x_3040_, v___x_3041_, v___x_3044_);
lean_inc_n(v___x_3038_, 6);
v___x_3046_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3038_);
lean_ctor_set(v___x_3046_, 1, v___x_3044_);
v___x_3047_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__10);
v___x_3048_ = lean_box(0);
v___x_3049_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3038_);
lean_ctor_set(v___x_3049_, 1, v___x_3047_);
lean_ctor_set(v___x_3049_, 2, v___x_3035_);
lean_ctor_set(v___x_3049_, 3, v___x_3048_);
v___x_3050_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__12));
v___x_3051_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13, &l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13_once, _init_l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__13);
v___x_3052_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3038_);
lean_ctor_set(v___x_3052_, 1, v___x_3050_);
lean_ctor_set(v___x_3052_, 2, v___x_3051_);
v___x_3053_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__14));
v___x_3054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3038_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = l_Lean_Syntax_node4(v___x_3038_, v___x_3045_, v___x_3046_, v___x_3049_, v___x_3052_, v___x_3054_);
v___x_3056_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3038_);
lean_ctor_set(v___x_3056_, 1, v___x_3042_);
lean_inc(v_stx_2980_);
v___x_3057_ = l_Lean_Syntax_node3(v___x_3038_, v___x_3043_, v___x_3055_, v___x_3056_, v_stx_2980_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3039_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v___x_3059_ = lean_box(0);
v___x_3060_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3058_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
lean_ctor_set(v___x_3060_, 2, v___x_3059_);
lean_ctor_set(v___x_3060_, 3, v___x_3059_);
lean_ctor_set(v___x_3060_, 4, v___x_3059_);
lean_ctor_set(v___x_3060_, 5, v___x_3059_);
v___x_3061_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__15));
v___x_3062_ = 4;
v___x_3063_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_2980_, v___x_3060_, v___x_3059_, v___x_3061_, v___x_3059_, v___x_3062_, v___x_3014_, v___y_2987_);
lean_dec_ref(v___x_3014_);
return v___x_3063_;
}
}
}
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec_ref(v___x_3014_);
lean_dec_ref(v___x_2981_);
lean_dec(v_stx_2980_);
v_a_3072_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3024_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3024_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
else
{
lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v___x_3014_);
lean_dec_ref(v___x_2981_);
lean_dec(v_stx_2980_);
v_a_3080_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3017_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3017_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec_ref(v___x_3014_);
lean_dec_ref(v___x_2981_);
lean_dec(v_stx_2980_);
v_a_3088_ = lean_ctor_get(v___x_3015_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3015_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3015_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3015_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed(lean_object* v___x_3096_, lean_object* v_stx_3097_, lean_object* v___x_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
uint8_t v___x_6321__boxed_3106_; lean_object* v_res_3107_; 
v___x_6321__boxed_3106_ = lean_unbox(v___x_3096_);
v_res_3107_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0(v___x_6321__boxed_3106_, v_stx_3097_, v___x_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(lean_object* v_stx_3113_, lean_object* v_a_3114_, lean_object* v_a_3115_){
_start:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; uint8_t v___x_3119_; lean_object* v___x_3120_; lean_object* v___f_3121_; lean_object* v___x_3122_; 
v___x_3117_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_initFn___closed__4_00___x40_Lean_Elab_Tactic_Grind_Lint_2628943379____hygCtx___hyg_2_));
v___x_3118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1));
lean_inc(v_stx_3113_);
v___x_3119_ = l_Lean_Syntax_isOfKind(v_stx_3113_, v___x_3118_);
v___x_3120_ = lean_box(v___x_3119_);
v___f_3121_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3121_, 0, v___x_3120_);
lean_closure_set(v___f_3121_, 1, v_stx_3113_);
lean_closure_set(v___f_3121_, 2, v___x_3117_);
v___x_3122_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_3121_, v_a_3114_, v_a_3115_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed(lean_object* v_stx_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect(v_stx_3123_, v_a_3124_, v_a_3125_);
lean_dec(v_a_3125_);
lean_dec_ref(v_a_3124_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(lean_object* v_a_3128_, lean_object* v_as_3129_, size_t v_sz_3130_, size_t v_i_3131_, uint8_t v_b_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v___x_3140_; 
v___x_3140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___redArg(v_a_3128_, v_as_3129_, v_sz_3130_, v_i_3131_, v_b_3132_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_);
return v___x_3140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2___boxed(lean_object* v_a_3141_, lean_object* v_as_3142_, lean_object* v_sz_3143_, lean_object* v_i_3144_, lean_object* v_b_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
size_t v_sz_boxed_3153_; size_t v_i_boxed_3154_; uint8_t v_b_boxed_3155_; lean_object* v_res_3156_; 
v_sz_boxed_3153_ = lean_unbox_usize(v_sz_3143_);
lean_dec(v_sz_3143_);
v_i_boxed_3154_ = lean_unbox_usize(v_i_3144_);
lean_dec(v_i_3144_);
v_b_boxed_3155_ = lean_unbox(v_b_3145_);
v_res_3156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__2(v_a_3141_, v_as_3142_, v_sz_boxed_3153_, v_i_boxed_3154_, v_b_boxed_3155_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec_ref(v_as_3142_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1(){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3162_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_3163_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___closed__1));
v___x_3164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___closed__1));
v___x_3165_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___boxed), 4, 0);
v___x_3166_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_3162_, v___x_3163_, v___x_3164_, v___x_3165_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1___boxed(lean_object* v_a_3167_){
_start:
{
lean_object* v_res_3168_; 
v_res_3168_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect__1();
return v_res_3168_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(lean_object* v_name_3169_, lean_object* v_suff_3170_){
_start:
{
if (lean_obj_tag(v_name_3169_) == 1)
{
lean_object* v_str_3171_; uint8_t v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
v_str_3171_ = lean_ctor_get(v_name_3169_, 1);
v___x_3172_ = 1;
v___x_3173_ = l_Lean_Name_toString(v_suff_3170_, v___x_3172_);
v___x_3174_ = lean_string_utf8_byte_size(v_str_3171_);
v___x_3175_ = lean_string_utf8_byte_size(v___x_3173_);
v___x_3176_ = lean_nat_dec_le(v___x_3175_, v___x_3174_);
if (v___x_3176_ == 0)
{
lean_dec_ref(v___x_3173_);
return v___x_3176_;
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v___x_3177_ = lean_unsigned_to_nat(0u);
v___x_3178_ = lean_nat_sub(v___x_3174_, v___x_3175_);
v___x_3179_ = lean_string_memcmp(v_str_3171_, v___x_3173_, v___x_3178_, v___x_3177_, v___x_3175_);
lean_dec(v___x_3178_);
lean_dec_ref(v___x_3173_);
return v___x_3179_;
}
}
else
{
uint8_t v___x_3180_; 
lean_dec(v_suff_3170_);
v___x_3180_ = 0;
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix___boxed(lean_object* v_name_3181_, lean_object* v_suff_3182_){
_start:
{
uint8_t v_res_3183_; lean_object* v_r_3184_; 
v_res_3183_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(v_name_3181_, v_suff_3182_);
lean_dec(v_name_3181_);
v_r_3184_ = lean_box(v_res_3183_);
return v_r_3184_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(lean_object* v___x_3185_, lean_object* v_as_3186_, size_t v_i_3187_, size_t v_stop_3188_){
_start:
{
uint8_t v___x_3189_; 
v___x_3189_ = lean_usize_dec_eq(v_i_3187_, v_stop_3188_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___x_3190_ = lean_array_uget_borrowed(v_as_3186_, v_i_3187_);
v___x_3191_ = l_Lean_Name_isPrefixOf(v___x_3190_, v___x_3185_);
if (v___x_3191_ == 0)
{
size_t v___x_3192_; size_t v___x_3193_; 
v___x_3192_ = ((size_t)1ULL);
v___x_3193_ = lean_usize_add(v_i_3187_, v___x_3192_);
v_i_3187_ = v___x_3193_;
goto _start;
}
else
{
return v___x_3191_;
}
}
else
{
uint8_t v___x_3195_; 
v___x_3195_ = 0;
return v___x_3195_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1___boxed(lean_object* v___x_3196_, lean_object* v_as_3197_, lean_object* v_i_3198_, lean_object* v_stop_3199_){
_start:
{
size_t v_i_boxed_3200_; size_t v_stop_boxed_3201_; uint8_t v_res_3202_; lean_object* v_r_3203_; 
v_i_boxed_3200_ = lean_unbox_usize(v_i_3198_);
lean_dec(v_i_3198_);
v_stop_boxed_3201_ = lean_unbox_usize(v_stop_3199_);
lean_dec(v_stop_3199_);
v_res_3202_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(v___x_3196_, v_as_3197_, v_i_boxed_3200_, v_stop_boxed_3201_);
lean_dec_ref(v_as_3197_);
lean_dec(v___x_3196_);
v_r_3203_ = lean_box(v_res_3202_);
return v_r_3203_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(lean_object* v_declName_3207_, lean_object* v_init_3208_, lean_object* v_x_3209_){
_start:
{
if (lean_obj_tag(v_x_3209_) == 0)
{
lean_object* v_k_3210_; lean_object* v_l_3211_; lean_object* v_r_3212_; lean_object* v___x_3213_; 
v_k_3210_ = lean_ctor_get(v_x_3209_, 1);
lean_inc(v_k_3210_);
v_l_3211_ = lean_ctor_get(v_x_3209_, 3);
lean_inc(v_l_3211_);
v_r_3212_ = lean_ctor_get(v_x_3209_, 4);
lean_inc(v_r_3212_);
lean_dec_ref(v_x_3209_);
v___x_3213_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3207_, v_init_3208_, v_l_3211_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_dec(v_r_3212_);
lean_dec(v_k_3210_);
return v___x_3213_;
}
else
{
lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3227_; 
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v___x_3213_, 0);
lean_dec(v_unused_3228_);
v___x_3215_ = v___x_3213_;
v_isShared_3216_ = v_isSharedCheck_3227_;
goto v_resetjp_3214_;
}
else
{
lean_dec(v___x_3213_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3227_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; uint8_t v___x_3218_; 
v___x_3217_ = lean_box(0);
v___x_3218_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_nameEndsWithSuffix(v_declName_3207_, v_k_3210_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; 
lean_del_object(v___x_3215_);
v___x_3219_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0));
v_init_3208_ = v___x_3219_;
v_x_3209_ = v_r_3212_;
goto _start;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
lean_dec(v_r_3212_);
v___x_3221_ = lean_box(v___x_3218_);
v___x_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v___x_3217_);
if (v_isShared_3216_ == 0)
{
lean_ctor_set_tag(v___x_3215_, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3223_);
v___x_3225_ = v___x_3215_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
}
else
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3229_, 0, v_init_3208_);
return v___x_3229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___boxed(lean_object* v_declName_3230_, lean_object* v_init_3231_, lean_object* v_x_3232_){
_start:
{
lean_object* v_res_3233_; 
v_res_3233_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3230_, v_init_3231_, v_x_3232_);
lean_dec(v_declName_3230_);
return v_res_3233_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(lean_object* v_declName_3237_, lean_object* v_as_3238_, size_t v_i_3239_, size_t v_stop_3240_){
_start:
{
uint8_t v___x_3241_; 
v___x_3241_ = lean_usize_dec_eq(v_i_3239_, v_stop_3240_);
if (v___x_3241_ == 0)
{
uint8_t v___x_3242_; uint8_t v___y_3244_; lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v___x_3242_ = 1;
v___x_3248_ = lean_array_uget_borrowed(v_as_3238_, v_i_3239_);
v___x_3249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___closed__1));
v___x_3250_ = lean_name_eq(v___x_3248_, v___x_3249_);
if (v___x_3250_ == 0)
{
uint8_t v___x_3251_; 
v___x_3251_ = l_Lean_Name_isPrefixOf(v___x_3248_, v_declName_3237_);
v___y_3244_ = v___x_3251_;
goto v___jp_3243_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
lean_inc(v_declName_3237_);
v___x_3252_ = l_Lean_Name_components(v_declName_3237_);
v___x_3253_ = l_List_lengthTR___redArg(v___x_3252_);
lean_dec(v___x_3252_);
v___x_3254_ = lean_unsigned_to_nat(1u);
v___x_3255_ = lean_nat_dec_eq(v___x_3253_, v___x_3254_);
lean_dec(v___x_3253_);
v___y_3244_ = v___x_3255_;
goto v___jp_3243_;
}
v___jp_3243_:
{
if (v___y_3244_ == 0)
{
size_t v___x_3245_; size_t v___x_3246_; 
v___x_3245_ = ((size_t)1ULL);
v___x_3246_ = lean_usize_add(v_i_3239_, v___x_3245_);
v_i_3239_ = v___x_3246_;
goto _start;
}
else
{
lean_dec(v_declName_3237_);
return v___x_3242_;
}
}
}
else
{
uint8_t v___x_3256_; 
lean_dec(v_declName_3237_);
v___x_3256_ = 0;
return v___x_3256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0___boxed(lean_object* v_declName_3257_, lean_object* v_as_3258_, lean_object* v_i_3259_, lean_object* v_stop_3260_){
_start:
{
size_t v_i_boxed_3261_; size_t v_stop_boxed_3262_; uint8_t v_res_3263_; lean_object* v_r_3264_; 
v_i_boxed_3261_ = lean_unbox_usize(v_i_3259_);
lean_dec(v_i_3259_);
v_stop_boxed_3262_ = lean_unbox_usize(v_stop_3260_);
lean_dec(v_stop_3260_);
v_res_3263_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(v_declName_3257_, v_as_3258_, v_i_boxed_3261_, v_stop_boxed_3262_);
lean_dec_ref(v_as_3258_);
v_r_3264_ = lean_box(v_res_3263_);
return v_r_3264_;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(lean_object* v_prefixes_x3f_3265_, uint8_t v_inModule_3266_, lean_object* v___x_3267_, lean_object* v___x_3268_, lean_object* v___x_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
if (lean_obj_tag(v_a_3270_) == 0)
{
lean_object* v___x_3272_; 
lean_dec(v___x_3269_);
v___x_3272_ = lean_array_to_list(v_a_3271_);
return v___x_3272_;
}
else
{
lean_object* v_head_3273_; lean_object* v_tail_3274_; lean_object* v_val_3276_; 
v_head_3273_ = lean_ctor_get(v_a_3270_, 0);
lean_inc(v_head_3273_);
v_tail_3274_ = lean_ctor_get(v_a_3270_, 1);
lean_inc(v_tail_3274_);
lean_dec_ref(v_a_3270_);
if (lean_obj_tag(v_head_3273_) == 0)
{
lean_object* v_declName_3279_; uint8_t v___y_3281_; uint8_t v___x_3310_; lean_object* v___y_3312_; 
v_declName_3279_ = lean_ctor_get(v_head_3273_, 0);
lean_inc(v_declName_3279_);
lean_dec_ref(v_head_3273_);
v___x_3310_ = l_Lean_NameSet_contains(v___x_3268_, v_declName_3279_);
if (v___x_3310_ == 0)
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v_a_3318_; 
v___x_3316_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2___closed__0));
lean_inc(v___x_3269_);
v___x_3317_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__2(v_declName_3279_, v___x_3316_, v___x_3269_);
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref(v___x_3317_);
v___y_3312_ = v_a_3318_;
goto v___jp_3311_;
}
else
{
lean_dec(v_declName_3279_);
v_a_3270_ = v_tail_3274_;
goto _start;
}
v___jp_3280_:
{
if (v___y_3281_ == 0)
{
if (lean_obj_tag(v_prefixes_x3f_3265_) == 1)
{
if (v_inModule_3266_ == 0)
{
lean_object* v_val_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_val_3282_ = lean_ctor_get(v_prefixes_x3f_3265_, 0);
v___x_3283_ = lean_unsigned_to_nat(0u);
v___x_3284_ = lean_array_get_size(v_val_3282_);
v___x_3285_ = lean_nat_dec_lt(v___x_3283_, v___x_3284_);
if (v___x_3285_ == 0)
{
lean_dec(v_declName_3279_);
v_a_3270_ = v_tail_3274_;
goto _start;
}
else
{
if (v___x_3285_ == 0)
{
lean_dec(v_declName_3279_);
v_a_3270_ = v_tail_3274_;
goto _start;
}
else
{
size_t v___x_3288_; size_t v___x_3289_; uint8_t v___x_3290_; 
v___x_3288_ = ((size_t)0ULL);
v___x_3289_ = lean_usize_of_nat(v___x_3284_);
lean_inc(v_declName_3279_);
v___x_3290_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__0(v_declName_3279_, v_val_3282_, v___x_3288_, v___x_3289_);
if (v___x_3290_ == 0)
{
lean_dec(v_declName_3279_);
v_a_3270_ = v_tail_3274_;
goto _start;
}
else
{
v_val_3276_ = v_declName_3279_;
goto v___jp_3275_;
}
}
}
}
else
{
lean_object* v_val_3292_; lean_object* v___x_3293_; 
v_val_3292_ = lean_ctor_get(v_prefixes_x3f_3265_, 0);
v___x_3293_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_3267_, v_declName_3279_);
if (lean_obj_tag(v___x_3293_) == 1)
{
lean_object* v_val_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; 
v_val_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_val_3294_);
lean_dec_ref(v___x_3293_);
v___x_3295_ = lean_unsigned_to_nat(0u);
v___x_3296_ = lean_array_get_size(v_val_3292_);
v___x_3297_ = lean_nat_dec_lt(v___x_3295_, v___x_3296_);
if (v___x_3297_ == 0)
{
lean_dec(v_val_3294_);
lean_dec(v_declName_3279_);
v_a_3270_ = v_tail_3274_;
goto _start;
}
else
{
if (v___x_3297_ == 0)
{
lean_dec(v_val_3294_);
lean_dec(v_declName_3279_);
v_a_3270_ = v_tail_3274_;
goto _start;
}
else
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; size_t v___x_3304_; size_t v___x_3305_; uint8_t v___x_3306_; 
v___x_3300_ = lean_box(0);
v___x_3301_ = l_Lean_Environment_header(v___x_3267_);
v___x_3302_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3301_);
v___x_3303_ = lean_array_get(v___x_3300_, v___x_3302_, v_val_3294_);
lean_dec(v_val_3294_);
lean_dec_ref(v___x_3302_);
v___x_3304_ = ((size_t)0ULL);
v___x_3305_ = lean_usize_of_nat(v___x_3296_);
v___x_3306_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__1(v___x_3303_, v_val_3292_, v___x_3304_, v___x_3305_);
lean_dec(v___x_3303_);
if (v___x_3306_ == 0)
{
lean_dec(v_declName_3279_);
v_a_3270_ = v_tail_3274_;
goto _start;
}
else
{
v_val_3276_ = v_declName_3279_;
goto v___jp_3275_;
}
}
}
}
else
{
lean_dec(v___x_3293_);
lean_dec(v_declName_3279_);
v_a_3270_ = v_tail_3274_;
goto _start;
}
}
}
else
{
v_val_3276_ = v_declName_3279_;
goto v___jp_3275_;
}
}
else
{
lean_dec(v_declName_3279_);
v_a_3270_ = v_tail_3274_;
goto _start;
}
}
v___jp_3311_:
{
lean_object* v_fst_3313_; 
v_fst_3313_ = lean_ctor_get(v___y_3312_, 0);
lean_inc(v_fst_3313_);
lean_dec_ref(v___y_3312_);
if (lean_obj_tag(v_fst_3313_) == 0)
{
v___y_3281_ = v___x_3310_;
goto v___jp_3280_;
}
else
{
lean_object* v_val_3314_; uint8_t v___x_3315_; 
v_val_3314_ = lean_ctor_get(v_fst_3313_, 0);
lean_inc(v_val_3314_);
lean_dec_ref(v_fst_3313_);
v___x_3315_ = lean_unbox(v_val_3314_);
lean_dec(v_val_3314_);
v___y_3281_ = v___x_3315_;
goto v___jp_3280_;
}
}
}
else
{
lean_dec(v_head_3273_);
v_a_3270_ = v_tail_3274_;
goto _start;
}
v___jp_3275_:
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_array_push(v_a_3271_, v_val_3276_);
v_a_3270_ = v_tail_3274_;
v_a_3271_ = v___x_3277_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3___boxed(lean_object* v_prefixes_x3f_3321_, lean_object* v_inModule_3322_, lean_object* v___x_3323_, lean_object* v___x_3324_, lean_object* v___x_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_){
_start:
{
uint8_t v_inModule_boxed_3328_; lean_object* v_res_3329_; 
v_inModule_boxed_3328_ = lean_unbox(v_inModule_3322_);
v_res_3329_ = l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(v_prefixes_x3f_3321_, v_inModule_boxed_3328_, v___x_3323_, v___x_3324_, v___x_3325_, v_a_3326_, v_a_3327_);
lean_dec(v___x_3324_);
lean_dec_ref(v___x_3323_);
lean_dec(v_prefixes_x3f_3321_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(lean_object* v_prefixes_x3f_3332_, uint8_t v_inModule_3333_, lean_object* v_a_3334_){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v_env_3338_; lean_object* v___x_3339_; lean_object* v_toEnvExtension_3340_; lean_object* v_asyncMode_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3336_ = lean_st_ref_get(v_a_3334_);
v___x_3337_ = lean_st_ref_get(v_a_3334_);
v_env_3338_ = lean_ctor_get(v___x_3336_, 0);
lean_inc_ref(v_env_3338_);
lean_dec(v___x_3336_);
v___x_3339_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipExt;
v_toEnvExtension_3340_ = lean_ctor_get(v___x_3339_, 0);
v_asyncMode_3341_ = lean_ctor_get(v_toEnvExtension_3340_, 2);
v___x_3342_ = l_Lean_Meta_Grind_grindExt;
v___x_3343_ = l_Lean_Meta_Grind_Extension_getEMatchTheorems___redArg(v___x_3342_, v_a_3334_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3346_; uint8_t v_isShared_3347_; uint8_t v_isSharedCheck_3364_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3346_ = v___x_3343_;
v_isShared_3347_ = v_isSharedCheck_3364_;
goto v_resetjp_3345_;
}
else
{
lean_inc(v_a_3344_);
lean_dec(v___x_3343_);
v___x_3346_ = lean_box(0);
v_isShared_3347_ = v_isSharedCheck_3364_;
goto v_resetjp_3345_;
}
v_resetjp_3345_:
{
lean_object* v___x_3348_; lean_object* v_env_3349_; lean_object* v___x_3350_; lean_object* v_toEnvExtension_3351_; lean_object* v_asyncMode_3352_; lean_object* v_env_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3348_ = lean_st_ref_get(v_a_3334_);
v_env_3349_ = lean_ctor_get(v___x_3337_, 0);
lean_inc_ref(v_env_3349_);
lean_dec(v___x_3337_);
v___x_3350_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_skipSuffixExt;
v_toEnvExtension_3351_ = lean_ctor_get(v___x_3350_, 0);
v_asyncMode_3352_ = lean_ctor_get(v_toEnvExtension_3351_, 2);
v_env_3353_ = lean_ctor_get(v___x_3348_, 0);
lean_inc_ref(v_env_3353_);
lean_dec(v___x_3348_);
v___x_3354_ = lean_box(1);
v___x_3355_ = lean_box(0);
v___x_3356_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3354_, v___x_3339_, v_env_3338_, v_asyncMode_3341_, v___x_3355_);
v___x_3357_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3354_, v___x_3350_, v_env_3349_, v_asyncMode_3352_, v___x_3355_);
v___x_3358_ = l_Lean_Meta_Grind_Theorems_getOrigins___redArg(v_a_3344_);
lean_dec(v_a_3344_);
v___x_3359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0));
v___x_3360_ = l_List_filterMapTR_go___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems_spec__3(v_prefixes_x3f_3332_, v_inModule_3333_, v_env_3353_, v___x_3356_, v___x_3357_, v___x_3358_, v___x_3359_);
lean_dec(v___x_3356_);
lean_dec_ref(v_env_3353_);
if (v_isShared_3347_ == 0)
{
lean_ctor_set(v___x_3346_, 0, v___x_3360_);
v___x_3362_ = v___x_3346_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref(v_env_3338_);
lean_dec(v___x_3337_);
v_a_3365_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3343_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3343_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___boxed(lean_object* v_prefixes_x3f_3373_, lean_object* v_inModule_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_){
_start:
{
uint8_t v_inModule_boxed_3377_; lean_object* v_res_3378_; 
v_inModule_boxed_3377_ = lean_unbox(v_inModule_3374_);
v_res_3378_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v_prefixes_x3f_3373_, v_inModule_boxed_3377_, v_a_3375_);
lean_dec(v_a_3375_);
lean_dec(v_prefixes_x3f_3373_);
return v_res_3378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(lean_object* v_prefixes_x3f_3379_, uint8_t v_inModule_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v_prefixes_x3f_3379_, v_inModule_3380_, v_a_3382_);
return v___x_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___boxed(lean_object* v_prefixes_x3f_3385_, lean_object* v_inModule_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
uint8_t v_inModule_boxed_3390_; lean_object* v_res_3391_; 
v_inModule_boxed_3390_ = lean_unbox(v_inModule_3386_);
v_res_3391_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems(v_prefixes_x3f_3385_, v_inModule_boxed_3390_, v_a_3387_, v_a_3388_);
lean_dec(v_a_3388_);
lean_dec_ref(v_a_3387_);
lean_dec(v_prefixes_x3f_3385_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(size_t v_sz_3392_, size_t v_i_3393_, lean_object* v_bs_3394_){
_start:
{
uint8_t v___x_3395_; 
v___x_3395_ = lean_usize_dec_lt(v_i_3393_, v_sz_3392_);
if (v___x_3395_ == 0)
{
return v_bs_3394_;
}
else
{
lean_object* v_v_3396_; lean_object* v___x_3397_; lean_object* v_bs_x27_3398_; lean_object* v___x_3399_; size_t v___x_3400_; size_t v___x_3401_; lean_object* v___x_3402_; 
v_v_3396_ = lean_array_uget(v_bs_3394_, v_i_3393_);
v___x_3397_ = lean_unsigned_to_nat(0u);
v_bs_x27_3398_ = lean_array_uset(v_bs_3394_, v_i_3393_, v___x_3397_);
v___x_3399_ = l_Lean_TSyntax_getId(v_v_3396_);
lean_dec(v_v_3396_);
v___x_3400_ = ((size_t)1ULL);
v___x_3401_ = lean_usize_add(v_i_3393_, v___x_3400_);
v___x_3402_ = lean_array_uset(v_bs_x27_3398_, v_i_3393_, v___x_3399_);
v_i_3393_ = v___x_3401_;
v_bs_3394_ = v___x_3402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4___boxed(lean_object* v_sz_3404_, lean_object* v_i_3405_, lean_object* v_bs_3406_){
_start:
{
size_t v_sz_boxed_3407_; size_t v_i_boxed_3408_; lean_object* v_res_3409_; 
v_sz_boxed_3407_ = lean_unbox_usize(v_sz_3404_);
lean_dec(v_sz_3404_);
v_i_boxed_3408_ = lean_unbox_usize(v_i_3405_);
lean_dec(v_i_3405_);
v_res_3409_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(v_sz_boxed_3407_, v_i_boxed_3408_, v_bs_3406_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(lean_object* v_hi_3410_, lean_object* v_pivot_3411_, lean_object* v_as_3412_, lean_object* v_i_3413_, lean_object* v_k_3414_){
_start:
{
uint8_t v___x_3415_; 
v___x_3415_ = lean_nat_dec_lt(v_k_3414_, v_hi_3410_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
lean_dec(v_k_3414_);
v___x_3416_ = lean_array_fswap(v_as_3412_, v_i_3413_, v_hi_3410_);
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v_i_3413_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
return v___x_3417_;
}
else
{
lean_object* v___x_3418_; uint8_t v___x_3419_; 
v___x_3418_ = lean_array_fget_borrowed(v_as_3412_, v_k_3414_);
v___x_3419_ = l_Lean_Name_lt(v___x_3418_, v_pivot_3411_);
if (v___x_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3421_; 
v___x_3420_ = lean_unsigned_to_nat(1u);
v___x_3421_ = lean_nat_add(v_k_3414_, v___x_3420_);
lean_dec(v_k_3414_);
v_k_3414_ = v___x_3421_;
goto _start;
}
else
{
lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3423_ = lean_array_fswap(v_as_3412_, v_i_3413_, v_k_3414_);
v___x_3424_ = lean_unsigned_to_nat(1u);
v___x_3425_ = lean_nat_add(v_i_3413_, v___x_3424_);
lean_dec(v_i_3413_);
v___x_3426_ = lean_nat_add(v_k_3414_, v___x_3424_);
lean_dec(v_k_3414_);
v_as_3412_ = v___x_3423_;
v_i_3413_ = v___x_3425_;
v_k_3414_ = v___x_3426_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg___boxed(lean_object* v_hi_3428_, lean_object* v_pivot_3429_, lean_object* v_as_3430_, lean_object* v_i_3431_, lean_object* v_k_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_3428_, v_pivot_3429_, v_as_3430_, v_i_3431_, v_k_3432_);
lean_dec(v_pivot_3429_);
lean_dec(v_hi_3428_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(lean_object* v_n_3434_, lean_object* v_as_3435_, lean_object* v_lo_3436_, lean_object* v_hi_3437_){
_start:
{
lean_object* v___y_3439_; uint8_t v___x_3449_; 
v___x_3449_ = lean_nat_dec_lt(v_lo_3436_, v_hi_3437_);
if (v___x_3449_ == 0)
{
lean_dec(v_lo_3436_);
return v_as_3435_;
}
else
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v_mid_3452_; lean_object* v___y_3454_; lean_object* v___y_3460_; lean_object* v___x_3465_; lean_object* v___x_3466_; uint8_t v___x_3467_; 
v___x_3450_ = lean_nat_add(v_lo_3436_, v_hi_3437_);
v___x_3451_ = lean_unsigned_to_nat(1u);
v_mid_3452_ = lean_nat_shiftr(v___x_3450_, v___x_3451_);
lean_dec(v___x_3450_);
v___x_3465_ = lean_array_fget_borrowed(v_as_3435_, v_mid_3452_);
v___x_3466_ = lean_array_fget_borrowed(v_as_3435_, v_lo_3436_);
v___x_3467_ = l_Lean_Name_lt(v___x_3465_, v___x_3466_);
if (v___x_3467_ == 0)
{
v___y_3460_ = v_as_3435_;
goto v___jp_3459_;
}
else
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_array_fswap(v_as_3435_, v_lo_3436_, v_mid_3452_);
v___y_3460_ = v___x_3468_;
goto v___jp_3459_;
}
v___jp_3453_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; uint8_t v___x_3457_; 
v___x_3455_ = lean_array_fget_borrowed(v___y_3454_, v_mid_3452_);
v___x_3456_ = lean_array_fget_borrowed(v___y_3454_, v_hi_3437_);
v___x_3457_ = l_Lean_Name_lt(v___x_3455_, v___x_3456_);
if (v___x_3457_ == 0)
{
lean_dec(v_mid_3452_);
v___y_3439_ = v___y_3454_;
goto v___jp_3438_;
}
else
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_array_fswap(v___y_3454_, v_mid_3452_, v_hi_3437_);
lean_dec(v_mid_3452_);
v___y_3439_ = v___x_3458_;
goto v___jp_3438_;
}
}
v___jp_3459_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; uint8_t v___x_3463_; 
v___x_3461_ = lean_array_fget_borrowed(v___y_3460_, v_hi_3437_);
v___x_3462_ = lean_array_fget_borrowed(v___y_3460_, v_lo_3436_);
v___x_3463_ = l_Lean_Name_lt(v___x_3461_, v___x_3462_);
if (v___x_3463_ == 0)
{
v___y_3454_ = v___y_3460_;
goto v___jp_3453_;
}
else
{
lean_object* v___x_3464_; 
v___x_3464_ = lean_array_fswap(v___y_3460_, v_lo_3436_, v_hi_3437_);
v___y_3454_ = v___x_3464_;
goto v___jp_3453_;
}
}
}
v___jp_3438_:
{
lean_object* v_pivot_3440_; lean_object* v___x_3441_; lean_object* v_fst_3442_; lean_object* v_snd_3443_; uint8_t v___x_3444_; 
v_pivot_3440_ = lean_array_fget(v___y_3439_, v_hi_3437_);
lean_inc_n(v_lo_3436_, 2);
v___x_3441_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_3437_, v_pivot_3440_, v___y_3439_, v_lo_3436_, v_lo_3436_);
lean_dec(v_pivot_3440_);
v_fst_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_fst_3442_);
v_snd_3443_ = lean_ctor_get(v___x_3441_, 1);
lean_inc(v_snd_3443_);
lean_dec_ref(v___x_3441_);
v___x_3444_ = lean_nat_dec_le(v_hi_3437_, v_fst_3442_);
if (v___x_3444_ == 0)
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_3434_, v_snd_3443_, v_lo_3436_, v_fst_3442_);
v___x_3446_ = lean_unsigned_to_nat(1u);
v___x_3447_ = lean_nat_add(v_fst_3442_, v___x_3446_);
lean_dec(v_fst_3442_);
v_as_3435_ = v___x_3445_;
v_lo_3436_ = v___x_3447_;
goto _start;
}
else
{
lean_dec(v_fst_3442_);
lean_dec(v_lo_3436_);
return v_snd_3443_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg___boxed(lean_object* v_n_3469_, lean_object* v_as_3470_, lean_object* v_lo_3471_, lean_object* v_hi_3472_){
_start:
{
lean_object* v_res_3473_; 
v_res_3473_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_3469_, v_as_3470_, v_lo_3471_, v_hi_3472_);
lean_dec(v_hi_3472_);
lean_dec(v_n_3469_);
return v_res_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_3474_, lean_object* v_msgData_3475_, uint8_t v_severity_3476_, uint8_t v_isSilent_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v___y_3484_; uint8_t v___y_3485_; lean_object* v___y_3486_; uint8_t v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3520_; lean_object* v___y_3521_; uint8_t v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; uint8_t v___y_3549_; lean_object* v___y_3550_; uint8_t v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3556_; lean_object* v___y_3557_; uint8_t v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; uint8_t v___y_3561_; uint8_t v___y_3562_; uint8_t v___x_3567_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; uint8_t v___y_3573_; uint8_t v___y_3574_; uint8_t v___y_3575_; uint8_t v___y_3577_; uint8_t v___x_3592_; 
v___x_3567_ = 2;
v___x_3592_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3476_, v___x_3567_);
if (v___x_3592_ == 0)
{
v___y_3577_ = v___x_3592_;
goto v___jp_3576_;
}
else
{
uint8_t v___x_3593_; 
lean_inc_ref(v_msgData_3475_);
v___x_3593_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3475_);
v___y_3577_ = v___x_3593_;
goto v___jp_3576_;
}
v___jp_3483_:
{
lean_object* v___x_3493_; lean_object* v_currNamespace_3494_; lean_object* v_openDecls_3495_; lean_object* v_env_3496_; lean_object* v_nextMacroScope_3497_; lean_object* v_ngen_3498_; lean_object* v_auxDeclNGen_3499_; lean_object* v_traceState_3500_; lean_object* v_cache_3501_; lean_object* v_messages_3502_; lean_object* v_infoState_3503_; lean_object* v_snapshotTasks_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3518_; 
v___x_3493_ = lean_st_ref_take(v___y_3492_);
v_currNamespace_3494_ = lean_ctor_get(v___y_3491_, 6);
v_openDecls_3495_ = lean_ctor_get(v___y_3491_, 7);
v_env_3496_ = lean_ctor_get(v___x_3493_, 0);
v_nextMacroScope_3497_ = lean_ctor_get(v___x_3493_, 1);
v_ngen_3498_ = lean_ctor_get(v___x_3493_, 2);
v_auxDeclNGen_3499_ = lean_ctor_get(v___x_3493_, 3);
v_traceState_3500_ = lean_ctor_get(v___x_3493_, 4);
v_cache_3501_ = lean_ctor_get(v___x_3493_, 5);
v_messages_3502_ = lean_ctor_get(v___x_3493_, 6);
v_infoState_3503_ = lean_ctor_get(v___x_3493_, 7);
v_snapshotTasks_3504_ = lean_ctor_get(v___x_3493_, 8);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3506_ = v___x_3493_;
v_isShared_3507_ = v_isSharedCheck_3518_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_snapshotTasks_3504_);
lean_inc(v_infoState_3503_);
lean_inc(v_messages_3502_);
lean_inc(v_cache_3501_);
lean_inc(v_traceState_3500_);
lean_inc(v_auxDeclNGen_3499_);
lean_inc(v_ngen_3498_);
lean_inc(v_nextMacroScope_3497_);
lean_inc(v_env_3496_);
lean_dec(v___x_3493_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3518_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3513_; 
lean_inc(v_openDecls_3495_);
lean_inc(v_currNamespace_3494_);
v___x_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3508_, 0, v_currNamespace_3494_);
lean_ctor_set(v___x_3508_, 1, v_openDecls_3495_);
v___x_3509_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
lean_ctor_set(v___x_3509_, 1, v___y_3486_);
lean_inc_ref(v___y_3488_);
lean_inc_ref(v___y_3484_);
v___x_3510_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3510_, 0, v___y_3484_);
lean_ctor_set(v___x_3510_, 1, v___y_3490_);
lean_ctor_set(v___x_3510_, 2, v___y_3489_);
lean_ctor_set(v___x_3510_, 3, v___y_3488_);
lean_ctor_set(v___x_3510_, 4, v___x_3509_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*5, v___y_3487_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*5 + 1, v___y_3485_);
lean_ctor_set_uint8(v___x_3510_, sizeof(void*)*5 + 2, v_isSilent_3477_);
v___x_3511_ = l_Lean_MessageLog_add(v___x_3510_, v_messages_3502_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 6, v___x_3511_);
v___x_3513_ = v___x_3506_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_env_3496_);
lean_ctor_set(v_reuseFailAlloc_3517_, 1, v_nextMacroScope_3497_);
lean_ctor_set(v_reuseFailAlloc_3517_, 2, v_ngen_3498_);
lean_ctor_set(v_reuseFailAlloc_3517_, 3, v_auxDeclNGen_3499_);
lean_ctor_set(v_reuseFailAlloc_3517_, 4, v_traceState_3500_);
lean_ctor_set(v_reuseFailAlloc_3517_, 5, v_cache_3501_);
lean_ctor_set(v_reuseFailAlloc_3517_, 6, v___x_3511_);
lean_ctor_set(v_reuseFailAlloc_3517_, 7, v_infoState_3503_);
lean_ctor_set(v_reuseFailAlloc_3517_, 8, v_snapshotTasks_3504_);
v___x_3513_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
v___x_3514_ = lean_st_ref_set(v___y_3492_, v___x_3513_);
v___x_3515_ = lean_box(0);
v___x_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
return v___x_3516_;
}
}
}
v___jp_3519_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3543_; 
v___x_3528_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3475_);
v___x_3529_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__0(v___x_3528_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3532_ = v___x_3529_;
v_isShared_3533_ = v_isSharedCheck_3543_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3529_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3543_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_inc_ref_n(v___y_3524_, 2);
v___x_3534_ = l_Lean_FileMap_toPosition(v___y_3524_, v___y_3525_);
lean_dec(v___y_3525_);
v___x_3535_ = l_Lean_FileMap_toPosition(v___y_3524_, v___y_3527_);
lean_dec(v___y_3527_);
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
v___x_3537_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_thmsToMessageData_spec__2___closed__3));
if (v___y_3526_ == 0)
{
lean_del_object(v___x_3532_);
lean_dec_ref(v___y_3520_);
v___y_3484_ = v___y_3521_;
v___y_3485_ = v___y_3522_;
v___y_3486_ = v_a_3530_;
v___y_3487_ = v___y_3523_;
v___y_3488_ = v___x_3537_;
v___y_3489_ = v___x_3536_;
v___y_3490_ = v___x_3534_;
v___y_3491_ = v___y_3480_;
v___y_3492_ = v___y_3481_;
goto v___jp_3483_;
}
else
{
uint8_t v___x_3538_; 
lean_inc(v_a_3530_);
v___x_3538_ = l_Lean_MessageData_hasTag(v___y_3520_, v_a_3530_);
if (v___x_3538_ == 0)
{
lean_object* v___x_3539_; lean_object* v___x_3541_; 
lean_dec_ref(v___x_3536_);
lean_dec_ref(v___x_3534_);
lean_dec(v_a_3530_);
v___x_3539_ = lean_box(0);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v___x_3539_);
v___x_3541_ = v___x_3532_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
else
{
lean_del_object(v___x_3532_);
v___y_3484_ = v___y_3521_;
v___y_3485_ = v___y_3522_;
v___y_3486_ = v_a_3530_;
v___y_3487_ = v___y_3523_;
v___y_3488_ = v___x_3537_;
v___y_3489_ = v___x_3536_;
v___y_3490_ = v___x_3534_;
v___y_3491_ = v___y_3480_;
v___y_3492_ = v___y_3481_;
goto v___jp_3483_;
}
}
}
}
v___jp_3544_:
{
lean_object* v___x_3553_; 
v___x_3553_ = l_Lean_Syntax_getTailPos_x3f(v___y_3547_, v___y_3549_);
lean_dec(v___y_3547_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_inc(v___y_3552_);
v___y_3520_ = v___y_3545_;
v___y_3521_ = v___y_3546_;
v___y_3522_ = v___y_3548_;
v___y_3523_ = v___y_3549_;
v___y_3524_ = v___y_3550_;
v___y_3525_ = v___y_3552_;
v___y_3526_ = v___y_3551_;
v___y_3527_ = v___y_3552_;
goto v___jp_3519_;
}
else
{
lean_object* v_val_3554_; 
v_val_3554_ = lean_ctor_get(v___x_3553_, 0);
lean_inc(v_val_3554_);
lean_dec_ref(v___x_3553_);
v___y_3520_ = v___y_3545_;
v___y_3521_ = v___y_3546_;
v___y_3522_ = v___y_3548_;
v___y_3523_ = v___y_3549_;
v___y_3524_ = v___y_3550_;
v___y_3525_ = v___y_3552_;
v___y_3526_ = v___y_3551_;
v___y_3527_ = v_val_3554_;
goto v___jp_3519_;
}
}
v___jp_3555_:
{
lean_object* v_ref_3563_; lean_object* v___x_3564_; 
v_ref_3563_ = l_Lean_replaceRef(v_ref_3474_, v___y_3559_);
v___x_3564_ = l_Lean_Syntax_getPos_x3f(v_ref_3563_, v___y_3558_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v___x_3565_; 
v___x_3565_ = lean_unsigned_to_nat(0u);
v___y_3545_ = v___y_3556_;
v___y_3546_ = v___y_3557_;
v___y_3547_ = v_ref_3563_;
v___y_3548_ = v___y_3562_;
v___y_3549_ = v___y_3558_;
v___y_3550_ = v___y_3560_;
v___y_3551_ = v___y_3561_;
v___y_3552_ = v___x_3565_;
goto v___jp_3544_;
}
else
{
lean_object* v_val_3566_; 
v_val_3566_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_val_3566_);
lean_dec_ref(v___x_3564_);
v___y_3545_ = v___y_3556_;
v___y_3546_ = v___y_3557_;
v___y_3547_ = v_ref_3563_;
v___y_3548_ = v___y_3562_;
v___y_3549_ = v___y_3558_;
v___y_3550_ = v___y_3560_;
v___y_3551_ = v___y_3561_;
v___y_3552_ = v_val_3566_;
goto v___jp_3544_;
}
}
v___jp_3568_:
{
if (v___y_3575_ == 0)
{
v___y_3556_ = v___y_3571_;
v___y_3557_ = v___y_3569_;
v___y_3558_ = v___y_3574_;
v___y_3559_ = v___y_3570_;
v___y_3560_ = v___y_3572_;
v___y_3561_ = v___y_3573_;
v___y_3562_ = v_severity_3476_;
goto v___jp_3555_;
}
else
{
v___y_3556_ = v___y_3571_;
v___y_3557_ = v___y_3569_;
v___y_3558_ = v___y_3574_;
v___y_3559_ = v___y_3570_;
v___y_3560_ = v___y_3572_;
v___y_3561_ = v___y_3573_;
v___y_3562_ = v___x_3567_;
goto v___jp_3555_;
}
}
v___jp_3576_:
{
if (v___y_3577_ == 0)
{
lean_object* v_fileName_3578_; lean_object* v_fileMap_3579_; lean_object* v_options_3580_; lean_object* v_ref_3581_; uint8_t v_suppressElabErrors_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___f_3585_; uint8_t v___x_3586_; uint8_t v___x_3587_; 
v_fileName_3578_ = lean_ctor_get(v___y_3480_, 0);
v_fileMap_3579_ = lean_ctor_get(v___y_3480_, 1);
v_options_3580_ = lean_ctor_get(v___y_3480_, 2);
v_ref_3581_ = lean_ctor_get(v___y_3480_, 5);
v_suppressElabErrors_3582_ = lean_ctor_get_uint8(v___y_3480_, sizeof(void*)*14 + 1);
v___x_3583_ = lean_box(v___y_3577_);
v___x_3584_ = lean_box(v_suppressElabErrors_3582_);
v___f_3585_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem_spec__3_spec__4_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3585_, 0, v___x_3583_);
lean_closure_set(v___f_3585_, 1, v___x_3584_);
v___x_3586_ = 1;
v___x_3587_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3476_, v___x_3586_);
if (v___x_3587_ == 0)
{
v___y_3569_ = v_fileName_3578_;
v___y_3570_ = v_ref_3581_;
v___y_3571_ = v___f_3585_;
v___y_3572_ = v_fileMap_3579_;
v___y_3573_ = v_suppressElabErrors_3582_;
v___y_3574_ = v___y_3577_;
v___y_3575_ = v___x_3587_;
goto v___jp_3568_;
}
else
{
lean_object* v___x_3588_; uint8_t v___x_3589_; 
v___x_3588_ = l_Lean_warningAsError;
v___x_3589_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintSkip_spec__0_spec__1_spec__3(v_options_3580_, v___x_3588_);
v___y_3569_ = v_fileName_3578_;
v___y_3570_ = v_ref_3581_;
v___y_3571_ = v___f_3585_;
v___y_3572_ = v_fileMap_3579_;
v___y_3573_ = v_suppressElabErrors_3582_;
v___y_3574_ = v___y_3577_;
v___y_3575_ = v___x_3589_;
goto v___jp_3568_;
}
}
else
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
lean_dec_ref(v_msgData_3475_);
v___x_3590_ = lean_box(0);
v___x_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
return v___x_3591_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_3594_, lean_object* v_msgData_3595_, lean_object* v_severity_3596_, lean_object* v_isSilent_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
uint8_t v_severity_boxed_3603_; uint8_t v_isSilent_boxed_3604_; lean_object* v_res_3605_; 
v_severity_boxed_3603_ = lean_unbox(v_severity_3596_);
v_isSilent_boxed_3604_ = lean_unbox(v_isSilent_3597_);
v_res_3605_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_3594_, v_msgData_3595_, v_severity_boxed_3603_, v_isSilent_boxed_3604_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
lean_dec(v___y_3601_);
lean_dec_ref(v___y_3600_);
lean_dec(v___y_3599_);
lean_dec_ref(v___y_3598_);
lean_dec(v_ref_3594_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(lean_object* v_msgData_3606_, uint8_t v_severity_3607_, uint8_t v_isSilent_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v_ref_3616_; lean_object* v___x_3617_; 
v_ref_3616_ = lean_ctor_get(v___y_3613_, 5);
v___x_3617_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_3616_, v_msgData_3606_, v_severity_3607_, v_isSilent_3608_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0___boxed(lean_object* v_msgData_3618_, lean_object* v_severity_3619_, lean_object* v_isSilent_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
uint8_t v_severity_boxed_3628_; uint8_t v_isSilent_boxed_3629_; lean_object* v_res_3630_; 
v_severity_boxed_3628_ = lean_unbox(v_severity_3619_);
v_isSilent_boxed_3629_ = lean_unbox(v_isSilent_3620_);
v_res_3630_ = l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(v_msgData_3618_, v_severity_boxed_3628_, v_isSilent_boxed_3629_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(lean_object* v_msgData_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
uint8_t v___x_3639_; uint8_t v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = 2;
v___x_3640_ = 0;
v___x_3641_ = l_Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0(v_msgData_3631_, v___x_3639_, v___x_3640_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0___boxed(lean_object* v_msgData_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v_res_3650_; 
v_res_3650_ = l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(v_msgData_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
lean_dec(v___y_3648_);
lean_dec_ref(v___y_3647_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
return v_res_3650_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__0));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(lean_object* v_a_3654_, lean_object* v_as_3655_, size_t v_sz_3656_, size_t v_i_3657_, lean_object* v_b_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
lean_object* v_snd_3667_; uint8_t v___x_3671_; 
v___x_3671_ = lean_usize_dec_lt(v_i_3657_, v_sz_3656_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; 
lean_dec_ref(v_a_3654_);
v___x_3672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3672_, 0, v_b_3658_);
return v___x_3672_;
}
else
{
lean_object* v_a_3673_; lean_object* v___x_3674_; 
v_a_3673_ = lean_array_uget_borrowed(v_as_3655_, v_i_3657_);
lean_inc_ref(v_a_3654_);
lean_inc(v_a_3673_);
v___x_3674_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem(v_a_3673_, v_a_3654_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_object* v_a_3675_; uint8_t v___x_3676_; 
v_a_3675_ = lean_ctor_get(v___x_3674_, 0);
lean_inc(v_a_3675_);
lean_dec_ref(v___x_3674_);
v___x_3676_ = lean_unbox(v_a_3675_);
lean_dec(v_a_3675_);
if (v___x_3676_ == 0)
{
v_snd_3667_ = v_b_3658_;
goto v___jp_3666_;
}
else
{
lean_object* v___x_3677_; 
lean_inc(v_a_3673_);
v___x_3677_ = lean_array_push(v_b_3658_, v_a_3673_);
v_snd_3667_ = v___x_3677_;
goto v___jp_3666_;
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3703_; 
v_a_3678_ = lean_ctor_get(v___x_3674_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3674_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3680_ = v___x_3674_;
v_isShared_3681_ = v_isSharedCheck_3703_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3674_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3703_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
uint8_t v___y_3683_; uint8_t v___x_3701_; 
v___x_3701_ = l_Lean_Exception_isInterrupt(v_a_3678_);
if (v___x_3701_ == 0)
{
uint8_t v___x_3702_; 
lean_inc(v_a_3678_);
v___x_3702_ = l_Lean_Exception_isRuntime(v_a_3678_);
v___y_3683_ = v___x_3702_;
goto v___jp_3682_;
}
else
{
v___y_3683_ = v___x_3701_;
goto v___jp_3682_;
}
v___jp_3682_:
{
if (v___y_3683_ == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
lean_del_object(v___x_3680_);
lean_inc(v_a_3673_);
v___x_3684_ = l_Lean_MessageData_ofName(v_a_3673_);
v___x_3685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___closed__1);
v___x_3686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3684_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___x_3687_ = l_Lean_Exception_toMessageData(v_a_3678_);
v___x_3688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3686_);
lean_ctor_set(v___x_3688_, 1, v___x_3687_);
v___x_3689_ = l_Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0(v___x_3688_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_dec_ref(v___x_3689_);
v_snd_3667_ = v_b_3658_;
goto v___jp_3666_;
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec_ref(v_b_3658_);
lean_dec_ref(v_a_3654_);
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3689_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3689_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
else
{
lean_object* v___x_3699_; 
lean_dec_ref(v_b_3658_);
lean_dec_ref(v_a_3654_);
if (v_isShared_3681_ == 0)
{
v___x_3699_ = v___x_3680_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3678_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
}
v___jp_3666_:
{
size_t v___x_3668_; size_t v___x_3669_; 
v___x_3668_ = ((size_t)1ULL);
v___x_3669_ = lean_usize_add(v_i_3657_, v___x_3668_);
v_i_3657_ = v___x_3669_;
v_b_3658_ = v_snd_3667_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1___boxed(lean_object* v_a_3704_, lean_object* v_as_3705_, lean_object* v_sz_3706_, lean_object* v_i_3707_, lean_object* v_b_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
size_t v_sz_boxed_3716_; size_t v_i_boxed_3717_; lean_object* v_res_3718_; 
v_sz_boxed_3716_ = lean_unbox_usize(v_sz_3706_);
lean_dec(v_sz_3706_);
v_i_boxed_3717_ = lean_unbox_usize(v_i_3707_);
lean_dec(v_i_3707_);
v_res_3718_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(v_a_3704_, v_as_3705_, v_sz_boxed_3716_, v_i_boxed_3717_, v_b_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
lean_dec_ref(v_as_3705_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(lean_object* v_as_3720_, size_t v_sz_3721_, size_t v_i_3722_, lean_object* v_b_3723_){
_start:
{
uint8_t v___x_3725_; 
v___x_3725_ = lean_usize_dec_lt(v_i_3722_, v_sz_3721_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; 
v___x_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3726_, 0, v_b_3723_);
return v___x_3726_;
}
else
{
lean_object* v___x_3727_; lean_object* v_a_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; size_t v___x_3734_; size_t v___x_3735_; 
v___x_3727_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v_a_3728_ = lean_array_uget_borrowed(v_as_3720_, v_i_3722_);
v___x_3729_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___closed__0));
lean_inc(v_a_3728_);
v___x_3730_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_a_3728_, v___x_3725_);
v___x_3731_ = lean_string_append(v___x_3729_, v___x_3730_);
lean_dec_ref(v___x_3730_);
v___x_3732_ = lean_string_append(v___x_3731_, v___x_3727_);
v___x_3733_ = lean_string_append(v_b_3723_, v___x_3732_);
lean_dec_ref(v___x_3732_);
v___x_3734_ = ((size_t)1ULL);
v___x_3735_ = lean_usize_add(v_i_3722_, v___x_3734_);
v_i_3722_ = v___x_3735_;
v_b_3723_ = v___x_3733_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg___boxed(lean_object* v_as_3737_, lean_object* v_sz_3738_, lean_object* v_i_3739_, lean_object* v_b_3740_, lean_object* v___y_3741_){
_start:
{
size_t v_sz_boxed_3742_; size_t v_i_boxed_3743_; lean_object* v_res_3744_; 
v_sz_boxed_3742_ = lean_unbox_usize(v_sz_3738_);
lean_dec(v_sz_3738_);
v_i_boxed_3743_ = lean_unbox_usize(v_i_3739_);
lean_dec(v_i_3739_);
v_res_3744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v_as_3737_, v_sz_boxed_3742_, v_i_boxed_3743_, v_b_3740_);
lean_dec_ref(v_as_3737_);
return v_res_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(uint8_t v___x_3746_, lean_object* v_stx_3747_, uint8_t v___x_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_){
_start:
{
if (v___x_3746_ == 0)
{
lean_object* v___x_3756_; 
lean_dec(v_stx_3747_);
v___x_3756_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3756_;
}
else
{
lean_object* v_fileName_3757_; lean_object* v_fileMap_3758_; lean_object* v_options_3759_; lean_object* v_currRecDepth_3760_; lean_object* v_maxRecDepth_3761_; lean_object* v_ref_3762_; lean_object* v_currNamespace_3763_; lean_object* v_openDecls_3764_; lean_object* v_initHeartbeats_3765_; lean_object* v_quotContext_3766_; lean_object* v_currMacroScope_3767_; uint8_t v_diag_3768_; lean_object* v_cancelTk_x3f_3769_; uint8_t v_suppressElabErrors_3770_; lean_object* v_inheritedTraceOptions_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; size_t v_sz_3775_; size_t v___x_3776_; lean_object* v___x_3777_; 
v_fileName_3757_ = lean_ctor_get(v___y_3753_, 0);
v_fileMap_3758_ = lean_ctor_get(v___y_3753_, 1);
v_options_3759_ = lean_ctor_get(v___y_3753_, 2);
v_currRecDepth_3760_ = lean_ctor_get(v___y_3753_, 3);
v_maxRecDepth_3761_ = lean_ctor_get(v___y_3753_, 4);
v_ref_3762_ = lean_ctor_get(v___y_3753_, 5);
v_currNamespace_3763_ = lean_ctor_get(v___y_3753_, 6);
v_openDecls_3764_ = lean_ctor_get(v___y_3753_, 7);
v_initHeartbeats_3765_ = lean_ctor_get(v___y_3753_, 8);
v_quotContext_3766_ = lean_ctor_get(v___y_3753_, 10);
v_currMacroScope_3767_ = lean_ctor_get(v___y_3753_, 11);
v_diag_3768_ = lean_ctor_get_uint8(v___y_3753_, sizeof(void*)*14);
v_cancelTk_x3f_3769_ = lean_ctor_get(v___y_3753_, 12);
v_suppressElabErrors_3770_ = lean_ctor_get_uint8(v___y_3753_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3771_ = lean_ctor_get(v___y_3753_, 13);
v___x_3772_ = lean_unsigned_to_nat(2u);
v___x_3773_ = l_Lean_Syntax_getArg(v_stx_3747_, v___x_3772_);
v___x_3774_ = l_Lean_Syntax_getArgs(v___x_3773_);
lean_dec(v___x_3773_);
v_sz_3775_ = lean_array_size(v___x_3774_);
v___x_3776_ = ((size_t)0ULL);
v___x_3777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__1(v_sz_3775_, v___x_3776_, v___x_3774_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v___x_3778_; 
lean_dec(v_stx_3747_);
v___x_3778_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3778_;
}
else
{
lean_object* v_val_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3981_; 
v_val_3779_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3781_ = v___x_3777_;
v_isShared_3782_ = v_isSharedCheck_3981_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_val_3779_);
lean_dec(v___x_3777_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3981_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3783_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; uint8_t v___y_3884_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v_m_x3f_3914_; lean_object* v_ids_x3f_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; lean_object* v___y_3920_; lean_object* v___y_3921_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v_m_x3f_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; uint8_t v___x_3970_; 
v___x_3783_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_inheritedTraceOptions_3771_);
lean_inc(v_cancelTk_x3f_3769_);
lean_inc(v_currMacroScope_3767_);
lean_inc(v_quotContext_3766_);
lean_inc(v_initHeartbeats_3765_);
lean_inc(v_openDecls_3764_);
lean_inc(v_currNamespace_3763_);
lean_inc(v_ref_3762_);
lean_inc(v_maxRecDepth_3761_);
lean_inc(v_currRecDepth_3760_);
lean_inc_ref(v_options_3759_);
lean_inc_ref(v_fileMap_3758_);
lean_inc_ref(v_fileName_3757_);
v___x_3873_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3873_, 0, v_fileName_3757_);
lean_ctor_set(v___x_3873_, 1, v_fileMap_3758_);
lean_ctor_set(v___x_3873_, 2, v_options_3759_);
lean_ctor_set(v___x_3873_, 3, v_currRecDepth_3760_);
lean_ctor_set(v___x_3873_, 4, v_maxRecDepth_3761_);
lean_ctor_set(v___x_3873_, 5, v_ref_3762_);
lean_ctor_set(v___x_3873_, 6, v_currNamespace_3763_);
lean_ctor_set(v___x_3873_, 7, v_openDecls_3764_);
lean_ctor_set(v___x_3873_, 8, v_initHeartbeats_3765_);
lean_ctor_set(v___x_3873_, 9, v___x_3783_);
lean_ctor_set(v___x_3873_, 10, v_quotContext_3766_);
lean_ctor_set(v___x_3873_, 11, v_currMacroScope_3767_);
lean_ctor_set(v___x_3873_, 12, v_cancelTk_x3f_3769_);
lean_ctor_set(v___x_3873_, 13, v_inheritedTraceOptions_3771_);
lean_ctor_set_uint8(v___x_3873_, sizeof(void*)*14, v_diag_3768_);
lean_ctor_set_uint8(v___x_3873_, sizeof(void*)*14 + 1, v_suppressElabErrors_3770_);
v___x_3874_ = lean_unsigned_to_nat(1u);
v___x_3954_ = lean_unsigned_to_nat(3u);
v___x_3955_ = l_Lean_Syntax_getArg(v_stx_3747_, v___x_3954_);
v___x_3970_ = l_Lean_Syntax_isNone(v___x_3955_);
if (v___x_3970_ == 0)
{
uint8_t v___x_3971_; 
lean_inc(v___x_3955_);
v___x_3971_ = l_Lean_Syntax_matchesNull(v___x_3955_, v___x_3954_);
if (v___x_3971_ == 0)
{
lean_object* v___x_3972_; 
lean_dec(v___x_3955_);
lean_dec_ref(v___x_3873_);
lean_del_object(v___x_3781_);
lean_dec(v_val_3779_);
lean_dec(v_stx_3747_);
v___x_3972_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3972_;
}
else
{
lean_object* v___x_3973_; uint8_t v___x_3974_; 
v___x_3973_ = l_Lean_Syntax_getArg(v___x_3955_, v___x_3874_);
v___x_3974_ = l_Lean_Syntax_isNone(v___x_3973_);
if (v___x_3974_ == 0)
{
uint8_t v___x_3975_; 
lean_inc(v___x_3973_);
v___x_3975_ = l_Lean_Syntax_matchesNull(v___x_3973_, v___x_3874_);
if (v___x_3975_ == 0)
{
lean_object* v___x_3976_; 
lean_dec(v___x_3973_);
lean_dec(v___x_3955_);
lean_dec_ref(v___x_3873_);
lean_del_object(v___x_3781_);
lean_dec(v_val_3779_);
lean_dec(v_stx_3747_);
v___x_3976_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect_spec__0___redArg();
return v___x_3976_;
}
else
{
lean_object* v_m_x3f_3977_; lean_object* v___x_3978_; 
v_m_x3f_3977_ = l_Lean_Syntax_getArg(v___x_3973_, v___x_3783_);
lean_dec(v___x_3973_);
v___x_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3978_, 0, v_m_x3f_3977_);
v_m_x3f_3957_ = v___x_3978_;
v___y_3958_ = v___y_3749_;
v___y_3959_ = v___y_3750_;
v___y_3960_ = v___y_3751_;
v___y_3961_ = v___y_3752_;
v___y_3962_ = v___x_3873_;
v___y_3963_ = v___y_3754_;
goto v___jp_3956_;
}
}
else
{
lean_object* v___x_3979_; 
lean_dec(v___x_3973_);
v___x_3979_ = lean_box(0);
v_m_x3f_3957_ = v___x_3979_;
v___y_3958_ = v___y_3749_;
v___y_3959_ = v___y_3750_;
v___y_3960_ = v___y_3751_;
v___y_3961_ = v___y_3752_;
v___y_3962_ = v___x_3873_;
v___y_3963_ = v___y_3754_;
goto v___jp_3956_;
}
}
}
else
{
lean_object* v___x_3980_; 
lean_dec(v___x_3955_);
lean_del_object(v___x_3781_);
v___x_3980_ = lean_box(0);
v_m_x3f_3914_ = v___x_3980_;
v_ids_x3f_3915_ = v___x_3980_;
v___y_3916_ = v___y_3749_;
v___y_3917_ = v___y_3750_;
v___y_3918_ = v___y_3751_;
v___y_3919_ = v___y_3752_;
v___y_3920_ = v___x_3873_;
v___y_3921_ = v___y_3754_;
goto v___jp_3913_;
}
v___jp_3784_:
{
lean_object* v___x_3793_; size_t v_sz_3794_; lean_object* v___x_3795_; 
v___x_3793_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg___closed__0));
v_sz_3794_ = lean_array_size(v___y_3792_);
v___x_3795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__1(v___y_3787_, v___y_3792_, v_sz_3794_, v___x_3776_, v___x_3793_, v___y_3789_, v___y_3788_, v___y_3791_, v___y_3785_, v___y_3786_, v___y_3790_);
lean_dec_ref(v___y_3792_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3838_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3798_ = v___x_3795_;
v_isShared_3799_ = v_isSharedCheck_3838_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3795_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3838_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3800_; uint8_t v___x_3801_; 
v___x_3800_ = lean_array_get_size(v_a_3796_);
v___x_3801_ = lean_nat_dec_eq(v___x_3800_, v___x_3783_);
if (v___x_3801_ == 0)
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
lean_del_object(v___x_3798_);
v___x_3802_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintInspect___lam__0___closed__5));
lean_inc(v_stx_3747_);
v___x_3803_ = l_Lean_PrettyPrinter_ppCategory(v___x_3802_, v_stx_3747_, v___y_3786_, v___y_3790_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; size_t v_sz_3809_; lean_object* v___x_3810_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref(v___x_3803_);
v___x_3805_ = l_Std_Format_defWidth;
v___x_3806_ = l_Std_Format_pretty(v_a_3804_, v___x_3805_, v___x_3783_, v___x_3783_);
v___x_3807_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_analyzeEMatchTheorem___closed__2));
v___x_3808_ = lean_string_append(v___x_3806_, v___x_3807_);
v_sz_3809_ = lean_array_size(v_a_3796_);
v___x_3810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v_a_3796_, v_sz_3809_, v___x_3776_, v___x_3808_);
lean_dec(v_a_3796_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; lean_object* v___x_3817_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3811_);
lean_dec_ref(v___x_3810_);
v___x_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3812_, 0, v_a_3811_);
v___x_3813_ = lean_box(0);
v___x_3814_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
lean_ctor_set(v___x_3814_, 2, v___x_3813_);
lean_ctor_set(v___x_3814_, 3, v___x_3813_);
lean_ctor_set(v___x_3814_, 4, v___x_3813_);
lean_ctor_set(v___x_3814_, 5, v___x_3813_);
v___x_3815_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___closed__0));
v___x_3816_ = 4;
v___x_3817_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(v_stx_3747_, v___x_3814_, v___x_3813_, v___x_3815_, v___x_3813_, v___x_3816_, v___y_3786_, v___y_3790_);
lean_dec_ref(v___y_3786_);
return v___x_3817_;
}
else
{
lean_object* v_a_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3825_; 
lean_dec_ref(v___y_3786_);
lean_dec(v_stx_3747_);
v_a_3818_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3820_ = v___x_3810_;
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
else
{
lean_inc(v_a_3818_);
lean_dec(v___x_3810_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3825_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v___x_3823_; 
if (v_isShared_3821_ == 0)
{
v___x_3823_ = v___x_3820_;
goto v_reusejp_3822_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v_a_3818_);
v___x_3823_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3822_;
}
v_reusejp_3822_:
{
return v___x_3823_;
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec(v_a_3796_);
lean_dec_ref(v___y_3786_);
lean_dec(v_stx_3747_);
v_a_3826_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3803_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3803_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3836_; 
lean_dec(v_a_3796_);
lean_dec_ref(v___y_3786_);
lean_dec(v_stx_3747_);
v___x_3834_ = lean_box(0);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 0, v___x_3834_);
v___x_3836_ = v___x_3798_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_3846_; 
lean_dec_ref(v___y_3786_);
lean_dec(v_stx_3747_);
v_a_3839_ = lean_ctor_get(v___x_3795_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3795_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3841_ = v___x_3795_;
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_a_3839_);
lean_dec(v___x_3795_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_3846_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v___x_3844_; 
if (v_isShared_3842_ == 0)
{
v___x_3844_ = v___x_3841_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v_a_3839_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
v___jp_3847_:
{
lean_object* v___x_3859_; 
v___x_3859_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v___y_3849_, v___y_3855_, v___y_3852_, v___y_3858_);
lean_dec(v___y_3858_);
lean_dec(v___y_3849_);
v___y_3785_ = v___y_3848_;
v___y_3786_ = v___y_3850_;
v___y_3787_ = v___y_3851_;
v___y_3788_ = v___y_3853_;
v___y_3789_ = v___y_3854_;
v___y_3790_ = v___y_3857_;
v___y_3791_ = v___y_3856_;
v___y_3792_ = v___x_3859_;
goto v___jp_3784_;
}
v___jp_3860_:
{
uint8_t v___x_3872_; 
v___x_3872_ = lean_nat_dec_le(v___y_3871_, v___y_3862_);
if (v___x_3872_ == 0)
{
lean_dec(v___y_3862_);
lean_inc(v___y_3871_);
v___y_3848_ = v___y_3861_;
v___y_3849_ = v___y_3863_;
v___y_3850_ = v___y_3864_;
v___y_3851_ = v___y_3865_;
v___y_3852_ = v___y_3871_;
v___y_3853_ = v___y_3866_;
v___y_3854_ = v___y_3867_;
v___y_3855_ = v___y_3868_;
v___y_3856_ = v___y_3870_;
v___y_3857_ = v___y_3869_;
v___y_3858_ = v___y_3871_;
goto v___jp_3847_;
}
else
{
v___y_3848_ = v___y_3861_;
v___y_3849_ = v___y_3863_;
v___y_3850_ = v___y_3864_;
v___y_3851_ = v___y_3865_;
v___y_3852_ = v___y_3871_;
v___y_3853_ = v___y_3866_;
v___y_3854_ = v___y_3867_;
v___y_3855_ = v___y_3868_;
v___y_3856_ = v___y_3870_;
v___y_3857_ = v___y_3869_;
v___y_3858_ = v___y_3862_;
goto v___jp_3847_;
}
}
v___jp_3875_:
{
lean_object* v___x_3885_; 
v___x_3885_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_getTheorems___redArg(v___y_3881_, v___y_3884_, v___y_3883_);
lean_dec(v___y_3881_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref(v___x_3885_);
v___x_3887_ = lean_array_mk(v_a_3886_);
v___x_3888_ = lean_array_get_size(v___x_3887_);
v___x_3889_ = lean_nat_dec_eq(v___x_3888_, v___x_3783_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3890_ = lean_nat_sub(v___x_3888_, v___x_3874_);
v___x_3891_ = lean_nat_dec_le(v___x_3783_, v___x_3890_);
if (v___x_3891_ == 0)
{
lean_inc(v___x_3890_);
v___y_3861_ = v___y_3876_;
v___y_3862_ = v___x_3890_;
v___y_3863_ = v___x_3888_;
v___y_3864_ = v___y_3877_;
v___y_3865_ = v___y_3878_;
v___y_3866_ = v___y_3879_;
v___y_3867_ = v___y_3880_;
v___y_3868_ = v___x_3887_;
v___y_3869_ = v___y_3883_;
v___y_3870_ = v___y_3882_;
v___y_3871_ = v___x_3890_;
goto v___jp_3860_;
}
else
{
v___y_3861_ = v___y_3876_;
v___y_3862_ = v___x_3890_;
v___y_3863_ = v___x_3888_;
v___y_3864_ = v___y_3877_;
v___y_3865_ = v___y_3878_;
v___y_3866_ = v___y_3879_;
v___y_3867_ = v___y_3880_;
v___y_3868_ = v___x_3887_;
v___y_3869_ = v___y_3883_;
v___y_3870_ = v___y_3882_;
v___y_3871_ = v___x_3783_;
goto v___jp_3860_;
}
}
else
{
v___y_3785_ = v___y_3876_;
v___y_3786_ = v___y_3877_;
v___y_3787_ = v___y_3878_;
v___y_3788_ = v___y_3879_;
v___y_3789_ = v___y_3880_;
v___y_3790_ = v___y_3883_;
v___y_3791_ = v___y_3882_;
v___y_3792_ = v___x_3887_;
goto v___jp_3784_;
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec_ref(v___y_3878_);
lean_dec_ref(v___y_3877_);
lean_dec(v_stx_3747_);
v_a_3892_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3885_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3885_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
v___jp_3900_:
{
if (lean_obj_tag(v___y_3902_) == 1)
{
lean_object* v_val_3910_; 
v_val_3910_ = lean_ctor_get(v___y_3902_, 0);
lean_inc(v_val_3910_);
lean_dec_ref(v___y_3902_);
if (lean_obj_tag(v_val_3910_) == 1)
{
lean_dec_ref(v_val_3910_);
v___y_3876_ = v___y_3901_;
v___y_3877_ = v___y_3903_;
v___y_3878_ = v___y_3904_;
v___y_3879_ = v___y_3905_;
v___y_3880_ = v___y_3906_;
v___y_3881_ = v___y_3909_;
v___y_3882_ = v___y_3908_;
v___y_3883_ = v___y_3907_;
v___y_3884_ = v___x_3748_;
goto v___jp_3875_;
}
else
{
uint8_t v___x_3911_; 
lean_dec(v_val_3910_);
v___x_3911_ = 0;
v___y_3876_ = v___y_3901_;
v___y_3877_ = v___y_3903_;
v___y_3878_ = v___y_3904_;
v___y_3879_ = v___y_3905_;
v___y_3880_ = v___y_3906_;
v___y_3881_ = v___y_3909_;
v___y_3882_ = v___y_3908_;
v___y_3883_ = v___y_3907_;
v___y_3884_ = v___x_3911_;
goto v___jp_3875_;
}
}
else
{
uint8_t v___x_3912_; 
lean_dec(v___y_3902_);
v___x_3912_ = 0;
v___y_3876_ = v___y_3901_;
v___y_3877_ = v___y_3903_;
v___y_3878_ = v___y_3904_;
v___y_3879_ = v___y_3905_;
v___y_3880_ = v___y_3906_;
v___y_3881_ = v___y_3909_;
v___y_3882_ = v___y_3908_;
v___y_3883_ = v___y_3907_;
v___y_3884_ = v___x_3912_;
goto v___jp_3875_;
}
}
v___jp_3913_:
{
lean_object* v___x_3922_; 
v___x_3922_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkConfig(v_val_3779_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v_val_3779_);
if (lean_obj_tag(v___x_3922_) == 0)
{
lean_object* v_a_3923_; lean_object* v___x_3924_; 
v_a_3923_ = lean_ctor_get(v___x_3922_, 0);
lean_inc(v_a_3923_);
lean_dec_ref(v___x_3922_);
v___x_3924_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_mkParams(v_a_3923_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
if (lean_obj_tag(v___x_3924_) == 0)
{
if (lean_obj_tag(v_ids_x3f_3915_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3926_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref(v___x_3924_);
v___x_3926_ = lean_box(0);
v___y_3901_ = v___y_3919_;
v___y_3902_ = v_m_x3f_3914_;
v___y_3903_ = v___y_3920_;
v___y_3904_ = v_a_3925_;
v___y_3905_ = v___y_3917_;
v___y_3906_ = v___y_3916_;
v___y_3907_ = v___y_3921_;
v___y_3908_ = v___y_3918_;
v___y_3909_ = v___x_3926_;
goto v___jp_3900_;
}
else
{
lean_object* v_a_3927_; lean_object* v_val_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3937_; 
v_a_3927_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3927_);
lean_dec_ref(v___x_3924_);
v_val_3928_ = lean_ctor_get(v_ids_x3f_3915_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v_ids_x3f_3915_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3930_ = v_ids_x3f_3915_;
v_isShared_3931_ = v_isSharedCheck_3937_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_val_3928_);
lean_dec(v_ids_x3f_3915_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3937_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
size_t v_sz_3932_; lean_object* v___x_3933_; lean_object* v___x_3935_; 
v_sz_3932_ = lean_array_size(v_val_3928_);
v___x_3933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__4(v_sz_3932_, v___x_3776_, v_val_3928_);
if (v_isShared_3931_ == 0)
{
lean_ctor_set(v___x_3930_, 0, v___x_3933_);
v___x_3935_ = v___x_3930_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3933_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
v___y_3901_ = v___y_3919_;
v___y_3902_ = v_m_x3f_3914_;
v___y_3903_ = v___y_3920_;
v___y_3904_ = v_a_3927_;
v___y_3905_ = v___y_3917_;
v___y_3906_ = v___y_3916_;
v___y_3907_ = v___y_3921_;
v___y_3908_ = v___y_3918_;
v___y_3909_ = v___x_3935_;
goto v___jp_3900_;
}
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec_ref(v___y_3920_);
lean_dec(v_ids_x3f_3915_);
lean_dec(v_m_x3f_3914_);
lean_dec(v_stx_3747_);
v_a_3938_ = lean_ctor_get(v___x_3924_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3924_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3924_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3924_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_dec_ref(v___y_3920_);
lean_dec(v_ids_x3f_3915_);
lean_dec(v_m_x3f_3914_);
lean_dec(v_stx_3747_);
v_a_3946_ = lean_ctor_get(v___x_3922_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3922_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3922_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3922_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
v___jp_3956_:
{
lean_object* v___x_3964_; lean_object* v_ids_x3f_3965_; lean_object* v___x_3967_; 
v___x_3964_ = l_Lean_Syntax_getArg(v___x_3955_, v___x_3772_);
lean_dec(v___x_3955_);
v_ids_x3f_3965_ = l_Lean_Syntax_getArgs(v___x_3964_);
lean_dec(v___x_3964_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v_m_x3f_3957_);
v___x_3967_ = v___x_3781_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_m_x3f_3957_);
v___x_3967_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
lean_object* v___x_3968_; 
v___x_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3968_, 0, v_ids_x3f_3965_);
v_m_x3f_3914_ = v___x_3967_;
v_ids_x3f_3915_ = v___x_3968_;
v___y_3916_ = v___y_3958_;
v___y_3917_ = v___y_3959_;
v___y_3918_ = v___y_3960_;
v___y_3919_ = v___y_3961_;
v___y_3920_ = v___y_3962_;
v___y_3921_ = v___y_3963_;
goto v___jp_3913_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed(lean_object* v___x_3982_, lean_object* v_stx_3983_, lean_object* v___x_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
uint8_t v___x_11644__boxed_3992_; uint8_t v___x_11645__boxed_3993_; lean_object* v_res_3994_; 
v___x_11644__boxed_3992_ = lean_unbox(v___x_3982_);
v___x_11645__boxed_3993_ = lean_unbox(v___x_3984_);
v_res_3994_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0(v___x_11644__boxed_3992_, v_stx_3983_, v___x_11645__boxed_3993_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
lean_dec(v___y_3990_);
lean_dec_ref(v___y_3989_);
lean_dec(v___y_3988_);
lean_dec_ref(v___y_3987_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(lean_object* v_stx_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v___x_4004_; uint8_t v___x_4005_; uint8_t v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v___f_4009_; lean_object* v___x_4010_; 
v___x_4004_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1));
lean_inc(v_stx_4000_);
v___x_4005_ = l_Lean_Syntax_isOfKind(v_stx_4000_, v___x_4004_);
v___x_4006_ = 1;
v___x_4007_ = lean_box(v___x_4005_);
v___x_4008_ = lean_box(v___x_4006_);
v___f_4009_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4009_, 0, v___x_4007_);
lean_closure_set(v___f_4009_, 1, v_stx_4000_);
lean_closure_set(v___f_4009_, 2, v___x_4008_);
v___x_4010_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_4009_, v_a_4001_, v_a_4002_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed(lean_object* v_stx_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck(v_stx_4011_, v_a_4012_, v_a_4013_);
lean_dec(v_a_4013_);
lean_dec_ref(v_a_4012_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(lean_object* v_as_4016_, size_t v_sz_4017_, size_t v_i_4018_, lean_object* v_b_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___redArg(v_as_4016_, v_sz_4017_, v_i_4018_, v_b_4019_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2___boxed(lean_object* v_as_4028_, lean_object* v_sz_4029_, lean_object* v_i_4030_, lean_object* v_b_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
size_t v_sz_boxed_4039_; size_t v_i_boxed_4040_; lean_object* v_res_4041_; 
v_sz_boxed_4039_ = lean_unbox_usize(v_sz_4029_);
lean_dec(v_sz_4029_);
v_i_boxed_4040_ = lean_unbox_usize(v_i_4030_);
lean_dec(v_i_4030_);
v_res_4041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__2(v_as_4028_, v_sz_boxed_4039_, v_i_boxed_4040_, v_b_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
lean_dec(v___y_4037_);
lean_dec_ref(v___y_4036_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec_ref(v_as_4028_);
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(lean_object* v_n_4042_, lean_object* v_as_4043_, lean_object* v_lo_4044_, lean_object* v_hi_4045_, lean_object* v_w_4046_, lean_object* v_hlo_4047_, lean_object* v_hhi_4048_){
_start:
{
lean_object* v___x_4049_; 
v___x_4049_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___redArg(v_n_4042_, v_as_4043_, v_lo_4044_, v_hi_4045_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3___boxed(lean_object* v_n_4050_, lean_object* v_as_4051_, lean_object* v_lo_4052_, lean_object* v_hi_4053_, lean_object* v_w_4054_, lean_object* v_hlo_4055_, lean_object* v_hhi_4056_){
_start:
{
lean_object* v_res_4057_; 
v_res_4057_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3(v_n_4050_, v_as_4051_, v_lo_4052_, v_hi_4053_, v_w_4054_, v_hlo_4055_, v_hhi_4056_);
lean_dec(v_hi_4053_);
lean_dec(v_n_4050_);
return v_res_4057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(lean_object* v_n_4058_, lean_object* v_lo_4059_, lean_object* v_hi_4060_, lean_object* v_hhi_4061_, lean_object* v_pivot_4062_, lean_object* v_as_4063_, lean_object* v_i_4064_, lean_object* v_k_4065_, lean_object* v_ilo_4066_, lean_object* v_ik_4067_, lean_object* v_w_4068_){
_start:
{
lean_object* v___x_4069_; 
v___x_4069_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___redArg(v_hi_4060_, v_pivot_4062_, v_as_4063_, v_i_4064_, v_k_4065_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4___boxed(lean_object* v_n_4070_, lean_object* v_lo_4071_, lean_object* v_hi_4072_, lean_object* v_hhi_4073_, lean_object* v_pivot_4074_, lean_object* v_as_4075_, lean_object* v_i_4076_, lean_object* v_k_4077_, lean_object* v_ilo_4078_, lean_object* v_ik_4079_, lean_object* v_w_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__3_spec__4(v_n_4070_, v_lo_4071_, v_hi_4072_, v_hhi_4073_, v_pivot_4074_, v_as_4075_, v_i_4076_, v_k_4077_, v_ilo_4078_, v_ik_4079_, v_w_4080_);
lean_dec(v_pivot_4074_);
lean_dec(v_hi_4072_);
lean_dec(v_lo_4071_);
lean_dec(v_n_4070_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(lean_object* v_ref_4082_, lean_object* v_msgData_4083_, uint8_t v_severity_4084_, uint8_t v_isSilent_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v___x_4093_; 
v___x_4093_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___redArg(v_ref_4082_, v_msgData_4083_, v_severity_4084_, v_isSilent_4085_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_4094_, lean_object* v_msgData_4095_, lean_object* v_severity_4096_, lean_object* v_isSilent_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_){
_start:
{
uint8_t v_severity_boxed_4105_; uint8_t v_isSilent_boxed_4106_; lean_object* v_res_4107_; 
v_severity_boxed_4105_ = lean_unbox(v_severity_4096_);
v_isSilent_boxed_4106_ = lean_unbox(v_isSilent_4097_);
v_res_4107_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00__private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck_spec__0_spec__0_spec__1(v_ref_4094_, v_msgData_4095_, v_severity_boxed_4105_, v_isSilent_boxed_4106_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_);
lean_dec(v___y_4103_);
lean_dec_ref(v___y_4102_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v_ref_4094_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1(){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4113_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_4114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___closed__1));
v___x_4115_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___closed__1));
v___x_4116_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___boxed), 4, 0);
v___x_4117_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_4113_, v___x_4114_, v___x_4115_, v___x_4116_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1___boxed(lean_object* v_a_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck___regBuiltin___private_Lean_Elab_Tactic_Grind_Lint_0__Lean_Elab_Tactic_Grind_elabGrindLintCheck__1();
return v_res_4119_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Lint(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Config(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Lint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
