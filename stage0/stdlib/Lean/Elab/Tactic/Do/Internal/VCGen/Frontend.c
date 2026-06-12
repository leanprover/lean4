// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Frontend
// Imports: public import Lean.Elab.Tactic.Do.VCGen.SuggestInvariant public import Lean.Elab.Tactic.Do.VCGen public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.Driver public import Lean.Meta.Sym.Simp.Attr public import Lean.Meta.Sym.Simp.ControlFlow public import Lean.Meta.Sym.Simp.EvalGround public import Lean.Meta.Sym.Simp.Forall public import Lean.Meta.Sym.Simp.Rewrite public import Lean.Meta.Sym.Simp.Simproc public import Lean.Elab.Tactic.Grind.Main public import Lean.Elab.Tactic.Grind.Basic
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpArrowTelescope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simpControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_insert(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_Sym_Simp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_LocalContext_findFromUserName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkGrindParams(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabGrindConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_elabConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_mvcgen_warning;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkGoalCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_GrindM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_elabInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_processHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mvcgen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 186, 72, 71, 180, 239, 13, 70)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5(lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpErase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 24, 229, 171, 59, 186, 144, 157)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__5_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpStar"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__7_value),LEAN_SCALAR_PTR_LITERAL(125, 38, 251, 225, 228, 173, 11, 37)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Could not resolve spec theorem `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__11_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "SPred"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "entails_cons_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__4_value),LEAN_SCALAR_PTR_LITERAL(121, 192, 217, 126, 138, 217, 120, 234)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "entails_nil_pure_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__6_value),LEAN_SCALAR_PTR_LITERAL(77, 71, 95, 197, 218, 24, 130, 149)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "entails_nil_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__8_value),LEAN_SCALAR_PTR_LITERAL(209, 42, 38, 114, 220, 245, 181, 209)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "apply_pure_cons_entails_l"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__10_value),LEAN_SCALAR_PTR_LITERAL(88, 114, 58, 244, 248, 249, 100, 189)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "apply_pure_cons_entails_r"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__12_value),LEAN_SCALAR_PTR_LITERAL(36, 125, 0, 206, 159, 122, 18, 62)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "down_pure_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__14_value),LEAN_SCALAR_PTR_LITERAL(242, 230, 134, 253, 236, 36, 160, 34)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "pure_elim'"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__16_value),LEAN_SCALAR_PTR_LITERAL(146, 100, 201, 175, 219, 207, 33, 227)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "pure_intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__18_value),LEAN_SCALAR_PTR_LITERAL(212, 52, 84, 252, 44, 75, 13, 225)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PostCond"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entails"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__20_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21_value),LEAN_SCALAR_PTR_LITERAL(32, 111, 255, 27, 103, 9, 244, 9)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22_value),LEAN_SCALAR_PTR_LITERAL(106, 198, 3, 218, 176, 38, 40, 252)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__20_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21_value),LEAN_SCALAR_PTR_LITERAL(32, 111, 255, 27, 103, 9, 244, 9)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24_value),LEAN_SCALAR_PTR_LITERAL(152, 24, 212, 180, 51, 184, 242, 134)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ExceptConds"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21_value),LEAN_SCALAR_PTR_LITERAL(72, 205, 41, 157, 129, 142, 231, 99)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22_value),LEAN_SCALAR_PTR_LITERAL(114, 214, 92, 55, 221, 19, 3, 63)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "pure"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21_value),LEAN_SCALAR_PTR_LITERAL(72, 205, 41, 157, 129, 142, 231, 99)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__28_value),LEAN_SCALAR_PTR_LITERAL(177, 127, 46, 135, 84, 167, 103, 90)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "entails_false"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__30_value),LEAN_SCALAR_PTR_LITERAL(130, 197, 58, 234, 180, 192, 166, 113)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "entails_true"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__32 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__32_value),LEAN_SCALAR_PTR_LITERAL(246, 50, 98, 188, 214, 243, 38, 248)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__34 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__34_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "of_entails_wp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__35 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__35_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__36_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__36_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__36_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__36_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__36_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__34_value),LEAN_SCALAR_PTR_LITERAL(31, 48, 165, 224, 255, 99, 7, 166)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__36_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__35_value),LEAN_SCALAR_PTR_LITERAL(191, 31, 210, 183, 145, 91, 10, 79)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__36 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__36_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__37 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__37_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__38 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__37_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__38_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__39 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__39_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__40;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__42 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__42_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__43 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__43_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__44_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__44_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__44_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__44_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__43_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__44 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__44_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__45 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__45_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__45_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__47 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__47_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__47_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__48 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__48_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__49 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__49_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__50_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__50_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__50_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__50_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__50_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__50_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__49_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__50 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__50_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__51 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__51_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__52_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__52_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__52_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__51_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__52 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__52_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__53 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__53_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unfoldPartialApp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__54 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__54_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__55;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__54_value),LEAN_SCALAR_PTR_LITERAL(49, 203, 120, 209, 69, 128, 204, 215)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__56 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__56_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "negConfigItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__57 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__57_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__58_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__58_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__58_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__57_value),LEAN_SCALAR_PTR_LITERAL(196, 29, 29, 161, 247, 206, 181, 221)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__58 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__58_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__59 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__59_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__60 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__60_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__61;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__60_value),LEAN_SCALAR_PTR_LITERAL(56, 247, 87, 81, 188, 35, 250, 148)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__62 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__62_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__63_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__63;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__64 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__64_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__65 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__65_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__66 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__66_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_SpecAttr_getSpecSimpTheorems___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__67 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__67_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__68_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__68;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__69;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__70;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__71;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__72_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__72;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__73_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__73;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "mvcgen': the `leave` config option is currently ignored."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__1_value),LEAN_SCALAR_PTR_LITERAL(150, 98, 0, 78, 28, 79, 28, 100)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__3_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSeq"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__4_value),LEAN_SCALAR_PTR_LITERAL(158, 229, 98, 59, 247, 194, 34, 174)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_simp___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__0_value;
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__1___boxed, .m_arity = 12, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__0_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__3;
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__4_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 153, .m_capacity = 153, .m_length = 148, .m_data = "named Sym.simp variants are not yet supported in `mvcgen'`; use `mvcgen' simplifying_assumptions [thm₁, thm₂, ...]` with the default variant instead"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__5_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*13 + 32, .m_other = 13, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1)),((lean_object*)(((size_t)(5) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(8) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)(((size_t)(1000) << 1) | 1)),((lean_object*)(((size_t)(1048576) << 1) | 1)),((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 1, 0, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 1, 1, 0, 1, 1)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inv"};
static const lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__0 = (const lean_object*)&l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Could not parse invariant label; expected `inv<n>`."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__0_value)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__1_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__2;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Duplicate invariant alternative for `inv"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__5_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invariantDotAlt"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 218, 225, 197, 89, 244, 133, 64)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invariantCaseAlt"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(163, 146, 32, 128, 83, 151, 179, 6)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Expected `invariantDotAlt` or `invariantCaseAlt`."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Alternation between labelled and bulleted invariants is not supported."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__12_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invariantAlts"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 41, 254, 250, 50, 69, 99, 10)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invariantsKW"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__4_value),LEAN_SCALAR_PTR_LITERAL(113, 87, 251, 76, 123, 116, 93, 232)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "token"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__6_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invariants\? "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__7_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__6_value),LEAN_SCALAR_PTR_LITERAL(89, 149, 26, 37, 31, 104, 89, 130)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__8_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__7_value),LEAN_SCALAR_PTR_LITERAL(241, 40, 134, 186, 103, 193, 43, 220)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Invariant alternative `inv"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "` does not match any invariant goal."};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 1, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 145, .m_capacity = 145, .m_length = 144, .m_data = "The `mvcgen'` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it. Avoid using it in production projects."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__1_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "pre-tactic failed on at least one VC; see errors above"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__1;
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 78, .m_data = "`mvcgen' invariants\?` (suggest mode) is not supported inside `sym => …` blocks"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "mvcgen'"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__3_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 164, 188, 44, 114, 250, 122, 123)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__3_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__4_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__5_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__6_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(89, 242, 56, 182, 153, 42, 114, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(132, 236, 244, 1, 128, 181, 211, 156)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "VCGen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(175, 167, 22, 210, 240, 170, 245, 185)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Frontend"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(18, 209, 67, 183, 120, 233, 44, 242)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__13_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__13_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(147, 197, 196, 233, 158, 77, 49, 202)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__14_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 108, 164, 213, 221, 37, 180, 229)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__15_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 84, 138, 219, 247, 214, 26, 16)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__16_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(73, 168, 135, 192, 193, 202, 29, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__17_value),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(109, 141, 169, 199, 171, 247, 59, 245)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__18_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(64, 59, 250, 17, 189, 47, 163, 133)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__19_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "evalSymMVCGen'"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__19_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(19, 92, 242, 121, 57, 23, 92, 131)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 41, .m_data = "`mvcgen'` step inside `sym => …` blocks. "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_docString__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__0_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__0_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__0_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(172, 206, 51, 98, 251, 95, 173, 15)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabMVCGen'"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(232, 135, 166, 206, 84, 210, 155, 104)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(207, 201, 16, 251, 167, 255, 54, 189)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Tactic-level `mvcgen'`. "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_docString__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg(lean_object* v_x_7_, lean_object* v_goals_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_16_ = lean_st_mk_ref(v_goals_8_);
v___x_17_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___closed__2));
lean_inc(v_a_14_);
lean_inc_ref(v_a_13_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v___x_16_);
v___x_18_ = lean_apply_9(v_x_7_, v___x_17_, v___x_16_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, lean_box(0));
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_27_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_27_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_27_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = lean_st_ref_get(v___x_16_);
lean_dec(v___x_16_);
lean_dec(v___x_23_);
if (v_isShared_22_ == 0)
{
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v_a_19_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
return v___x_25_;
}
}
}
else
{
lean_dec(v___x_16_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg___boxed(lean_object* v_x_28_, lean_object* v_goals_29_, lean_object* v_a_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg(v_x_28_, v_goals_29_, v_a_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec(v_a_31_);
lean_dec_ref(v_a_30_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM(lean_object* v_00_u03b1_38_, lean_object* v_x_39_, lean_object* v_goals_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg(v_x_39_, v_goals_40_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___boxed(lean_object* v_00_u03b1_49_, lean_object* v_x_50_, lean_object* v_goals_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM(v_00_u03b1_49_, v_x_50_, v_goals_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
return v_res_59_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_62_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg(){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___closed__0);
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___boxed(lean_object* v___y_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0(lean_object* v_00_u03b1_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___boxed(lean_object* v_00_u03b1_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0(v_00_u03b1_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
return v_res_85_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_86_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__1(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__0);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5(lean_object* v_00_u03b2_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5___closed__1);
return v___x_90_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__0(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_91_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__1(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__0);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6(lean_object* v_00_u03b2_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6___closed__1);
return v___x_95_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_96_ = lean_box(1);
v___x_97_ = l_Lean_MessageData_ofFormat(v___x_96_);
return v___x_97_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__2));
v___x_102_ = l_Lean_MessageData_ofFormat(v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6(lean_object* v_x_103_, lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
return v_x_103_;
}
else
{
lean_object* v_head_105_; lean_object* v_tail_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_128_; 
v_head_105_ = lean_ctor_get(v_x_104_, 0);
v_tail_106_ = lean_ctor_get(v_x_104_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_104_);
if (v_isSharedCheck_128_ == 0)
{
v___x_108_ = v_x_104_;
v_isShared_109_ = v_isSharedCheck_128_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_tail_106_);
lean_inc(v_head_105_);
lean_dec(v_x_104_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_128_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v_before_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_126_; 
v_before_110_ = lean_ctor_get(v_head_105_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v_head_105_);
if (v_isSharedCheck_126_ == 0)
{
lean_object* v_unused_127_; 
v_unused_127_ = lean_ctor_get(v_head_105_, 1);
lean_dec(v_unused_127_);
v___x_112_ = v_head_105_;
v_isShared_113_ = v_isSharedCheck_126_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_before_110_);
lean_dec(v_head_105_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_126_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 7);
lean_ctor_set(v___x_112_, 1, v___x_114_);
lean_ctor_set(v___x_112_, 0, v_x_103_);
v___x_116_ = v___x_112_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_x_103_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_114_);
v___x_116_ = v_reuseFailAlloc_125_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_117_; lean_object* v___x_119_; 
v___x_117_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__3);
if (v_isShared_109_ == 0)
{
lean_ctor_set_tag(v___x_108_, 7);
lean_ctor_set(v___x_108_, 1, v___x_117_);
lean_ctor_set(v___x_108_, 0, v___x_116_);
v___x_119_ = v___x_108_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_117_);
v___x_119_ = v_reuseFailAlloc_124_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = l_Lean_MessageData_ofSyntax(v_before_110_);
v___x_121_ = l_Lean_indentD(v___x_120_);
v___x_122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_119_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
v_x_103_ = v___x_122_;
v_x_104_ = v_tail_106_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(lean_object* v_opts_129_, lean_object* v_opt_130_){
_start:
{
lean_object* v_name_131_; lean_object* v_defValue_132_; lean_object* v_map_133_; lean_object* v___x_134_; 
v_name_131_ = lean_ctor_get(v_opt_130_, 0);
v_defValue_132_ = lean_ctor_get(v_opt_130_, 1);
v_map_133_ = lean_ctor_get(v_opts_129_, 0);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_133_, v_name_131_);
if (lean_obj_tag(v___x_134_) == 0)
{
uint8_t v___x_135_; 
v___x_135_ = lean_unbox(v_defValue_132_);
return v___x_135_;
}
else
{
lean_object* v_val_136_; 
v_val_136_ = lean_ctor_get(v___x_134_, 0);
lean_inc(v_val_136_);
lean_dec_ref_known(v___x_134_, 1);
if (lean_obj_tag(v_val_136_) == 1)
{
uint8_t v_v_137_; 
v_v_137_ = lean_ctor_get_uint8(v_val_136_, 0);
lean_dec_ref_known(v_val_136_, 0);
return v_v_137_;
}
else
{
uint8_t v___x_138_; 
lean_dec(v_val_136_);
v___x_138_ = lean_unbox(v_defValue_132_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5___boxed(lean_object* v_opts_139_, lean_object* v_opt_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_opts_139_, v_opt_140_);
lean_dec_ref(v_opt_140_);
lean_dec_ref(v_opts_139_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__1));
v___x_147_ = l_Lean_MessageData_ofFormat(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg(lean_object* v_msgData_148_, lean_object* v_macroStack_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_options_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_options_152_ = lean_ctor_get(v___y_150_, 2);
v___x_153_ = l_Lean_Elab_pp_macroStack;
v___x_154_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_options_152_, v___x_153_);
if (v___x_154_ == 0)
{
lean_object* v___x_155_; 
lean_dec(v_macroStack_149_);
v___x_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_155_, 0, v_msgData_148_);
return v___x_155_;
}
else
{
if (lean_obj_tag(v_macroStack_149_) == 0)
{
lean_object* v___x_156_; 
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v_msgData_148_);
return v___x_156_;
}
else
{
lean_object* v_head_157_; lean_object* v_after_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_173_; 
v_head_157_ = lean_ctor_get(v_macroStack_149_, 0);
lean_inc(v_head_157_);
v_after_158_ = lean_ctor_get(v_head_157_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_head_157_);
if (v_isSharedCheck_173_ == 0)
{
lean_object* v_unused_174_; 
v_unused_174_ = lean_ctor_get(v_head_157_, 0);
lean_dec(v_unused_174_);
v___x_160_ = v_head_157_;
v_isShared_161_ = v_isSharedCheck_173_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_after_158_);
lean_dec(v_head_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_173_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0);
if (v_isShared_161_ == 0)
{
lean_ctor_set_tag(v___x_160_, 7);
lean_ctor_set(v___x_160_, 1, v___x_162_);
lean_ctor_set(v___x_160_, 0, v_msgData_148_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_msgData_148_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v___x_162_);
v___x_164_ = v_reuseFailAlloc_172_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_msgData_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_165_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__2);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = l_Lean_MessageData_ofSyntax(v_after_158_);
v___x_168_ = l_Lean_indentD(v___x_167_);
v_msgData_169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_169_, 0, v___x_166_);
lean_ctor_set(v_msgData_169_, 1, v___x_168_);
v___x_170_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6(v_msgData_169_, v_macroStack_149_);
v___x_171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
return v___x_171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_175_, lean_object* v_macroStack_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg(v_msgData_175_, v_macroStack_176_, v___y_177_);
lean_dec_ref(v___y_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(lean_object* v_msgData_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_, lean_object* v___y_184_){
_start:
{
lean_object* v___x_186_; lean_object* v_env_187_; lean_object* v___x_188_; lean_object* v_mctx_189_; lean_object* v_lctx_190_; lean_object* v_options_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_186_ = lean_st_ref_get(v___y_184_);
v_env_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc_ref(v_env_187_);
lean_dec(v___x_186_);
v___x_188_ = lean_st_ref_get(v___y_182_);
v_mctx_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc_ref(v_mctx_189_);
lean_dec(v___x_188_);
v_lctx_190_ = lean_ctor_get(v___y_181_, 2);
v_options_191_ = lean_ctor_get(v___y_183_, 2);
lean_inc_ref(v_options_191_);
lean_inc_ref(v_lctx_190_);
v___x_192_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_192_, 0, v_env_187_);
lean_ctor_set(v___x_192_, 1, v_mctx_189_);
lean_ctor_set(v___x_192_, 2, v_lctx_190_);
lean_ctor_set(v___x_192_, 3, v_options_191_);
v___x_193_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_msgData_180_);
v___x_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1___boxed(lean_object* v_msgData_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v_msgData_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_);
lean_dec(v___y_199_);
lean_dec_ref(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(lean_object* v_msg_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_ref_210_; lean_object* v___x_211_; lean_object* v_a_212_; lean_object* v_macroStack_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_224_; 
v_ref_210_ = lean_ctor_get(v___y_207_, 5);
v___x_211_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v_msg_202_, v___y_205_, v___y_206_, v___y_207_, v___y_208_);
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref(v___x_211_);
v_macroStack_213_ = lean_ctor_get(v___y_203_, 1);
v___x_214_ = l_Lean_Elab_getBetterRef(v_ref_210_, v_macroStack_213_);
lean_inc(v_macroStack_213_);
v___x_215_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg(v_a_212_, v_macroStack_213_, v___y_207_);
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_224_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_224_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_214_);
lean_ctor_set(v___x_220_, 1, v_a_216_);
if (v_isShared_219_ == 0)
{
lean_ctor_set_tag(v___x_218_, 1);
lean_ctor_set(v___x_218_, 0, v___x_220_);
v___x_222_ = v___x_218_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v___x_220_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg___boxed(lean_object* v_msg_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(v_msg_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(lean_object* v_ref_234_, lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_fileName_243_; lean_object* v_fileMap_244_; lean_object* v_options_245_; lean_object* v_currRecDepth_246_; lean_object* v_maxRecDepth_247_; lean_object* v_ref_248_; lean_object* v_currNamespace_249_; lean_object* v_openDecls_250_; lean_object* v_initHeartbeats_251_; lean_object* v_maxHeartbeats_252_; lean_object* v_quotContext_253_; lean_object* v_currMacroScope_254_; uint8_t v_diag_255_; lean_object* v_cancelTk_x3f_256_; uint8_t v_suppressElabErrors_257_; lean_object* v_inheritedTraceOptions_258_; lean_object* v_ref_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_fileName_243_ = lean_ctor_get(v___y_240_, 0);
v_fileMap_244_ = lean_ctor_get(v___y_240_, 1);
v_options_245_ = lean_ctor_get(v___y_240_, 2);
v_currRecDepth_246_ = lean_ctor_get(v___y_240_, 3);
v_maxRecDepth_247_ = lean_ctor_get(v___y_240_, 4);
v_ref_248_ = lean_ctor_get(v___y_240_, 5);
v_currNamespace_249_ = lean_ctor_get(v___y_240_, 6);
v_openDecls_250_ = lean_ctor_get(v___y_240_, 7);
v_initHeartbeats_251_ = lean_ctor_get(v___y_240_, 8);
v_maxHeartbeats_252_ = lean_ctor_get(v___y_240_, 9);
v_quotContext_253_ = lean_ctor_get(v___y_240_, 10);
v_currMacroScope_254_ = lean_ctor_get(v___y_240_, 11);
v_diag_255_ = lean_ctor_get_uint8(v___y_240_, sizeof(void*)*14);
v_cancelTk_x3f_256_ = lean_ctor_get(v___y_240_, 12);
v_suppressElabErrors_257_ = lean_ctor_get_uint8(v___y_240_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_258_ = lean_ctor_get(v___y_240_, 13);
v_ref_259_ = l_Lean_replaceRef(v_ref_234_, v_ref_248_);
lean_inc_ref(v_inheritedTraceOptions_258_);
lean_inc(v_cancelTk_x3f_256_);
lean_inc(v_currMacroScope_254_);
lean_inc(v_quotContext_253_);
lean_inc(v_maxHeartbeats_252_);
lean_inc(v_initHeartbeats_251_);
lean_inc(v_openDecls_250_);
lean_inc(v_currNamespace_249_);
lean_inc(v_maxRecDepth_247_);
lean_inc(v_currRecDepth_246_);
lean_inc_ref(v_options_245_);
lean_inc_ref(v_fileMap_244_);
lean_inc_ref(v_fileName_243_);
v___x_260_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_260_, 0, v_fileName_243_);
lean_ctor_set(v___x_260_, 1, v_fileMap_244_);
lean_ctor_set(v___x_260_, 2, v_options_245_);
lean_ctor_set(v___x_260_, 3, v_currRecDepth_246_);
lean_ctor_set(v___x_260_, 4, v_maxRecDepth_247_);
lean_ctor_set(v___x_260_, 5, v_ref_259_);
lean_ctor_set(v___x_260_, 6, v_currNamespace_249_);
lean_ctor_set(v___x_260_, 7, v_openDecls_250_);
lean_ctor_set(v___x_260_, 8, v_initHeartbeats_251_);
lean_ctor_set(v___x_260_, 9, v_maxHeartbeats_252_);
lean_ctor_set(v___x_260_, 10, v_quotContext_253_);
lean_ctor_set(v___x_260_, 11, v_currMacroScope_254_);
lean_ctor_set(v___x_260_, 12, v_cancelTk_x3f_256_);
lean_ctor_set(v___x_260_, 13, v_inheritedTraceOptions_258_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*14, v_diag_255_);
lean_ctor_set_uint8(v___x_260_, sizeof(void*)*14 + 1, v_suppressElabErrors_257_);
v___x_261_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(v_msg_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___x_260_, v___y_241_);
lean_dec_ref_known(v___x_260_, 14);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg___boxed(lean_object* v_ref_262_, lean_object* v_msg_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(v_ref_262_, v_msg_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v_ref_262_);
return v_res_271_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_272_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__0);
v___x_274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__2(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__1);
v___x_276_ = lean_unsigned_to_nat(0u);
v___x_277_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
lean_ctor_set(v___x_277_, 2, v___x_276_);
lean_ctor_set(v___x_277_, 3, v___x_276_);
lean_ctor_set(v___x_277_, 4, v___x_275_);
lean_ctor_set(v___x_277_, 5, v___x_275_);
lean_ctor_set(v___x_277_, 6, v___x_275_);
lean_ctor_set(v___x_277_, 7, v___x_275_);
lean_ctor_set(v___x_277_, 8, v___x_275_);
lean_ctor_set(v___x_277_, 9, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__3(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_unsigned_to_nat(32u);
v___x_279_ = lean_mk_empty_array_with_capacity(v___x_278_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__4(void){
_start:
{
size_t v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_281_ = ((size_t)5ULL);
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = lean_unsigned_to_nat(32u);
v___x_284_ = lean_mk_empty_array_with_capacity(v___x_283_);
v___x_285_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__3);
v___x_286_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_284_);
lean_ctor_set(v___x_286_, 2, v___x_282_);
lean_ctor_set(v___x_286_, 3, v___x_282_);
lean_ctor_set_usize(v___x_286_, 4, v___x_281_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__5(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_287_ = lean_box(1);
v___x_288_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__4);
v___x_289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__1);
v___x_290_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
lean_ctor_set(v___x_290_, 1, v___x_288_);
lean_ctor_set(v___x_290_, 2, v___x_287_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__7(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__6));
v___x_293_ = l_Lean_stringToMessageData(v___x_292_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__9(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_295_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__8));
v___x_296_ = l_Lean_stringToMessageData(v___x_295_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__11(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__10));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__13(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__12));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__15(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__14));
v___x_305_ = l_Lean_stringToMessageData(v___x_304_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__17(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__16));
v___x_308_ = l_Lean_stringToMessageData(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__19(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__18));
v___x_311_ = l_Lean_stringToMessageData(v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(lean_object* v_msg_312_, lean_object* v_declHint_313_, lean_object* v___y_314_){
_start:
{
lean_object* v___x_316_; lean_object* v_env_317_; uint8_t v___x_318_; 
v___x_316_ = lean_st_ref_get(v___y_314_);
v_env_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc_ref(v_env_317_);
lean_dec(v___x_316_);
v___x_318_ = l_Lean_Name_isAnonymous(v_declHint_313_);
if (v___x_318_ == 0)
{
uint8_t v_isExporting_319_; 
v_isExporting_319_ = lean_ctor_get_uint8(v_env_317_, sizeof(void*)*8);
if (v_isExporting_319_ == 0)
{
lean_object* v___x_320_; 
lean_dec_ref(v_env_317_);
lean_dec(v_declHint_313_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v_msg_312_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; uint8_t v___x_322_; 
lean_inc_ref(v_env_317_);
v___x_321_ = l_Lean_Environment_setExporting(v_env_317_, v___x_318_);
lean_inc(v_declHint_313_);
lean_inc_ref(v___x_321_);
v___x_322_ = l_Lean_Environment_contains(v___x_321_, v_declHint_313_, v_isExporting_319_);
if (v___x_322_ == 0)
{
lean_object* v___x_323_; 
lean_dec_ref(v___x_321_);
lean_dec_ref(v_env_317_);
lean_dec(v_declHint_313_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v_msg_312_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_c_329_; lean_object* v___x_330_; 
v___x_324_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__2);
v___x_325_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__5);
v___x_326_ = l_Lean_Options_empty;
v___x_327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_327_, 0, v___x_321_);
lean_ctor_set(v___x_327_, 1, v___x_324_);
lean_ctor_set(v___x_327_, 2, v___x_325_);
lean_ctor_set(v___x_327_, 3, v___x_326_);
lean_inc(v_declHint_313_);
v___x_328_ = l_Lean_MessageData_ofConstName(v_declHint_313_, v___x_318_);
v_c_329_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_329_, 0, v___x_327_);
lean_ctor_set(v_c_329_, 1, v___x_328_);
v___x_330_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_317_, v_declHint_313_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec_ref(v_env_317_);
lean_dec(v_declHint_313_);
v___x_331_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__7);
v___x_332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v_c_329_);
v___x_333_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__9);
v___x_334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_MessageData_note(v___x_334_);
v___x_336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_336_, 0, v_msg_312_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
else
{
lean_object* v_val_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_373_; 
v_val_338_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_373_ == 0)
{
v___x_340_ = v___x_330_;
v_isShared_341_ = v_isSharedCheck_373_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_val_338_);
lean_dec(v___x_330_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_373_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_mod_345_; uint8_t v___x_346_; 
v___x_342_ = lean_box(0);
v___x_343_ = l_Lean_Environment_header(v_env_317_);
lean_dec_ref(v_env_317_);
v___x_344_ = l_Lean_EnvironmentHeader_moduleNames(v___x_343_);
v_mod_345_ = lean_array_get(v___x_342_, v___x_344_, v_val_338_);
lean_dec(v_val_338_);
lean_dec_ref(v___x_344_);
v___x_346_ = l_Lean_isPrivateName(v_declHint_313_);
lean_dec(v_declHint_313_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_347_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__11);
v___x_348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v_c_329_);
v___x_349_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__13);
v___x_350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = l_Lean_MessageData_ofName(v_mod_345_);
v___x_352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__15);
v___x_354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_352_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = l_Lean_MessageData_note(v___x_354_);
v___x_356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_356_, 0, v_msg_312_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 0);
lean_ctor_set(v___x_340_, 0, v___x_356_);
v___x_358_ = v___x_340_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
v___x_360_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__7);
v___x_361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v_c_329_);
v___x_362_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__17);
v___x_363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = l_Lean_MessageData_ofName(v_mod_345_);
v___x_365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__19);
v___x_367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
v___x_368_ = l_Lean_MessageData_note(v___x_367_);
v___x_369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_369_, 0, v_msg_312_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
if (v_isShared_341_ == 0)
{
lean_ctor_set_tag(v___x_340_, 0);
lean_ctor_set(v___x_340_, 0, v___x_369_);
v___x_371_ = v___x_340_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_374_; 
lean_dec_ref(v_env_317_);
lean_dec(v_declHint_313_);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_msg_312_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___boxed(lean_object* v_msg_375_, lean_object* v_declHint_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_msg_375_, v_declHint_376_, v___y_377_);
lean_dec(v___y_377_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12(lean_object* v_msg_380_, lean_object* v_declHint_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v___x_389_; lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_399_; 
v___x_389_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_msg_380_, v_declHint_381_, v___y_387_);
v_a_390_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_399_ == 0)
{
v___x_392_ = v___x_389_;
v_isShared_393_ = v_isSharedCheck_399_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_399_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_397_; 
v___x_394_ = l_Lean_unknownIdentifierMessageTag;
v___x_395_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_a_390_);
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 0, v___x_395_);
v___x_397_ = v___x_392_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v___x_395_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msg_400_, lean_object* v_declHint_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12(v_msg_400_, v_declHint_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9___redArg(lean_object* v_ref_410_, lean_object* v_msg_411_, lean_object* v_declHint_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; lean_object* v_a_421_; lean_object* v___x_422_; 
v___x_420_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12(v_msg_411_, v_declHint_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
v_a_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_a_421_);
lean_dec_ref(v___x_420_);
v___x_422_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(v_ref_410_, v_a_421_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9___redArg___boxed(lean_object* v_ref_423_, lean_object* v_msg_424_, lean_object* v_declHint_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9___redArg(v_ref_423_, v_msg_424_, v_declHint_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec(v_ref_423_);
return v_res_433_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__0));
v___x_436_ = l_Lean_stringToMessageData(v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__2));
v___x_439_ = l_Lean_stringToMessageData(v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg(lean_object* v_ref_440_, lean_object* v_constName_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; 
v___x_449_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__1);
v___x_450_ = 0;
lean_inc(v_constName_441_);
v___x_451_ = l_Lean_MessageData_ofConstName(v_constName_441_, v___x_450_);
v___x_452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_449_);
lean_ctor_set(v___x_452_, 1, v___x_451_);
v___x_453_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__3);
v___x_454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_452_);
lean_ctor_set(v___x_454_, 1, v___x_453_);
v___x_455_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9___redArg(v_ref_440_, v___x_454_, v_constName_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___boxed(lean_object* v_ref_456_, lean_object* v_constName_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg(v_ref_456_, v_constName_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_);
lean_dec(v___y_463_);
lean_dec_ref(v___y_462_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v_ref_456_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg(lean_object* v_constName_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_ref_474_; lean_object* v___x_475_; 
v_ref_474_ = lean_ctor_get(v___y_471_, 5);
v___x_475_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg(v_ref_474_, v_constName_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg___boxed(lean_object* v_constName_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg(v_constName_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___lam__0(lean_object* v_fst_485_, lean_object* v_fst_486_, lean_object* v_specThm_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_proof_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_proof_495_ = lean_ctor_get(v_specThm_487_, 2);
lean_inc_ref(v_proof_495_);
lean_dec_ref(v_specThm_487_);
v___x_496_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_erase(v_fst_485_, v_proof_495_);
v___x_497_ = lean_box(0);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v_fst_486_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___lam__0___boxed(lean_object* v_fst_501_, lean_object* v_fst_502_, lean_object* v_specThm_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___lam__0(v_fst_501_, v_fst_502_, v_specThm_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_511_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__10(void){
_start:
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__9));
v___x_535_ = l_Lean_stringToMessageData(v___x_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3(lean_object* v_as_537_, size_t v_sz_538_, size_t v_i_539_, lean_object* v_b_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_a_549_; uint8_t v___x_553_; 
v___x_553_ = lean_usize_dec_lt(v_i_539_, v_sz_538_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v_b_540_);
return v___x_554_;
}
else
{
lean_object* v_snd_555_; lean_object* v_fst_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_790_; 
v_snd_555_ = lean_ctor_get(v_b_540_, 1);
v_fst_556_ = lean_ctor_get(v_b_540_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_b_540_);
if (v_isSharedCheck_790_ == 0)
{
v___x_558_ = v_b_540_;
v_isShared_559_ = v_isSharedCheck_790_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_snd_555_);
lean_inc(v_fst_556_);
lean_dec(v_b_540_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_790_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v_fst_560_; lean_object* v_snd_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_789_; 
v_fst_560_ = lean_ctor_get(v_snd_555_, 0);
v_snd_561_ = lean_ctor_get(v_snd_555_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_snd_555_);
if (v_isSharedCheck_789_ == 0)
{
v___x_563_ = v_snd_555_;
v_isShared_564_ = v_isSharedCheck_789_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_snd_561_);
lean_inc(v_fst_560_);
lean_dec(v_snd_555_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_789_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v_fst_566_; lean_object* v_snd_567_; lean_object* v_fst_575_; lean_object* v_snd_576_; lean_object* v_fst_580_; lean_object* v_snd_581_; lean_object* v___x_584_; lean_object* v_a_585_; lean_object* v___y_587_; uint8_t v___y_588_; lean_object* v___y_592_; uint8_t v___y_593_; lean_object* v___y_601_; uint8_t v___y_602_; lean_object* v_a_606_; lean_object* v___y_610_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_584_ = lean_unsigned_to_nat(1u);
v_a_585_ = lean_array_uget_borrowed(v_as_537_, v_i_539_);
lean_inc(v_a_585_);
v___x_616_ = l_Lean_Syntax_getKind(v_a_585_);
v___x_617_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__4));
v___x_618_ = lean_name_eq(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; uint8_t v___x_620_; 
lean_del_object(v___x_563_);
lean_del_object(v___x_558_);
v___x_619_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__6));
v___x_620_ = lean_name_eq(v___x_616_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__8));
v___x_622_ = lean_name_eq(v___x_616_, v___x_621_);
lean_dec(v___x_616_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec_ref_known(v___x_623_, 1);
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v_fst_560_);
lean_ctor_set(v___x_624_, 1, v_snd_561_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_fst_556_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v_a_549_ = v___x_625_;
goto v___jp_548_;
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec(v_snd_561_);
lean_dec(v_fst_560_);
lean_dec(v_fst_556_);
v_a_626_ = lean_ctor_get(v___x_623_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_623_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_623_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_623_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
lean_dec(v_snd_561_);
lean_inc(v_a_585_);
v___x_634_ = lean_array_push(v_fst_560_, v_a_585_);
v___x_635_ = lean_box(v___x_553_);
v___x_636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_634_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v_fst_556_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v_a_549_ = v___x_637_;
goto v___jp_548_;
}
}
else
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
lean_dec(v___x_616_);
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = l_Lean_Syntax_getArg(v_a_585_, v___x_638_);
v___x_640_ = l_Lean_Syntax_isNone(v___x_639_);
lean_dec(v___x_639_);
if (v___x_640_ == 0)
{
goto v___jp_596_;
}
else
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = l_Lean_Syntax_getArg(v_a_585_, v___x_584_);
v___x_642_ = l_Lean_Syntax_isNone(v___x_641_);
lean_dec(v___x_641_);
if (v___x_642_ == 0)
{
goto v___jp_596_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Meta_saveState___redArg(v___y_544_, v___y_546_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_689_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v___x_645_ = lean_unsigned_to_nat(2u);
v___x_646_ = l_Lean_Syntax_getArg(v_a_585_, v___x_645_);
v___x_716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__11));
lean_inc(v___x_646_);
v___x_717_ = l_Lean_Elab_Term_resolveId_x3f(v___x_646_, v___x_716_, v___x_553_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_dec(v_a_644_);
v___y_689_ = v___x_717_;
goto v___jp_688_;
}
else
{
lean_object* v_a_718_; uint8_t v___y_720_; uint8_t v___x_731_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
v___x_731_ = l_Lean_Exception_isInterrupt(v_a_718_);
if (v___x_731_ == 0)
{
uint8_t v___x_732_; 
v___x_732_ = l_Lean_Exception_isRuntime(v_a_718_);
v___y_720_ = v___x_732_;
goto v___jp_719_;
}
else
{
lean_dec(v_a_718_);
v___y_720_ = v___x_731_;
goto v___jp_719_;
}
v___jp_719_:
{
if (v___y_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec_ref_known(v___x_717_, 1);
v___x_721_ = l_Lean_Meta_SavedState_restore___redArg(v_a_644_, v___y_544_, v___y_546_);
lean_dec(v_a_644_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; 
lean_dec_ref_known(v___x_721_, 1);
lean_inc(v___x_646_);
v___x_722_ = l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(v___x_646_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
v___y_689_ = v___x_722_;
goto v___jp_688_;
}
else
{
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v___x_646_);
lean_dec(v_snd_561_);
lean_dec(v_fst_560_);
lean_dec(v_fst_556_);
v_a_723_ = lean_ctor_get(v___x_721_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_721_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_721_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_721_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
else
{
lean_dec(v_a_644_);
v___y_689_ = v___x_717_;
goto v___jp_688_;
}
}
}
v___jp_647_:
{
lean_object* v_fileName_654_; lean_object* v_fileMap_655_; lean_object* v_options_656_; lean_object* v_currRecDepth_657_; lean_object* v_maxRecDepth_658_; lean_object* v_ref_659_; lean_object* v_currNamespace_660_; lean_object* v_openDecls_661_; lean_object* v_initHeartbeats_662_; lean_object* v_maxHeartbeats_663_; lean_object* v_quotContext_664_; lean_object* v_currMacroScope_665_; uint8_t v_diag_666_; lean_object* v_cancelTk_x3f_667_; uint8_t v_suppressElabErrors_668_; lean_object* v_inheritedTraceOptions_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v_ref_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_fileName_654_ = lean_ctor_get(v___y_652_, 0);
v_fileMap_655_ = lean_ctor_get(v___y_652_, 1);
v_options_656_ = lean_ctor_get(v___y_652_, 2);
v_currRecDepth_657_ = lean_ctor_get(v___y_652_, 3);
v_maxRecDepth_658_ = lean_ctor_get(v___y_652_, 4);
v_ref_659_ = lean_ctor_get(v___y_652_, 5);
v_currNamespace_660_ = lean_ctor_get(v___y_652_, 6);
v_openDecls_661_ = lean_ctor_get(v___y_652_, 7);
v_initHeartbeats_662_ = lean_ctor_get(v___y_652_, 8);
v_maxHeartbeats_663_ = lean_ctor_get(v___y_652_, 9);
v_quotContext_664_ = lean_ctor_get(v___y_652_, 10);
v_currMacroScope_665_ = lean_ctor_get(v___y_652_, 11);
v_diag_666_ = lean_ctor_get_uint8(v___y_652_, sizeof(void*)*14);
v_cancelTk_x3f_667_ = lean_ctor_get(v___y_652_, 12);
v_suppressElabErrors_668_ = lean_ctor_get_uint8(v___y_652_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_669_ = lean_ctor_get(v___y_652_, 13);
v___x_670_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__10);
lean_inc(v___x_646_);
v___x_671_ = l_Lean_MessageData_ofSyntax(v___x_646_);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_670_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg___closed__3);
v___x_674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v_ref_675_ = l_Lean_replaceRef(v___x_646_, v_ref_659_);
lean_dec(v___x_646_);
lean_inc_ref(v_inheritedTraceOptions_669_);
lean_inc(v_cancelTk_x3f_667_);
lean_inc(v_currMacroScope_665_);
lean_inc(v_quotContext_664_);
lean_inc(v_maxHeartbeats_663_);
lean_inc(v_initHeartbeats_662_);
lean_inc(v_openDecls_661_);
lean_inc(v_currNamespace_660_);
lean_inc(v_maxRecDepth_658_);
lean_inc(v_currRecDepth_657_);
lean_inc_ref(v_options_656_);
lean_inc_ref(v_fileMap_655_);
lean_inc_ref(v_fileName_654_);
v___x_676_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_676_, 0, v_fileName_654_);
lean_ctor_set(v___x_676_, 1, v_fileMap_655_);
lean_ctor_set(v___x_676_, 2, v_options_656_);
lean_ctor_set(v___x_676_, 3, v_currRecDepth_657_);
lean_ctor_set(v___x_676_, 4, v_maxRecDepth_658_);
lean_ctor_set(v___x_676_, 5, v_ref_675_);
lean_ctor_set(v___x_676_, 6, v_currNamespace_660_);
lean_ctor_set(v___x_676_, 7, v_openDecls_661_);
lean_ctor_set(v___x_676_, 8, v_initHeartbeats_662_);
lean_ctor_set(v___x_676_, 9, v_maxHeartbeats_663_);
lean_ctor_set(v___x_676_, 10, v_quotContext_664_);
lean_ctor_set(v___x_676_, 11, v_currMacroScope_665_);
lean_ctor_set(v___x_676_, 12, v_cancelTk_x3f_667_);
lean_ctor_set(v___x_676_, 13, v_inheritedTraceOptions_669_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*14, v_diag_666_);
lean_ctor_set_uint8(v___x_676_, sizeof(void*)*14 + 1, v_suppressElabErrors_668_);
v___x_677_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(v___x_674_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, v___x_676_, v___y_653_);
lean_dec_ref_known(v___x_676_, 14);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec_ref_known(v___x_677_, 1);
v___x_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_678_, 0, v_fst_560_);
lean_ctor_set(v___x_678_, 1, v_snd_561_);
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v_fst_556_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
v_a_549_ = v___x_679_;
goto v___jp_548_;
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v_snd_561_);
lean_dec(v_fst_560_);
lean_dec(v_fst_556_);
v_a_680_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_677_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_677_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
v___jp_688_:
{
if (lean_obj_tag(v___y_689_) == 0)
{
lean_object* v_a_690_; 
v_a_690_ = lean_ctor_get(v___y_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___y_689_, 1);
if (lean_obj_tag(v_a_690_) == 1)
{
lean_object* v_val_691_; 
v_val_691_ = lean_ctor_get(v_a_690_, 0);
lean_inc(v_val_691_);
lean_dec_ref_known(v_a_690_, 1);
switch(lean_obj_tag(v_val_691_))
{
case 4:
{
lean_object* v_declName_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec(v___x_646_);
v_declName_692_ = lean_ctor_get(v_val_691_, 0);
lean_inc(v_declName_692_);
lean_dec_ref_known(v_val_691_, 2);
v___x_693_ = lean_unsigned_to_nat(1000u);
v___x_694_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_declName_692_, v___x_693_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___x_696_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
v___x_696_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_fst_556_, v_a_695_);
v_fst_580_ = v___x_696_;
v_snd_581_ = v_fst_560_;
goto v___jp_579_;
}
else
{
lean_object* v_a_697_; uint8_t v___x_698_; 
v_a_697_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_694_, 1);
v___x_698_ = l_Lean_Exception_isInterrupt(v_a_697_);
if (v___x_698_ == 0)
{
uint8_t v___x_699_; 
lean_inc(v_a_697_);
v___x_699_ = l_Lean_Exception_isRuntime(v_a_697_);
v___y_587_ = v_a_697_;
v___y_588_ = v___x_699_;
goto v___jp_586_;
}
else
{
v___y_587_ = v_a_697_;
v___y_588_ = v___x_698_;
goto v___jp_586_;
}
}
}
case 1:
{
lean_object* v_fvarId_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec(v___x_646_);
v_fvarId_700_ = lean_ctor_get(v_val_691_, 0);
lean_inc(v_fvarId_700_);
lean_dec_ref_known(v_val_691_, 1);
v___x_701_ = lean_unsigned_to_nat(1000u);
v___x_702_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_fvarId_700_, v___x_701_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref_known(v___x_702_, 1);
v___x_704_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_fst_556_, v_a_703_);
v_fst_575_ = v___x_704_;
v_snd_576_ = v_fst_560_;
goto v___jp_574_;
}
else
{
lean_object* v_a_705_; uint8_t v___x_706_; 
v_a_705_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_705_);
lean_dec_ref_known(v___x_702_, 1);
v___x_706_ = l_Lean_Exception_isInterrupt(v_a_705_);
if (v___x_706_ == 0)
{
uint8_t v___x_707_; 
lean_inc(v_a_705_);
v___x_707_ = l_Lean_Exception_isRuntime(v_a_705_);
v___y_592_ = v_a_705_;
v___y_593_ = v___x_707_;
goto v___jp_591_;
}
else
{
v___y_592_ = v_a_705_;
v___y_593_ = v___x_706_;
goto v___jp_591_;
}
}
}
default: 
{
lean_dec(v_val_691_);
v___y_648_ = v___y_541_;
v___y_649_ = v___y_542_;
v___y_650_ = v___y_543_;
v___y_651_ = v___y_544_;
v___y_652_ = v___y_545_;
v___y_653_ = v___y_546_;
goto v___jp_647_;
}
}
}
else
{
lean_dec(v_a_690_);
v___y_648_ = v___y_541_;
v___y_649_ = v___y_542_;
v___y_650_ = v___y_543_;
v___y_651_ = v___y_544_;
v___y_652_ = v___y_545_;
v___y_653_ = v___y_546_;
goto v___jp_647_;
}
}
else
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_715_; 
lean_dec(v___x_646_);
lean_dec(v_snd_561_);
lean_dec(v_fst_560_);
lean_dec(v_fst_556_);
v_a_708_ = lean_ctor_get(v___y_689_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v___y_689_);
if (v_isSharedCheck_715_ == 0)
{
v___x_710_ = v___y_689_;
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___y_689_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_715_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_711_ == 0)
{
v___x_713_ = v___x_710_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v_snd_561_);
lean_dec(v_fst_560_);
lean_dec(v_fst_556_);
v_a_733_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_643_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_643_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v___x_616_);
v___x_741_ = l_Lean_Syntax_getArg(v_a_585_, v___x_584_);
lean_inc(v___x_741_);
v___x_742_ = l_Lean_Elab_Term_isLocalIdent_x3f(v___x_741_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
if (lean_obj_tag(v_a_743_) == 1)
{
lean_object* v_val_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v___x_741_);
v_val_744_ = lean_ctor_get(v_a_743_, 0);
lean_inc(v_val_744_);
lean_dec_ref_known(v_a_743_, 1);
v___x_745_ = l_Lean_Expr_fvarId_x21(v_val_744_);
lean_dec(v_val_744_);
v___x_746_ = lean_unsigned_to_nat(1000u);
v___x_747_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v___x_745_, v___x_746_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
lean_inc(v_fst_560_);
lean_inc(v_fst_556_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___lam__0(v_fst_556_, v_fst_560_, v_a_748_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
v___y_610_ = v___x_749_;
goto v___jp_609_;
}
else
{
lean_object* v_a_750_; 
v_a_750_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_750_);
lean_dec_ref_known(v___x_747_, 1);
v_a_606_ = v_a_750_;
goto v___jp_605_;
}
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec(v_a_743_);
v___x_751_ = lean_box(0);
lean_inc(v___x_741_);
v___x_752_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_741_, v___x_751_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
lean_dec(v___x_741_);
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = lean_unsigned_to_nat(1000u);
v___x_755_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromConst(v_a_753_, v___x_754_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
lean_inc(v_fst_560_);
lean_inc(v_fst_556_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___lam__0(v_fst_556_, v_fst_560_, v_a_756_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
v___y_610_ = v___x_757_;
goto v___jp_609_;
}
else
{
lean_object* v_a_758_; 
v_a_758_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_758_);
lean_dec_ref_known(v___x_755_, 1);
v_a_606_ = v_a_758_;
goto v___jp_605_;
}
}
else
{
lean_object* v_a_759_; uint8_t v___y_761_; uint8_t v___x_786_; 
v_a_759_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_759_);
lean_dec_ref_known(v___x_752_, 1);
v___x_786_ = l_Lean_Exception_isInterrupt(v_a_759_);
if (v___x_786_ == 0)
{
uint8_t v___x_787_; 
lean_inc(v_a_759_);
v___x_787_ = l_Lean_Exception_isRuntime(v_a_759_);
v___y_761_ = v___x_787_;
goto v___jp_760_;
}
else
{
v___y_761_ = v___x_786_;
goto v___jp_760_;
}
v___jp_760_:
{
if (v___y_761_ == 0)
{
lean_object* v_fileName_762_; lean_object* v_fileMap_763_; lean_object* v_options_764_; lean_object* v_currRecDepth_765_; lean_object* v_maxRecDepth_766_; lean_object* v_ref_767_; lean_object* v_currNamespace_768_; lean_object* v_openDecls_769_; lean_object* v_initHeartbeats_770_; lean_object* v_maxHeartbeats_771_; lean_object* v_quotContext_772_; lean_object* v_currMacroScope_773_; uint8_t v_diag_774_; lean_object* v_cancelTk_x3f_775_; uint8_t v_suppressElabErrors_776_; lean_object* v_inheritedTraceOptions_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_ref_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec(v_a_759_);
v_fileName_762_ = lean_ctor_get(v___y_545_, 0);
v_fileMap_763_ = lean_ctor_get(v___y_545_, 1);
v_options_764_ = lean_ctor_get(v___y_545_, 2);
v_currRecDepth_765_ = lean_ctor_get(v___y_545_, 3);
v_maxRecDepth_766_ = lean_ctor_get(v___y_545_, 4);
v_ref_767_ = lean_ctor_get(v___y_545_, 5);
v_currNamespace_768_ = lean_ctor_get(v___y_545_, 6);
v_openDecls_769_ = lean_ctor_get(v___y_545_, 7);
v_initHeartbeats_770_ = lean_ctor_get(v___y_545_, 8);
v_maxHeartbeats_771_ = lean_ctor_get(v___y_545_, 9);
v_quotContext_772_ = lean_ctor_get(v___y_545_, 10);
v_currMacroScope_773_ = lean_ctor_get(v___y_545_, 11);
v_diag_774_ = lean_ctor_get_uint8(v___y_545_, sizeof(void*)*14);
v_cancelTk_x3f_775_ = lean_ctor_get(v___y_545_, 12);
v_suppressElabErrors_776_ = lean_ctor_get_uint8(v___y_545_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_777_ = lean_ctor_get(v___y_545_, 13);
v___x_778_ = l_Lean_Syntax_getId(v___x_741_);
v___x_779_ = lean_erase_macro_scopes(v___x_778_);
v_ref_780_ = l_Lean_replaceRef(v___x_741_, v_ref_767_);
lean_dec(v___x_741_);
lean_inc_ref(v_inheritedTraceOptions_777_);
lean_inc(v_cancelTk_x3f_775_);
lean_inc(v_currMacroScope_773_);
lean_inc(v_quotContext_772_);
lean_inc(v_maxHeartbeats_771_);
lean_inc(v_initHeartbeats_770_);
lean_inc(v_openDecls_769_);
lean_inc(v_currNamespace_768_);
lean_inc(v_maxRecDepth_766_);
lean_inc(v_currRecDepth_765_);
lean_inc_ref(v_options_764_);
lean_inc_ref(v_fileMap_763_);
lean_inc_ref(v_fileName_762_);
v___x_781_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_781_, 0, v_fileName_762_);
lean_ctor_set(v___x_781_, 1, v_fileMap_763_);
lean_ctor_set(v___x_781_, 2, v_options_764_);
lean_ctor_set(v___x_781_, 3, v_currRecDepth_765_);
lean_ctor_set(v___x_781_, 4, v_maxRecDepth_766_);
lean_ctor_set(v___x_781_, 5, v_ref_780_);
lean_ctor_set(v___x_781_, 6, v_currNamespace_768_);
lean_ctor_set(v___x_781_, 7, v_openDecls_769_);
lean_ctor_set(v___x_781_, 8, v_initHeartbeats_770_);
lean_ctor_set(v___x_781_, 9, v_maxHeartbeats_771_);
lean_ctor_set(v___x_781_, 10, v_quotContext_772_);
lean_ctor_set(v___x_781_, 11, v_currMacroScope_773_);
lean_ctor_set(v___x_781_, 12, v_cancelTk_x3f_775_);
lean_ctor_set(v___x_781_, 13, v_inheritedTraceOptions_777_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*14, v_diag_774_);
lean_ctor_set_uint8(v___x_781_, sizeof(void*)*14 + 1, v_suppressElabErrors_776_);
v___x_782_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg(v___x_779_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___x_781_, v___y_546_);
lean_dec_ref_known(v___x_781_, 14);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; lean_object* v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
lean_inc(v_fst_560_);
lean_inc(v_fst_556_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___lam__0(v_fst_556_, v_fst_560_, v_a_783_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
v___y_610_ = v___x_784_;
goto v___jp_609_;
}
else
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_782_, 1);
v_a_606_ = v_a_785_;
goto v___jp_605_;
}
}
else
{
lean_dec(v___x_741_);
v_a_606_ = v_a_759_;
goto v___jp_605_;
}
}
}
}
}
else
{
lean_object* v_a_788_; 
lean_dec(v___x_741_);
v_a_788_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_788_);
lean_dec_ref_known(v___x_742_, 1);
v_a_606_ = v_a_788_;
goto v___jp_605_;
}
}
v___jp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 0, v_snd_567_);
v___x_569_ = v___x_563_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_snd_567_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_snd_561_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_571_; 
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___x_569_);
lean_ctor_set(v___x_558_, 0, v_fst_566_);
v___x_571_ = v___x_558_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_fst_566_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
v_a_549_ = v___x_571_;
goto v___jp_548_;
}
}
}
v___jp_574_:
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v_snd_576_);
lean_ctor_set(v___x_577_, 1, v_snd_561_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v_fst_575_);
lean_ctor_set(v___x_578_, 1, v___x_577_);
v_a_549_ = v___x_578_;
goto v___jp_548_;
}
v___jp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v_snd_581_);
lean_ctor_set(v___x_582_, 1, v_snd_561_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v_fst_580_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v_a_549_ = v___x_583_;
goto v___jp_548_;
}
v___jp_586_:
{
if (v___y_588_ == 0)
{
lean_object* v___x_589_; 
lean_dec_ref(v___y_587_);
lean_inc(v_a_585_);
v___x_589_ = lean_array_push(v_fst_560_, v_a_585_);
v_fst_580_ = v_fst_556_;
v_snd_581_ = v___x_589_;
goto v___jp_579_;
}
else
{
lean_object* v___x_590_; 
lean_dec(v_snd_561_);
lean_dec(v_fst_560_);
lean_dec(v_fst_556_);
v___x_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_590_, 0, v___y_587_);
return v___x_590_;
}
}
v___jp_591_:
{
if (v___y_593_ == 0)
{
lean_object* v___x_594_; 
lean_dec_ref(v___y_592_);
lean_inc(v_a_585_);
v___x_594_ = lean_array_push(v_fst_560_, v_a_585_);
v_fst_575_ = v_fst_556_;
v_snd_576_ = v___x_594_;
goto v___jp_574_;
}
else
{
lean_object* v___x_595_; 
lean_dec(v_snd_561_);
lean_dec(v_fst_560_);
lean_dec(v_fst_556_);
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v___y_592_);
return v___x_595_;
}
}
v___jp_596_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
lean_inc(v_a_585_);
v___x_597_ = lean_array_push(v_fst_560_, v_a_585_);
v___x_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v_snd_561_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_fst_556_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v_a_549_ = v___x_599_;
goto v___jp_548_;
}
v___jp_600_:
{
if (v___y_602_ == 0)
{
lean_object* v___x_603_; 
lean_dec_ref(v___y_601_);
lean_inc(v_a_585_);
v___x_603_ = lean_array_push(v_fst_560_, v_a_585_);
v_fst_566_ = v_fst_556_;
v_snd_567_ = v___x_603_;
goto v___jp_565_;
}
else
{
lean_object* v___x_604_; 
lean_del_object(v___x_563_);
lean_dec(v_snd_561_);
lean_dec(v_fst_560_);
lean_del_object(v___x_558_);
lean_dec(v_fst_556_);
v___x_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_604_, 0, v___y_601_);
return v___x_604_;
}
}
v___jp_605_:
{
uint8_t v___x_607_; 
v___x_607_ = l_Lean_Exception_isInterrupt(v_a_606_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; 
lean_inc_ref(v_a_606_);
v___x_608_ = l_Lean_Exception_isRuntime(v_a_606_);
v___y_601_ = v_a_606_;
v___y_602_ = v___x_608_;
goto v___jp_600_;
}
else
{
v___y_601_ = v_a_606_;
v___y_602_ = v___x_607_;
goto v___jp_600_;
}
}
v___jp_609_:
{
if (lean_obj_tag(v___y_610_) == 0)
{
lean_object* v_a_611_; lean_object* v_snd_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; 
lean_dec(v_fst_560_);
lean_dec(v_fst_556_);
v_a_611_ = lean_ctor_get(v___y_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___y_610_, 1);
v_snd_612_ = lean_ctor_get(v_a_611_, 1);
lean_inc(v_snd_612_);
lean_dec(v_a_611_);
v_fst_613_ = lean_ctor_get(v_snd_612_, 0);
lean_inc(v_fst_613_);
v_snd_614_ = lean_ctor_get(v_snd_612_, 1);
lean_inc(v_snd_614_);
lean_dec(v_snd_612_);
v_fst_566_ = v_fst_613_;
v_snd_567_ = v_snd_614_;
goto v___jp_565_;
}
else
{
lean_object* v_a_615_; 
v_a_615_ = lean_ctor_get(v___y_610_, 0);
lean_inc(v_a_615_);
lean_dec_ref_known(v___y_610_, 1);
v_a_606_ = v_a_615_;
goto v___jp_605_;
}
}
}
}
}
v___jp_548_:
{
size_t v___x_550_; size_t v___x_551_; 
v___x_550_ = ((size_t)1ULL);
v___x_551_ = lean_usize_add(v_i_539_, v___x_550_);
v_i_539_ = v___x_551_;
v_b_540_ = v_a_549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___boxed(lean_object* v_as_791_, lean_object* v_sz_792_, lean_object* v_i_793_, lean_object* v_b_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_){
_start:
{
size_t v_sz_boxed_802_; size_t v_i_boxed_803_; lean_object* v_res_804_; 
v_sz_boxed_802_ = lean_unbox_usize(v_sz_792_);
lean_dec(v_sz_792_);
v_i_boxed_803_ = lean_unbox_usize(v_i_793_);
lean_dec(v_i_793_);
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3(v_as_791_, v_sz_boxed_802_, v_i_boxed_803_, v_b_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_);
lean_dec(v___y_800_);
lean_dec_ref(v___y_799_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
lean_dec_ref(v_as_791_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___redArg(lean_object* v_as_805_, size_t v_sz_806_, size_t v_i_807_, lean_object* v_b_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_a_815_; uint8_t v___x_819_; 
v___x_819_ = lean_usize_dec_lt(v_i_807_, v_sz_806_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_820_, 0, v_b_808_);
return v___x_820_;
}
else
{
lean_object* v_a_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_a_821_ = lean_array_uget_borrowed(v_as_805_, v_i_807_);
lean_inc(v_a_821_);
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_a_821_);
lean_inc_ref(v_b_808_);
v___x_823_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_isErased(v_b_808_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_821_);
v___x_825_ = l_Lean_Elab_Tactic_Do_SpecAttr_mkSpecTheoremFromLocal(v_a_821_, v___x_824_, v___y_809_, v___y_810_, v___y_811_, v___y_812_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v_a_826_; lean_object* v___x_827_; 
v_a_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_a_826_);
lean_dec_ref_known(v___x_825_, 1);
v___x_827_ = l_Lean_Elab_Tactic_Do_SpecAttr_SpecTheorems_insert(v_b_808_, v_a_826_);
v_a_815_ = v___x_827_;
goto v___jp_814_;
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_839_; 
v_a_828_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_839_ == 0)
{
v___x_830_ = v___x_825_;
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_825_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_839_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
uint8_t v___y_833_; uint8_t v___x_837_; 
v___x_837_ = l_Lean_Exception_isInterrupt(v_a_828_);
if (v___x_837_ == 0)
{
uint8_t v___x_838_; 
lean_inc(v_a_828_);
v___x_838_ = l_Lean_Exception_isRuntime(v_a_828_);
v___y_833_ = v___x_838_;
goto v___jp_832_;
}
else
{
v___y_833_ = v___x_837_;
goto v___jp_832_;
}
v___jp_832_:
{
if (v___y_833_ == 0)
{
lean_del_object(v___x_830_);
lean_dec(v_a_828_);
v_a_815_ = v_b_808_;
goto v___jp_814_;
}
else
{
lean_object* v___x_835_; 
lean_dec_ref(v_b_808_);
if (v_isShared_831_ == 0)
{
v___x_835_ = v___x_830_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_a_828_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
}
}
}
}
else
{
v_a_815_ = v_b_808_;
goto v___jp_814_;
}
}
v___jp_814_:
{
size_t v___x_816_; size_t v___x_817_; 
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_807_, v___x_816_);
v_i_807_ = v___x_817_;
v_b_808_ = v_a_815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___redArg___boxed(lean_object* v_as_840_, lean_object* v_sz_841_, lean_object* v_i_842_, lean_object* v_b_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
size_t v_sz_boxed_849_; size_t v_i_boxed_850_; lean_object* v_res_851_; 
v_sz_boxed_849_ = lean_unbox_usize(v_sz_841_);
lean_dec(v_sz_841_);
v_i_boxed_850_ = lean_unbox_usize(v_i_842_);
lean_dec(v_i_842_);
v_res_851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___redArg(v_as_840_, v_sz_boxed_849_, v_i_boxed_850_, v_b_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec_ref(v_as_840_);
return v_res_851_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__40(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_959_ = lean_box(0);
v___x_960_ = lean_unsigned_to_nat(16u);
v___x_961_ = lean_mk_array(v___x_960_, v___x_959_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41(void){
_start:
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__40, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__40_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__40);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
lean_ctor_set(v___x_964_, 1, v___x_962_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__55(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__54));
v___x_999_ = l_String_toRawSubstring_x27(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__61(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__60));
v___x_1011_ = l_String_toRawSubstring_x27(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__63(void){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Array_mkArray0(lean_box(0));
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__68(void){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__69(void){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5(lean_box(0));
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__70(void){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6(lean_box(0));
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__71(void){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__72(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__71, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__71_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__71);
v___x_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__73(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1025_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__72, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__72_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__72);
v___x_1026_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__70, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__70_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__70);
v___x_1027_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__69, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__69_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__69);
v___x_1028_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__68, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__68_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__68);
v___x_1029_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
lean_ctor_set(v___x_1029_, 2, v___x_1027_);
lean_ctor_set(v___x_1029_, 3, v___x_1026_);
lean_ctor_set(v___x_1029_, 4, v___x_1027_);
lean_ctor_set(v___x_1029_, 5, v___x_1025_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext(lean_object* v_lemmas_1030_, lean_object* v_goal_1031_, uint8_t v_ignoreStarArg_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Elab_Tactic_Do_SpecAttr_getSpecTheorems___redArg(v_a_1038_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v_a_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___y_1045_; lean_object* v_specThms_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1050_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; size_t v_sz_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v_a_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc(v_a_1041_);
lean_dec_ref_known(v___x_1040_, 1);
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = 0;
v___x_1253_ = lean_unsigned_to_nat(1u);
v___x_1254_ = l_Lean_Syntax_getArg(v_lemmas_1030_, v___x_1253_);
v___x_1255_ = l_Lean_Syntax_getSepArgs(v___x_1254_);
lean_dec(v___x_1254_);
v___x_1256_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__42));
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v_a_1041_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v_sz_1258_ = lean_array_size(v___x_1255_);
v___x_1259_ = ((size_t)0ULL);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3(v___x_1255_, v_sz_1258_, v___x_1259_, v___x_1257_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec_ref(v___x_1255_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v_snd_1262_; lean_object* v_fst_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1367_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
lean_inc(v_a_1261_);
lean_dec_ref_known(v___x_1260_, 1);
v_snd_1262_ = lean_ctor_get(v_a_1261_, 1);
v_fst_1263_ = lean_ctor_get(v_a_1261_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_a_1261_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1265_ = v_a_1261_;
v_isShared_1266_ = v_isSharedCheck_1367_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_snd_1262_);
lean_inc(v_fst_1263_);
lean_dec(v_a_1261_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1367_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_fst_1267_; lean_object* v_snd_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1366_; 
v_fst_1267_ = lean_ctor_get(v_snd_1262_, 0);
v_snd_1268_ = lean_ctor_get(v_snd_1262_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_snd_1262_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1270_ = v_snd_1262_;
v_isShared_1271_ = v_isSharedCheck_1366_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_snd_1268_);
lean_inc(v_fst_1267_);
lean_dec(v_snd_1262_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1366_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v_ref_1272_; lean_object* v_quotContext_1273_; lean_object* v_currMacroScope_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v_ref_1272_ = lean_ctor_get(v_a_1037_, 5);
v_quotContext_1273_ = lean_ctor_get(v_a_1037_, 10);
v_currMacroScope_1274_ = lean_ctor_get(v_a_1037_, 11);
v___x_1275_ = l_Lean_SourceInfo_fromRef(v_ref_1272_, v___x_1043_);
v___x_1276_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__43));
v___x_1277_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__44));
lean_inc(v___x_1275_);
if (v_isShared_1271_ == 0)
{
lean_ctor_set_tag(v___x_1270_, 2);
lean_ctor_set(v___x_1270_, 1, v___x_1276_);
lean_ctor_set(v___x_1270_, 0, v___x_1275_);
v___x_1279_ = v___x_1270_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1276_);
v___x_1279_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1280_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46));
v___x_1281_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__48));
v___x_1282_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__50));
v___x_1283_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__52));
v___x_1284_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__53));
lean_inc(v___x_1275_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set_tag(v___x_1265_, 2);
lean_ctor_set(v___x_1265_, 1, v___x_1284_);
lean_ctor_set(v___x_1265_, 0, v___x_1275_);
v___x_1286_ = v___x_1265_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1287_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__55, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__55_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__55);
v___x_1288_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__56));
lean_inc_n(v_currMacroScope_1274_, 2);
lean_inc_n(v_quotContext_1273_, 2);
v___x_1289_ = l_Lean_addMacroScope(v_quotContext_1273_, v___x_1288_, v_currMacroScope_1274_);
v___x_1290_ = lean_box(0);
lean_inc_n(v___x_1275_, 14);
v___x_1291_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1275_);
lean_ctor_set(v___x_1291_, 1, v___x_1287_);
lean_ctor_set(v___x_1291_, 2, v___x_1289_);
lean_ctor_set(v___x_1291_, 3, v___x_1290_);
v___x_1292_ = l_Lean_Syntax_node2(v___x_1275_, v___x_1283_, v___x_1286_, v___x_1291_);
v___x_1293_ = l_Lean_Syntax_node1(v___x_1275_, v___x_1282_, v___x_1292_);
v___x_1294_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__58));
v___x_1295_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__59));
v___x_1296_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1275_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__61, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__61_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__61);
v___x_1298_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__62));
v___x_1299_ = l_Lean_addMacroScope(v_quotContext_1273_, v___x_1298_, v_currMacroScope_1274_);
v___x_1300_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1275_);
lean_ctor_set(v___x_1300_, 1, v___x_1297_);
lean_ctor_set(v___x_1300_, 2, v___x_1299_);
lean_ctor_set(v___x_1300_, 3, v___x_1290_);
v___x_1301_ = l_Lean_Syntax_node2(v___x_1275_, v___x_1294_, v___x_1296_, v___x_1300_);
v___x_1302_ = l_Lean_Syntax_node1(v___x_1275_, v___x_1282_, v___x_1301_);
v___x_1303_ = l_Lean_Syntax_node2(v___x_1275_, v___x_1281_, v___x_1293_, v___x_1302_);
v___x_1304_ = l_Lean_Syntax_node1(v___x_1275_, v___x_1280_, v___x_1303_);
v___x_1305_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__63, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__63_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__63);
v___x_1306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1275_);
lean_ctor_set(v___x_1306_, 1, v___x_1281_);
lean_ctor_set(v___x_1306_, 2, v___x_1305_);
v___x_1307_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__64));
v___x_1308_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1275_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
v___x_1309_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__65));
v___x_1310_ = l_Lean_Syntax_SepArray_ofElems(v___x_1309_, v_fst_1267_);
lean_dec(v_fst_1267_);
v___x_1311_ = l_Array_append___redArg(v___x_1305_, v___x_1310_);
lean_dec_ref(v___x_1310_);
v___x_1312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1275_);
lean_ctor_set(v___x_1312_, 1, v___x_1281_);
lean_ctor_set(v___x_1312_, 2, v___x_1311_);
v___x_1313_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__66));
v___x_1314_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1275_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = l_Lean_Syntax_node3(v___x_1275_, v___x_1281_, v___x_1308_, v___x_1312_, v___x_1314_);
lean_inc_ref_n(v___x_1306_, 2);
v___x_1316_ = l_Lean_Syntax_node6(v___x_1275_, v___x_1277_, v___x_1279_, v___x_1304_, v___x_1306_, v___x_1306_, v___x_1315_, v___x_1306_);
v___x_1317_ = 0;
v___x_1318_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__67));
v___x_1319_ = lean_box(v___x_1043_);
v___x_1320_ = lean_box(v___x_1317_);
v___x_1321_ = lean_box(v_ignoreStarArg_1032_);
v___x_1322_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_1322_, 0, v___x_1316_);
lean_closure_set(v___x_1322_, 1, v___x_1319_);
lean_closure_set(v___x_1322_, 2, v___x_1320_);
lean_closure_set(v___x_1322_, 3, v___x_1321_);
lean_closure_set(v___x_1322_, 4, v___x_1318_);
v___x_1323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_goal_1031_);
lean_ctor_set(v___x_1323_, 1, v___x_1290_);
v___x_1324_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg(v___x_1322_, v___x_1323_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___y_1327_; lean_object* v_ctx_1350_; lean_object* v_simpTheorems_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_a_1325_);
lean_dec_ref_known(v___x_1324_, 1);
v_ctx_1350_ = lean_ctor_get(v_a_1325_, 0);
lean_inc_ref(v_ctx_1350_);
lean_dec(v_a_1325_);
v_simpTheorems_1351_ = lean_ctor_get(v_ctx_1350_, 6);
lean_inc_ref(v_simpTheorems_1351_);
lean_dec_ref(v_ctx_1350_);
v___x_1352_ = lean_array_get_size(v_simpTheorems_1351_);
v___x_1353_ = lean_nat_dec_lt(v___x_1042_, v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1354_; 
lean_dec_ref(v_simpTheorems_1351_);
v___x_1354_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__73, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__73_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__73);
v___y_1327_ = v___x_1354_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_array_fget(v_simpTheorems_1351_, v___x_1042_);
lean_dec_ref(v_simpTheorems_1351_);
v___y_1327_ = v___x_1355_;
goto v___jp_1326_;
}
v___jp_1326_:
{
uint8_t v___x_1328_; 
v___x_1328_ = lean_unbox(v_snd_1268_);
lean_dec(v_snd_1268_);
if (v___x_1328_ == 0)
{
v___y_1045_ = v___y_1327_;
v_specThms_1046_ = v_fst_1263_;
v___y_1047_ = v_a_1035_;
v___y_1048_ = v_a_1036_;
v___y_1049_ = v_a_1037_;
v___y_1050_ = v_a_1038_;
goto v___jp_1044_;
}
else
{
if (v_ignoreStarArg_1032_ == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Meta_getPropHyps(v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; size_t v_sz_1331_; lean_object* v___x_1332_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref_known(v___x_1329_, 1);
v_sz_1331_ = lean_array_size(v_a_1330_);
v___x_1332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___redArg(v_a_1330_, v_sz_1331_, v___x_1259_, v_fst_1263_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
lean_dec(v_a_1330_);
if (lean_obj_tag(v___x_1332_) == 0)
{
lean_object* v_a_1333_; 
v_a_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_a_1333_);
lean_dec_ref_known(v___x_1332_, 1);
v___y_1045_ = v___y_1327_;
v_specThms_1046_ = v_a_1333_;
v___y_1047_ = v_a_1035_;
v___y_1048_ = v_a_1036_;
v___y_1049_ = v_a_1037_;
v___y_1050_ = v_a_1038_;
goto v___jp_1044_;
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec_ref(v___y_1327_);
v_a_1334_ = lean_ctor_get(v___x_1332_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1332_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1332_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1332_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_object* v_a_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
lean_dec_ref(v___y_1327_);
lean_dec(v_fst_1263_);
v_a_1342_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1329_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_a_1342_);
lean_dec(v___x_1329_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_a_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
else
{
v___y_1045_ = v___y_1327_;
v_specThms_1046_ = v_fst_1263_;
v___y_1047_ = v_a_1035_;
v___y_1048_ = v_a_1036_;
v___y_1049_ = v_a_1037_;
v___y_1050_ = v_a_1038_;
goto v___jp_1044_;
}
}
}
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_snd_1268_);
lean_dec(v_fst_1263_);
v_a_1356_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1324_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1324_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
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
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec(v_goal_1031_);
v_a_1368_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1260_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1260_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
v___jp_1044_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1051_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5));
v___x_1052_ = lean_box(0);
v___x_1053_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1051_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1053_) == 0)
{
lean_object* v_a_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_a_1054_ = lean_ctor_get(v___x_1053_, 0);
lean_inc(v_a_1054_);
lean_dec_ref_known(v___x_1053_, 1);
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7));
v___x_1056_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1055_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_a_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___x_1058_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9));
v___x_1059_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1058_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1059_, 1);
v___x_1061_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11));
v___x_1062_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1061_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v___x_1062_, 1);
v___x_1064_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13));
v___x_1065_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1064_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v___x_1067_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15));
v___x_1068_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1067_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref_known(v___x_1068_, 1);
v___x_1070_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17));
v___x_1071_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1070_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v_a_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_a_1072_);
lean_dec_ref_known(v___x_1071_, 1);
v___x_1073_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19));
v___x_1074_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1073_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_a_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_a_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_a_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___x_1076_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23));
v___x_1077_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1076_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1077_) == 0)
{
lean_object* v_a_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_a_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_a_1078_);
lean_dec_ref_known(v___x_1077_, 1);
v___x_1079_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25));
v___x_1080_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1079_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
v___x_1082_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27));
v___x_1083_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1082_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1083_) == 0)
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v_a_1084_ = lean_ctor_get(v___x_1083_, 0);
lean_inc(v_a_1084_);
lean_dec_ref_known(v___x_1083_, 1);
v___x_1085_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29));
v___x_1086_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1085_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31));
v___x_1089_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1088_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v___x_1091_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33));
v___x_1092_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1091_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1094_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__36));
v___x_1095_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1094_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1095_) == 0)
{
lean_object* v_a_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
lean_inc(v_a_1096_);
lean_dec_ref_known(v___x_1095_, 1);
v___x_1097_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__39));
v___x_1098_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_1097_, v___x_1052_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_SpecAttr_migrateSpecTheoremsDatabase___boxed), 9, 2);
lean_closure_set(v___x_1100_, 0, v_specThms_1046_);
lean_closure_set(v___x_1100_, 1, v___y_1045_);
v___x_1101_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_1100_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1116_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1116_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1116_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; uint8_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1106_ = lean_box(0);
v___x_1107_ = 1;
v___x_1108_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41);
v___x_1109_ = lean_alloc_ctor(0, 19, 4);
lean_ctor_set(v___x_1109_, 0, v_a_1054_);
lean_ctor_set(v___x_1109_, 1, v_a_1057_);
lean_ctor_set(v___x_1109_, 2, v_a_1060_);
lean_ctor_set(v___x_1109_, 3, v_a_1063_);
lean_ctor_set(v___x_1109_, 4, v_a_1066_);
lean_ctor_set(v___x_1109_, 5, v_a_1069_);
lean_ctor_set(v___x_1109_, 6, v_a_1072_);
lean_ctor_set(v___x_1109_, 7, v_a_1075_);
lean_ctor_set(v___x_1109_, 8, v_a_1078_);
lean_ctor_set(v___x_1109_, 9, v_a_1081_);
lean_ctor_set(v___x_1109_, 10, v_a_1084_);
lean_ctor_set(v___x_1109_, 11, v_a_1087_);
lean_ctor_set(v___x_1109_, 12, v_a_1090_);
lean_ctor_set(v___x_1109_, 13, v_a_1093_);
lean_ctor_set(v___x_1109_, 14, v_a_1096_);
lean_ctor_set(v___x_1109_, 15, v_a_1099_);
lean_ctor_set(v___x_1109_, 16, v___x_1052_);
lean_ctor_set(v___x_1109_, 17, v___x_1106_);
lean_ctor_set(v___x_1109_, 18, v___x_1108_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*19, v___x_1107_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*19 + 1, v___x_1043_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*19 + 2, v___x_1107_);
lean_ctor_set_uint8(v___x_1109_, sizeof(void*)*19 + 3, v___x_1043_);
v___x_1110_ = lean_box(1);
v___x_1111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1111_, 0, v_a_1102_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
lean_ctor_set(v___x_1111_, 2, v___x_1042_);
v___x_1112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1109_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1112_);
v___x_1114_ = v___x_1104_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec(v_a_1099_);
lean_dec(v_a_1096_);
lean_dec(v_a_1093_);
lean_dec(v_a_1090_);
lean_dec(v_a_1087_);
lean_dec(v_a_1084_);
lean_dec(v_a_1081_);
lean_dec(v_a_1078_);
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
v_a_1117_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1101_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1101_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
else
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1132_; 
lean_dec(v_a_1096_);
lean_dec(v_a_1093_);
lean_dec(v_a_1090_);
lean_dec(v_a_1087_);
lean_dec(v_a_1084_);
lean_dec(v_a_1081_);
lean_dec(v_a_1078_);
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1125_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1127_ = v___x_1098_;
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1098_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1132_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1130_; 
if (v_isShared_1128_ == 0)
{
v___x_1130_ = v___x_1127_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1125_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v_a_1093_);
lean_dec(v_a_1090_);
lean_dec(v_a_1087_);
lean_dec(v_a_1084_);
lean_dec(v_a_1081_);
lean_dec(v_a_1078_);
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1133_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1095_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1095_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1148_; 
lean_dec(v_a_1090_);
lean_dec(v_a_1087_);
lean_dec(v_a_1084_);
lean_dec(v_a_1081_);
lean_dec(v_a_1078_);
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1141_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1148_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1143_ = v___x_1092_;
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1092_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1148_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1146_; 
if (v_isShared_1144_ == 0)
{
v___x_1146_ = v___x_1143_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1141_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_a_1087_);
lean_dec(v_a_1084_);
lean_dec(v_a_1081_);
lean_dec(v_a_1078_);
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1149_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1089_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1089_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v_a_1084_);
lean_dec(v_a_1081_);
lean_dec(v_a_1078_);
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1157_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1086_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1086_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_a_1081_);
lean_dec(v_a_1078_);
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1165_ = lean_ctor_get(v___x_1083_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1083_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1083_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1083_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec(v_a_1078_);
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1173_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1080_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1080_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_a_1075_);
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1181_ = lean_ctor_get(v___x_1077_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1077_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1077_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1077_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v_a_1072_);
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1189_ = lean_ctor_get(v___x_1074_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1074_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1074_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1074_);
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
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_a_1069_);
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1197_ = lean_ctor_get(v___x_1071_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1071_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1071_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1071_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_a_1066_);
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1205_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1068_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1068_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v_a_1063_);
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1213_ = lean_ctor_get(v___x_1065_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1065_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1065_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1065_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_a_1060_);
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1221_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1062_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1062_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_a_1057_);
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1229_ = lean_ctor_get(v___x_1059_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1059_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1059_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_a_1054_);
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1237_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1056_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1056_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_specThms_1046_);
lean_dec_ref(v___y_1045_);
v_a_1245_ = lean_ctor_get(v___x_1053_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1053_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1053_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1053_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v_goal_1031_);
v_a_1376_ = lean_ctor_get(v___x_1040_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1040_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1040_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___boxed(lean_object* v_lemmas_1384_, lean_object* v_goal_1385_, lean_object* v_ignoreStarArg_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_){
_start:
{
uint8_t v_ignoreStarArg_boxed_1394_; lean_object* v_res_1395_; 
v_ignoreStarArg_boxed_1394_ = lean_unbox(v_ignoreStarArg_1386_);
v_res_1395_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext(v_lemmas_1384_, v_goal_1385_, v_ignoreStarArg_boxed_1394_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
lean_dec_ref(v_a_1387_);
lean_dec(v_lemmas_1384_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1(lean_object* v_00_u03b1_1396_, lean_object* v_msg_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(v_msg_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___boxed(lean_object* v_00_u03b1_1406_, lean_object* v_msg_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1(v_00_u03b1_1406_, v_msg_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2(lean_object* v_00_u03b1_1416_, lean_object* v_constName_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg(v_constName_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___boxed(lean_object* v_00_u03b1_1426_, lean_object* v_constName_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2(v_00_u03b1_1426_, v_constName_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4(lean_object* v_as_1436_, size_t v_sz_1437_, size_t v_i_1438_, lean_object* v_b_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___redArg(v_as_1436_, v_sz_1437_, v_i_1438_, v_b_1439_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___boxed(lean_object* v_as_1448_, lean_object* v_sz_1449_, lean_object* v_i_1450_, lean_object* v_b_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
size_t v_sz_boxed_1459_; size_t v_i_boxed_1460_; lean_object* v_res_1461_; 
v_sz_boxed_1459_ = lean_unbox_usize(v_sz_1449_);
lean_dec(v_sz_1449_);
v_i_boxed_1460_ = lean_unbox_usize(v_i_1450_);
lean_dec(v_i_1450_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4(v_as_1448_, v_sz_boxed_1459_, v_i_boxed_1460_, v_b_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec_ref(v_as_1448_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2(lean_object* v_msgData_1462_, lean_object* v_macroStack_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg(v_msgData_1462_, v_macroStack_1463_, v___y_1468_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___boxed(lean_object* v_msgData_1472_, lean_object* v_macroStack_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2(v_msgData_1472_, v_macroStack_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4(lean_object* v_00_u03b1_1482_, lean_object* v_ref_1483_, lean_object* v_constName_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___redArg(v_ref_1483_, v_constName_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1493_, lean_object* v_ref_1494_, lean_object* v_constName_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4(v_00_u03b1_1493_, v_ref_1494_, v_constName_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v_ref_1494_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9(lean_object* v_00_u03b1_1504_, lean_object* v_ref_1505_, lean_object* v_msg_1506_, lean_object* v_declHint_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9___redArg(v_ref_1505_, v_msg_1506_, v_declHint_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9___boxed(lean_object* v_00_u03b1_1516_, lean_object* v_ref_1517_, lean_object* v_msg_1518_, lean_object* v_declHint_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9(v_00_u03b1_1516_, v_ref_1517_, v_msg_1518_, v_declHint_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v_ref_1517_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13(lean_object* v_msg_1528_, lean_object* v_declHint_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg(v_msg_1528_, v_declHint_1529_, v___y_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___boxed(lean_object* v_msg_1538_, lean_object* v_declHint_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13(v_msg_1538_, v_declHint_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13(lean_object* v_00_u03b1_1548_, lean_object* v_ref_1549_, lean_object* v_msg_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(v_ref_1549_, v_msg_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___boxed(lean_object* v_00_u03b1_1559_, lean_object* v_ref_1560_, lean_object* v_msg_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13(v_00_u03b1_1559_, v_ref_1560_, v_msg_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v_ref_1560_);
return v_res_1569_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_1577_, uint8_t v_suppressElabErrors_1578_, lean_object* v_x_1579_){
_start:
{
if (lean_obj_tag(v_x_1579_) == 1)
{
lean_object* v_pre_1580_; 
v_pre_1580_ = lean_ctor_get(v_x_1579_, 0);
switch(lean_obj_tag(v_pre_1580_))
{
case 1:
{
lean_object* v_pre_1581_; 
v_pre_1581_ = lean_ctor_get(v_pre_1580_, 0);
switch(lean_obj_tag(v_pre_1581_))
{
case 0:
{
lean_object* v_str_1582_; lean_object* v_str_1583_; lean_object* v___x_1584_; uint8_t v___x_1585_; 
v_str_1582_ = lean_ctor_get(v_x_1579_, 1);
v_str_1583_ = lean_ctor_get(v_pre_1580_, 1);
v___x_1584_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1585_ = lean_string_dec_eq(v_str_1583_, v___x_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___closed__2));
v___x_1587_ = lean_string_dec_eq(v_str_1583_, v___x_1586_);
if (v___x_1587_ == 0)
{
return v___y_1577_;
}
else
{
lean_object* v___x_1588_; uint8_t v___x_1589_; 
v___x_1588_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1589_ = lean_string_dec_eq(v_str_1582_, v___x_1588_);
if (v___x_1589_ == 0)
{
return v___y_1577_;
}
else
{
return v_suppressElabErrors_1578_;
}
}
}
else
{
lean_object* v___x_1590_; uint8_t v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1591_ = lean_string_dec_eq(v_str_1582_, v___x_1590_);
if (v___x_1591_ == 0)
{
return v___y_1577_;
}
else
{
return v_suppressElabErrors_1578_;
}
}
}
case 1:
{
lean_object* v_pre_1592_; 
v_pre_1592_ = lean_ctor_get(v_pre_1581_, 0);
if (lean_obj_tag(v_pre_1592_) == 0)
{
lean_object* v_str_1593_; lean_object* v_str_1594_; lean_object* v_str_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_str_1593_ = lean_ctor_get(v_x_1579_, 1);
v_str_1594_ = lean_ctor_get(v_pre_1580_, 1);
v_str_1595_ = lean_ctor_get(v_pre_1581_, 1);
v___x_1596_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1597_ = lean_string_dec_eq(v_str_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
return v___y_1577_;
}
else
{
lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1598_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1599_ = lean_string_dec_eq(v_str_1594_, v___x_1598_);
if (v___x_1599_ == 0)
{
return v___y_1577_;
}
else
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1601_ = lean_string_dec_eq(v_str_1593_, v___x_1600_);
if (v___x_1601_ == 0)
{
return v___y_1577_;
}
else
{
return v_suppressElabErrors_1578_;
}
}
}
}
else
{
return v___y_1577_;
}
}
default: 
{
return v___y_1577_;
}
}
}
case 0:
{
lean_object* v_str_1602_; lean_object* v___x_1603_; uint8_t v___x_1604_; 
v_str_1602_ = lean_ctor_get(v_x_1579_, 1);
v___x_1603_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_1604_ = lean_string_dec_eq(v_str_1602_, v___x_1603_);
if (v___x_1604_ == 0)
{
return v___y_1577_;
}
else
{
return v_suppressElabErrors_1578_;
}
}
default: 
{
return v___y_1577_;
}
}
}
else
{
return v___y_1577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_1605_, lean_object* v_suppressElabErrors_1606_, lean_object* v_x_1607_){
_start:
{
uint8_t v___y_2865__boxed_1608_; uint8_t v_suppressElabErrors_boxed_1609_; uint8_t v_res_1610_; lean_object* v_r_1611_; 
v___y_2865__boxed_1608_ = lean_unbox(v___y_1605_);
v_suppressElabErrors_boxed_1609_ = lean_unbox(v_suppressElabErrors_1606_);
v_res_1610_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0(v___y_2865__boxed_1608_, v_suppressElabErrors_boxed_1609_, v_x_1607_);
lean_dec(v_x_1607_);
v_r_1611_ = lean_box(v_res_1610_);
return v_r_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1(lean_object* v_ref_1613_, lean_object* v_msgData_1614_, uint8_t v_severity_1615_, uint8_t v_isSilent_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___y_1626_; uint8_t v___y_1627_; lean_object* v___y_1628_; uint8_t v___y_1629_; lean_object* v___y_1630_; lean_object* v___y_1631_; lean_object* v___y_1659_; lean_object* v___y_1660_; uint8_t v___y_1661_; lean_object* v___y_1662_; uint8_t v___y_1663_; uint8_t v___y_1664_; lean_object* v___y_1665_; lean_object* v___y_1666_; lean_object* v___y_1684_; lean_object* v___y_1685_; lean_object* v___y_1686_; uint8_t v___y_1687_; lean_object* v___y_1688_; uint8_t v___y_1689_; uint8_t v___y_1690_; lean_object* v___y_1691_; lean_object* v___y_1695_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; uint8_t v___y_1699_; uint8_t v___y_1700_; uint8_t v___y_1701_; uint8_t v___x_1706_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; uint8_t v___y_1712_; uint8_t v___y_1713_; uint8_t v___y_1714_; uint8_t v___y_1716_; uint8_t v___x_1731_; 
v___x_1706_ = 2;
v___x_1731_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1615_, v___x_1706_);
if (v___x_1731_ == 0)
{
v___y_1716_ = v___x_1731_;
goto v___jp_1715_;
}
else
{
uint8_t v___x_1732_; 
lean_inc_ref(v_msgData_1614_);
v___x_1732_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1614_);
v___y_1716_ = v___x_1732_;
goto v___jp_1715_;
}
v___jp_1622_:
{
lean_object* v___x_1632_; lean_object* v_currNamespace_1633_; lean_object* v_openDecls_1634_; lean_object* v_env_1635_; lean_object* v_nextMacroScope_1636_; lean_object* v_ngen_1637_; lean_object* v_auxDeclNGen_1638_; lean_object* v_traceState_1639_; lean_object* v_cache_1640_; lean_object* v_messages_1641_; lean_object* v_infoState_1642_; lean_object* v_snapshotTasks_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1657_; 
v___x_1632_ = lean_st_ref_take(v___y_1631_);
v_currNamespace_1633_ = lean_ctor_get(v___y_1630_, 6);
v_openDecls_1634_ = lean_ctor_get(v___y_1630_, 7);
v_env_1635_ = lean_ctor_get(v___x_1632_, 0);
v_nextMacroScope_1636_ = lean_ctor_get(v___x_1632_, 1);
v_ngen_1637_ = lean_ctor_get(v___x_1632_, 2);
v_auxDeclNGen_1638_ = lean_ctor_get(v___x_1632_, 3);
v_traceState_1639_ = lean_ctor_get(v___x_1632_, 4);
v_cache_1640_ = lean_ctor_get(v___x_1632_, 5);
v_messages_1641_ = lean_ctor_get(v___x_1632_, 6);
v_infoState_1642_ = lean_ctor_get(v___x_1632_, 7);
v_snapshotTasks_1643_ = lean_ctor_get(v___x_1632_, 8);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1632_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1645_ = v___x_1632_;
v_isShared_1646_ = v_isSharedCheck_1657_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_snapshotTasks_1643_);
lean_inc(v_infoState_1642_);
lean_inc(v_messages_1641_);
lean_inc(v_cache_1640_);
lean_inc(v_traceState_1639_);
lean_inc(v_auxDeclNGen_1638_);
lean_inc(v_ngen_1637_);
lean_inc(v_nextMacroScope_1636_);
lean_inc(v_env_1635_);
lean_dec(v___x_1632_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1657_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1652_; 
lean_inc(v_openDecls_1634_);
lean_inc(v_currNamespace_1633_);
v___x_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1647_, 0, v_currNamespace_1633_);
lean_ctor_set(v___x_1647_, 1, v_openDecls_1634_);
v___x_1648_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc_ref(v___y_1626_);
v___x_1649_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1649_, 0, v___y_1626_);
lean_ctor_set(v___x_1649_, 1, v___y_1628_);
lean_ctor_set(v___x_1649_, 2, v___y_1625_);
lean_ctor_set(v___x_1649_, 3, v___y_1623_);
lean_ctor_set(v___x_1649_, 4, v___x_1648_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*5, v___y_1629_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*5 + 1, v___y_1627_);
lean_ctor_set_uint8(v___x_1649_, sizeof(void*)*5 + 2, v_isSilent_1616_);
v___x_1650_ = l_Lean_MessageLog_add(v___x_1649_, v_messages_1641_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 6, v___x_1650_);
v___x_1652_ = v___x_1645_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_env_1635_);
lean_ctor_set(v_reuseFailAlloc_1656_, 1, v_nextMacroScope_1636_);
lean_ctor_set(v_reuseFailAlloc_1656_, 2, v_ngen_1637_);
lean_ctor_set(v_reuseFailAlloc_1656_, 3, v_auxDeclNGen_1638_);
lean_ctor_set(v_reuseFailAlloc_1656_, 4, v_traceState_1639_);
lean_ctor_set(v_reuseFailAlloc_1656_, 5, v_cache_1640_);
lean_ctor_set(v_reuseFailAlloc_1656_, 6, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1656_, 7, v_infoState_1642_);
lean_ctor_set(v_reuseFailAlloc_1656_, 8, v_snapshotTasks_1643_);
v___x_1652_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = lean_st_ref_set(v___y_1631_, v___x_1652_);
v___x_1654_ = lean_box(0);
v___x_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1654_);
return v___x_1655_;
}
}
}
v___jp_1658_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v_a_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1682_; 
v___x_1667_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1614_);
v___x_1668_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v___x_1667_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1671_ = v___x_1668_;
v_isShared_1672_ = v_isSharedCheck_1682_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_a_1669_);
lean_dec(v___x_1668_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1682_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_inc_ref_n(v___y_1662_, 2);
v___x_1673_ = l_Lean_FileMap_toPosition(v___y_1662_, v___y_1665_);
lean_dec(v___y_1665_);
v___x_1674_ = l_Lean_FileMap_toPosition(v___y_1662_, v___y_1666_);
lean_dec(v___y_1666_);
v___x_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
v___x_1676_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___closed__0));
if (v___y_1663_ == 0)
{
lean_del_object(v___x_1671_);
lean_dec_ref(v___y_1659_);
v___y_1623_ = v___x_1676_;
v___y_1624_ = v_a_1669_;
v___y_1625_ = v___x_1675_;
v___y_1626_ = v___y_1660_;
v___y_1627_ = v___y_1661_;
v___y_1628_ = v___x_1673_;
v___y_1629_ = v___y_1664_;
v___y_1630_ = v___y_1619_;
v___y_1631_ = v___y_1620_;
goto v___jp_1622_;
}
else
{
uint8_t v___x_1677_; 
lean_inc(v_a_1669_);
v___x_1677_ = l_Lean_MessageData_hasTag(v___y_1659_, v_a_1669_);
if (v___x_1677_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
lean_dec_ref_known(v___x_1675_, 1);
lean_dec_ref(v___x_1673_);
lean_dec(v_a_1669_);
v___x_1678_ = lean_box(0);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 0, v___x_1678_);
v___x_1680_ = v___x_1671_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
else
{
lean_del_object(v___x_1671_);
v___y_1623_ = v___x_1676_;
v___y_1624_ = v_a_1669_;
v___y_1625_ = v___x_1675_;
v___y_1626_ = v___y_1660_;
v___y_1627_ = v___y_1661_;
v___y_1628_ = v___x_1673_;
v___y_1629_ = v___y_1664_;
v___y_1630_ = v___y_1619_;
v___y_1631_ = v___y_1620_;
goto v___jp_1622_;
}
}
}
}
v___jp_1683_:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_Syntax_getTailPos_x3f(v___y_1686_, v___y_1690_);
lean_dec(v___y_1686_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_inc(v___y_1691_);
v___y_1659_ = v___y_1684_;
v___y_1660_ = v___y_1685_;
v___y_1661_ = v___y_1687_;
v___y_1662_ = v___y_1688_;
v___y_1663_ = v___y_1689_;
v___y_1664_ = v___y_1690_;
v___y_1665_ = v___y_1691_;
v___y_1666_ = v___y_1691_;
goto v___jp_1658_;
}
else
{
lean_object* v_val_1693_; 
v_val_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_val_1693_);
lean_dec_ref_known(v___x_1692_, 1);
v___y_1659_ = v___y_1684_;
v___y_1660_ = v___y_1685_;
v___y_1661_ = v___y_1687_;
v___y_1662_ = v___y_1688_;
v___y_1663_ = v___y_1689_;
v___y_1664_ = v___y_1690_;
v___y_1665_ = v___y_1691_;
v___y_1666_ = v_val_1693_;
goto v___jp_1658_;
}
}
v___jp_1694_:
{
lean_object* v_ref_1702_; lean_object* v___x_1703_; 
v_ref_1702_ = l_Lean_replaceRef(v_ref_1613_, v___y_1696_);
v___x_1703_ = l_Lean_Syntax_getPos_x3f(v_ref_1702_, v___y_1700_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_unsigned_to_nat(0u);
v___y_1684_ = v___y_1695_;
v___y_1685_ = v___y_1697_;
v___y_1686_ = v_ref_1702_;
v___y_1687_ = v___y_1701_;
v___y_1688_ = v___y_1698_;
v___y_1689_ = v___y_1699_;
v___y_1690_ = v___y_1700_;
v___y_1691_ = v___x_1704_;
goto v___jp_1683_;
}
else
{
lean_object* v_val_1705_; 
v_val_1705_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v___x_1703_, 1);
v___y_1684_ = v___y_1695_;
v___y_1685_ = v___y_1697_;
v___y_1686_ = v_ref_1702_;
v___y_1687_ = v___y_1701_;
v___y_1688_ = v___y_1698_;
v___y_1689_ = v___y_1699_;
v___y_1690_ = v___y_1700_;
v___y_1691_ = v_val_1705_;
goto v___jp_1683_;
}
}
v___jp_1707_:
{
if (v___y_1714_ == 0)
{
v___y_1695_ = v___y_1710_;
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1711_;
v___y_1699_ = v___y_1712_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v_severity_1615_;
goto v___jp_1694_;
}
else
{
v___y_1695_ = v___y_1710_;
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1711_;
v___y_1699_ = v___y_1712_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___x_1706_;
goto v___jp_1694_;
}
}
v___jp_1715_:
{
if (v___y_1716_ == 0)
{
lean_object* v_fileName_1717_; lean_object* v_fileMap_1718_; lean_object* v_options_1719_; lean_object* v_ref_1720_; uint8_t v_suppressElabErrors_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___f_1724_; uint8_t v___x_1725_; uint8_t v___x_1726_; 
v_fileName_1717_ = lean_ctor_get(v___y_1619_, 0);
v_fileMap_1718_ = lean_ctor_get(v___y_1619_, 1);
v_options_1719_ = lean_ctor_get(v___y_1619_, 2);
v_ref_1720_ = lean_ctor_get(v___y_1619_, 5);
v_suppressElabErrors_1721_ = lean_ctor_get_uint8(v___y_1619_, sizeof(void*)*14 + 1);
v___x_1722_ = lean_box(v___y_1716_);
v___x_1723_ = lean_box(v_suppressElabErrors_1721_);
v___f_1724_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1724_, 0, v___x_1722_);
lean_closure_set(v___f_1724_, 1, v___x_1723_);
v___x_1725_ = 1;
v___x_1726_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1615_, v___x_1725_);
if (v___x_1726_ == 0)
{
v___y_1708_ = v_ref_1720_;
v___y_1709_ = v_fileName_1717_;
v___y_1710_ = v___f_1724_;
v___y_1711_ = v_fileMap_1718_;
v___y_1712_ = v_suppressElabErrors_1721_;
v___y_1713_ = v___y_1716_;
v___y_1714_ = v___x_1726_;
goto v___jp_1707_;
}
else
{
lean_object* v___x_1727_; uint8_t v___x_1728_; 
v___x_1727_ = l_Lean_warningAsError;
v___x_1728_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_options_1719_, v___x_1727_);
v___y_1708_ = v_ref_1720_;
v___y_1709_ = v_fileName_1717_;
v___y_1710_ = v___f_1724_;
v___y_1711_ = v_fileMap_1718_;
v___y_1712_ = v_suppressElabErrors_1721_;
v___y_1713_ = v___y_1716_;
v___y_1714_ = v___x_1728_;
goto v___jp_1707_;
}
}
else
{
lean_object* v___x_1729_; lean_object* v___x_1730_; 
lean_dec_ref(v_msgData_1614_);
v___x_1729_ = lean_box(0);
v___x_1730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1730_, 0, v___x_1729_);
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1733_, lean_object* v_msgData_1734_, lean_object* v_severity_1735_, lean_object* v_isSilent_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
uint8_t v_severity_boxed_1742_; uint8_t v_isSilent_boxed_1743_; lean_object* v_res_1744_; 
v_severity_boxed_1742_ = lean_unbox(v_severity_1735_);
v_isSilent_boxed_1743_ = lean_unbox(v_isSilent_1736_);
v_res_1744_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1(v_ref_1733_, v_msgData_1734_, v_severity_boxed_1742_, v_isSilent_boxed_1743_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v_ref_1733_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0(lean_object* v_msgData_1745_, uint8_t v_severity_1746_, uint8_t v_isSilent_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v_ref_1753_; lean_object* v___x_1754_; 
v_ref_1753_ = lean_ctor_get(v___y_1750_, 5);
v___x_1754_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1(v_ref_1753_, v_msgData_1745_, v_severity_1746_, v_isSilent_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0___boxed(lean_object* v_msgData_1755_, lean_object* v_severity_1756_, lean_object* v_isSilent_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_){
_start:
{
uint8_t v_severity_boxed_1763_; uint8_t v_isSilent_boxed_1764_; lean_object* v_res_1765_; 
v_severity_boxed_1763_ = lean_unbox(v_severity_1756_);
v_isSilent_boxed_1764_ = lean_unbox(v_isSilent_1757_);
v_res_1765_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0(v_msgData_1755_, v_severity_boxed_1763_, v_isSilent_boxed_1764_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
lean_dec(v___y_1761_);
lean_dec_ref(v___y_1760_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0(lean_object* v_msgData_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
uint8_t v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = 1;
v___x_1773_ = 0;
v___x_1774_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0(v_msgData_1766_, v___x_1772_, v___x_1773_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0___boxed(lean_object* v_msgData_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0(v_msgData_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
return v_res_1781_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2(void){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1785_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__1));
v___x_1786_ = l_Lean_MessageData_ofFormat(v___x_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig(lean_object* v_config_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_){
_start:
{
uint8_t v_leave_1793_; 
v_leave_1793_ = lean_ctor_get_uint8(v_config_1787_, sizeof(void*)*1 + 1);
if (v_leave_1793_ == 0)
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2);
v___x_1795_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0(v___x_1794_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_);
return v___x_1795_;
}
else
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___boxed(lean_object* v_config_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig(v_config_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
lean_dec(v_a_1802_);
lean_dec_ref(v_a_1801_);
lean_dec(v_a_1800_);
lean_dec_ref(v_a_1799_);
lean_dec_ref(v_config_1798_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams(lean_object* v_grindStx_1821_, lean_object* v_goal_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; uint8_t v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; uint8_t v___y_1851_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1854_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2));
lean_inc(v_grindStx_1821_);
v___x_1855_ = l_Lean_Syntax_isOfKind(v_grindStx_1821_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1856_; 
lean_dec(v_goal_1822_);
lean_dec(v_grindStx_1821_);
v___x_1856_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
return v___x_1856_;
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; 
v___x_1857_ = lean_unsigned_to_nat(1u);
v___x_1858_ = l_Lean_Syntax_getArg(v_grindStx_1821_, v___x_1857_);
v___x_1859_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__46));
lean_inc(v___x_1858_);
v___x_1860_ = l_Lean_Syntax_isOfKind(v___x_1858_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1896_; 
lean_dec(v___x_1858_);
lean_dec(v_goal_1822_);
lean_dec(v_grindStx_1821_);
v___x_1896_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v___y_1899_; lean_object* v_grindParams_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v_only_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___x_1933_; uint8_t v___x_1934_; 
v___x_1897_ = lean_unsigned_to_nat(2u);
v___x_1933_ = l_Lean_Syntax_getArg(v_grindStx_1821_, v___x_1897_);
v___x_1934_ = l_Lean_Syntax_isNone(v___x_1933_);
if (v___x_1934_ == 0)
{
uint8_t v___x_1935_; 
lean_inc(v___x_1933_);
v___x_1935_ = l_Lean_Syntax_matchesNull(v___x_1933_, v___x_1857_);
if (v___x_1935_ == 0)
{
lean_object* v___x_1936_; 
lean_dec(v___x_1933_);
lean_dec(v___x_1858_);
lean_dec(v_goal_1822_);
lean_dec(v_grindStx_1821_);
v___x_1936_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
return v___x_1936_;
}
else
{
lean_object* v___x_1937_; lean_object* v_only_1938_; lean_object* v___x_1939_; 
v___x_1937_ = lean_unsigned_to_nat(0u);
v_only_1938_ = l_Lean_Syntax_getArg(v___x_1933_, v___x_1937_);
lean_dec(v___x_1933_);
v___x_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1939_, 0, v_only_1938_);
v_only_1917_ = v___x_1939_;
v___y_1918_ = v_a_1823_;
v___y_1919_ = v_a_1824_;
v___y_1920_ = v_a_1825_;
v___y_1921_ = v_a_1826_;
v___y_1922_ = v_a_1827_;
v___y_1923_ = v_a_1828_;
goto v___jp_1916_;
}
}
else
{
lean_object* v___x_1940_; 
lean_dec(v___x_1933_);
v___x_1940_ = lean_box(0);
v_only_1917_ = v___x_1940_;
v___y_1918_ = v_a_1823_;
v___y_1919_ = v_a_1824_;
v___y_1920_ = v_a_1825_;
v___y_1921_ = v_a_1826_;
v___y_1922_ = v_a_1827_;
v___y_1923_ = v_a_1828_;
goto v___jp_1916_;
}
v___jp_1898_:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v___x_1907_ = lean_unsigned_to_nat(4u);
v___x_1908_ = l_Lean_Syntax_getArg(v_grindStx_1821_, v___x_1907_);
lean_dec(v_grindStx_1821_);
v___x_1909_ = l_Lean_Syntax_isNone(v___x_1908_);
if (v___x_1909_ == 0)
{
uint8_t v___x_1910_; 
lean_inc(v___x_1908_);
v___x_1910_ = l_Lean_Syntax_matchesNull(v___x_1908_, v___x_1897_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; 
lean_dec(v___x_1908_);
lean_dec(v_grindParams_1900_);
lean_dec(v___y_1899_);
lean_dec(v___x_1858_);
lean_dec(v_goal_1822_);
v___x_1911_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
return v___x_1911_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1912_ = l_Lean_Syntax_getArg(v___x_1908_, v___x_1857_);
lean_dec(v___x_1908_);
v___x_1913_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__5));
v___x_1914_ = l_Lean_Syntax_isOfKind(v___x_1912_, v___x_1913_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; 
lean_dec(v_grindParams_1900_);
lean_dec(v___y_1899_);
lean_dec(v___x_1858_);
lean_dec(v_goal_1822_);
v___x_1915_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
return v___x_1915_;
}
else
{
v___y_1862_ = v_grindParams_1900_;
v___y_1863_ = v___y_1899_;
v___y_1864_ = v___y_1901_;
v___y_1865_ = v___y_1902_;
v___y_1866_ = v___y_1903_;
v___y_1867_ = v___y_1904_;
v___y_1868_ = v___y_1905_;
v___y_1869_ = v___y_1906_;
goto v___jp_1861_;
}
}
}
else
{
lean_dec(v___x_1908_);
v___y_1862_ = v_grindParams_1900_;
v___y_1863_ = v___y_1899_;
v___y_1864_ = v___y_1901_;
v___y_1865_ = v___y_1902_;
v___y_1866_ = v___y_1903_;
v___y_1867_ = v___y_1904_;
v___y_1868_ = v___y_1905_;
v___y_1869_ = v___y_1906_;
goto v___jp_1861_;
}
}
v___jp_1916_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1924_ = lean_unsigned_to_nat(3u);
v___x_1925_ = l_Lean_Syntax_getArg(v_grindStx_1821_, v___x_1924_);
v___x_1926_ = l_Lean_Syntax_isNone(v___x_1925_);
if (v___x_1926_ == 0)
{
uint8_t v___x_1927_; 
lean_inc(v___x_1925_);
v___x_1927_ = l_Lean_Syntax_matchesNull(v___x_1925_, v___x_1924_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; 
lean_dec(v___x_1925_);
lean_dec(v_only_1917_);
lean_dec(v___x_1858_);
lean_dec(v_goal_1822_);
lean_dec(v_grindStx_1821_);
v___x_1928_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; lean_object* v_grindParams_1930_; lean_object* v___x_1931_; 
v___x_1929_ = l_Lean_Syntax_getArg(v___x_1925_, v___x_1857_);
lean_dec(v___x_1925_);
v_grindParams_1930_ = l_Lean_Syntax_getArgs(v___x_1929_);
lean_dec(v___x_1929_);
v___x_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1931_, 0, v_grindParams_1930_);
v___y_1899_ = v_only_1917_;
v_grindParams_1900_ = v___x_1931_;
v___y_1901_ = v___y_1918_;
v___y_1902_ = v___y_1919_;
v___y_1903_ = v___y_1920_;
v___y_1904_ = v___y_1921_;
v___y_1905_ = v___y_1922_;
v___y_1906_ = v___y_1923_;
goto v___jp_1898_;
}
}
else
{
lean_object* v___x_1932_; 
lean_dec(v___x_1925_);
v___x_1932_ = lean_box(0);
v___y_1899_ = v_only_1917_;
v_grindParams_1900_ = v___x_1932_;
v___y_1901_ = v___y_1918_;
v___y_1902_ = v___y_1919_;
v___y_1903_ = v___y_1920_;
v___y_1904_ = v___y_1921_;
v___y_1905_ = v___y_1922_;
v___y_1906_ = v___y_1923_;
goto v___jp_1898_;
}
}
}
v___jp_1861_:
{
uint8_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1870_ = 0;
v___x_1871_ = lean_unsigned_to_nat(9u);
v___x_1872_ = lean_unsigned_to_nat(5u);
v___x_1873_ = lean_unsigned_to_nat(8u);
v___x_1874_ = lean_unsigned_to_nat(1000u);
v___x_1875_ = lean_unsigned_to_nat(100000u);
v___x_1876_ = lean_unsigned_to_nat(1024u);
v___x_1877_ = lean_unsigned_to_nat(1048576u);
v___x_1878_ = lean_unsigned_to_nat(10u);
v___x_1879_ = lean_unsigned_to_nat(50u);
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_alloc_ctor(0, 13, 32);
lean_ctor_set(v___x_1881_, 0, v___x_1871_);
lean_ctor_set(v___x_1881_, 1, v___x_1872_);
lean_ctor_set(v___x_1881_, 2, v___x_1873_);
lean_ctor_set(v___x_1881_, 3, v___x_1873_);
lean_ctor_set(v___x_1881_, 4, v___x_1874_);
lean_ctor_set(v___x_1881_, 5, v___x_1874_);
lean_ctor_set(v___x_1881_, 6, v___x_1875_);
lean_ctor_set(v___x_1881_, 7, v___x_1876_);
lean_ctor_set(v___x_1881_, 8, v___x_1874_);
lean_ctor_set(v___x_1881_, 9, v___x_1877_);
lean_ctor_set(v___x_1881_, 10, v___x_1878_);
lean_ctor_set(v___x_1881_, 11, v___x_1879_);
lean_ctor_set(v___x_1881_, 12, v___x_1880_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13, v___x_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 1, v___x_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 2, v___x_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 3, v___x_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 4, v___x_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 5, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 6, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 7, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 8, v___x_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 9, v___x_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 10, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 11, v___x_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 12, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 13, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 14, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 15, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 16, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 17, v___x_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 18, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 19, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 20, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 21, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 22, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 23, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 24, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 25, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 26, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 27, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 28, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 29, v___x_1870_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 30, v___x_1860_);
lean_ctor_set_uint8(v___x_1881_, sizeof(void*)*13 + 31, v___x_1860_);
v___x_1882_ = lean_box(v___x_1860_);
v___x_1883_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabGrindConfig___boxed), 12, 3);
lean_closure_set(v___x_1883_, 0, v___x_1858_);
lean_closure_set(v___x_1883_, 1, v___x_1881_);
lean_closure_set(v___x_1883_, 2, v___x_1882_);
v___x_1884_ = lean_box(0);
v___x_1885_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg(v___x_1883_, v___x_1884_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_);
if (lean_obj_tag(v___x_1885_) == 0)
{
if (lean_obj_tag(v___y_1863_) == 0)
{
lean_object* v_a_1886_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___y_1843_ = v___y_1866_;
v___y_1844_ = v_a_1886_;
v___y_1845_ = v___y_1869_;
v___y_1846_ = v___y_1867_;
v___y_1847_ = v___y_1868_;
v___y_1848_ = v___y_1864_;
v___y_1849_ = v___y_1862_;
v___y_1850_ = v___y_1865_;
v___y_1851_ = v___x_1870_;
goto v___jp_1842_;
}
else
{
lean_object* v_a_1887_; 
lean_dec_ref_known(v___y_1863_, 1);
v_a_1887_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1887_);
lean_dec_ref_known(v___x_1885_, 1);
v___y_1843_ = v___y_1866_;
v___y_1844_ = v_a_1887_;
v___y_1845_ = v___y_1869_;
v___y_1846_ = v___y_1867_;
v___y_1847_ = v___y_1868_;
v___y_1848_ = v___y_1864_;
v___y_1849_ = v___y_1862_;
v___y_1850_ = v___y_1865_;
v___y_1851_ = v___x_1860_;
goto v___jp_1842_;
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec(v_goal_1822_);
v_a_1888_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1885_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1885_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
v___jp_1830_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = l_Lean_Syntax_TSepArray_getElems___redArg(v___y_1839_);
lean_dec_ref(v___y_1839_);
v___x_1841_ = l_Lean_Elab_Tactic_mkGrindParams(v___y_1832_, v___y_1835_, v___x_1840_, v_goal_1822_, v___y_1837_, v___y_1838_, v___y_1831_, v___y_1834_, v___y_1836_, v___y_1833_);
lean_dec_ref(v___x_1840_);
return v___x_1841_;
}
v___jp_1842_:
{
if (lean_obj_tag(v___y_1849_) == 0)
{
lean_object* v___x_1852_; 
v___x_1852_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__0));
v___y_1831_ = v___y_1843_;
v___y_1832_ = v___y_1844_;
v___y_1833_ = v___y_1845_;
v___y_1834_ = v___y_1846_;
v___y_1835_ = v___y_1851_;
v___y_1836_ = v___y_1847_;
v___y_1837_ = v___y_1848_;
v___y_1838_ = v___y_1850_;
v___y_1839_ = v___x_1852_;
goto v___jp_1830_;
}
else
{
lean_object* v_val_1853_; 
v_val_1853_ = lean_ctor_get(v___y_1849_, 0);
lean_inc(v_val_1853_);
lean_dec_ref_known(v___y_1849_, 1);
v___y_1831_ = v___y_1843_;
v___y_1832_ = v___y_1844_;
v___y_1833_ = v___y_1845_;
v___y_1834_ = v___y_1846_;
v___y_1835_ = v___y_1851_;
v___y_1836_ = v___y_1847_;
v___y_1837_ = v___y_1848_;
v___y_1838_ = v___y_1850_;
v___y_1839_ = v_val_1853_;
goto v___jp_1830_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___boxed(lean_object* v_grindStx_1941_, lean_object* v_goal_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams(v_grindStx_1941_, v_goal_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
lean_dec(v_a_1948_);
lean_dec_ref(v_a_1947_);
lean_dec(v_a_1946_);
lean_dec_ref(v_a_1945_);
lean_dec(v_a_1944_);
lean_dec_ref(v_a_1943_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0(lean_object* v_x_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1964_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0___closed__0));
v___x_1965_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v___x_1964_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0___boxed(lean_object* v_x_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0(v_x_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v___y_1968_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__1(lean_object* v___f_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_){
_start:
{
lean_object* v___x_1991_; 
lean_inc_ref(v___y_1980_);
v___x_1991_ = l_Lean_Meta_Sym_Simp_simpControl(v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1993_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_1992_);
v___x_1993_ = lean_box(0);
if (lean_obj_tag(v_a_1992_) == 0)
{
uint8_t v_done_1994_; 
v_done_1994_ = lean_ctor_get_uint8(v_a_1992_, 0);
if (v_done_1994_ == 0)
{
uint8_t v_contextDependent_1995_; lean_object* v___x_1996_; 
lean_dec_ref_known(v___x_1991_, 1);
v_contextDependent_1995_ = lean_ctor_get_uint8(v_a_1992_, 1);
lean_dec_ref_known(v_a_1992_, 0);
v___x_1996_ = lean_apply_12(v___f_1979_, v___x_1993_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, lean_box(0));
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; uint8_t v___y_1999_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
if (v_contextDependent_1995_ == 0)
{
lean_dec(v_a_1997_);
return v___x_1996_;
}
else
{
if (lean_obj_tag(v_a_1997_) == 0)
{
uint8_t v_contextDependent_2009_; 
v_contextDependent_2009_ = lean_ctor_get_uint8(v_a_1997_, 1);
v___y_1999_ = v_contextDependent_2009_;
goto v___jp_1998_;
}
else
{
uint8_t v_contextDependent_2010_; 
v_contextDependent_2010_ = lean_ctor_get_uint8(v_a_1997_, sizeof(void*)*2 + 1);
v___y_1999_ = v_contextDependent_2010_;
goto v___jp_1998_;
}
}
v___jp_1998_:
{
if (v___y_1999_ == 0)
{
lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2007_; 
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2007_ == 0)
{
lean_object* v_unused_2008_; 
v_unused_2008_ = lean_ctor_get(v___x_1996_, 0);
lean_dec(v_unused_2008_);
v___x_2001_ = v___x_1996_;
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
else
{
lean_dec(v___x_1996_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2007_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_2003_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1997_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
else
{
lean_dec(v_a_1997_);
return v___x_1996_;
}
}
}
else
{
return v___x_1996_;
}
}
else
{
lean_dec_ref_known(v_a_1992_, 0);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec_ref(v___f_1979_);
return v___x_1991_;
}
}
else
{
uint8_t v_done_2011_; 
v_done_2011_ = lean_ctor_get_uint8(v_a_1992_, sizeof(void*)*2);
if (v_done_2011_ == 0)
{
lean_object* v_e_x27_2012_; lean_object* v_proof_2013_; uint8_t v_contextDependent_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref_known(v___x_1991_, 1);
v_e_x27_2012_ = lean_ctor_get(v_a_1992_, 0);
v_proof_2013_ = lean_ctor_get(v_a_1992_, 1);
v_contextDependent_2014_ = lean_ctor_get_uint8(v_a_1992_, sizeof(void*)*2 + 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_a_1992_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2016_ = v_a_1992_;
v_isShared_2017_ = v_isSharedCheck_2064_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_proof_2013_);
lean_inc(v_e_x27_2012_);
lean_dec(v_a_1992_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2064_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; 
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v___y_1987_);
lean_inc_ref(v___y_1986_);
lean_inc(v___y_1985_);
lean_inc_ref(v_e_x27_2012_);
v___x_2018_ = lean_apply_12(v___f_1979_, v___x_1993_, v_e_x27_2012_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, lean_box(0));
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2063_; 
v_a_2019_ = lean_ctor_get(v___x_2018_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2021_ = v___x_2018_;
v_isShared_2022_ = v_isSharedCheck_2063_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_2018_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2063_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
if (lean_obj_tag(v_a_2019_) == 0)
{
uint8_t v_done_2023_; uint8_t v_contextDependent_2024_; uint8_t v___y_2026_; 
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1980_);
v_done_2023_ = lean_ctor_get_uint8(v_a_2019_, 0);
v_contextDependent_2024_ = lean_ctor_get_uint8(v_a_2019_, 1);
lean_dec_ref_known(v_a_2019_, 0);
if (v_contextDependent_2014_ == 0)
{
v___y_2026_ = v_contextDependent_2024_;
goto v___jp_2025_;
}
else
{
v___y_2026_ = v_contextDependent_2014_;
goto v___jp_2025_;
}
v___jp_2025_:
{
lean_object* v___x_2028_; 
if (v_isShared_2017_ == 0)
{
v___x_2028_ = v___x_2016_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_e_x27_2012_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v_proof_2013_);
v___x_2028_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2030_; 
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*2, v_done_2023_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*2 + 1, v___y_2026_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2028_);
v___x_2030_ = v___x_2021_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v_e_x27_2033_; lean_object* v_proof_2034_; uint8_t v_done_2035_; uint8_t v_contextDependent_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2062_; 
lean_del_object(v___x_2021_);
lean_del_object(v___x_2016_);
v_e_x27_2033_ = lean_ctor_get(v_a_2019_, 0);
v_proof_2034_ = lean_ctor_get(v_a_2019_, 1);
v_done_2035_ = lean_ctor_get_uint8(v_a_2019_, sizeof(void*)*2);
v_contextDependent_2036_ = lean_ctor_get_uint8(v_a_2019_, sizeof(void*)*2 + 1);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_a_2019_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2038_ = v_a_2019_;
v_isShared_2039_ = v_isSharedCheck_2062_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_proof_2034_);
lean_inc(v_e_x27_2033_);
lean_dec(v_a_2019_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2062_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; 
lean_inc_ref(v_e_x27_2033_);
v___x_2040_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_1980_, v_e_x27_2012_, v_proof_2013_, v_e_x27_2033_, v_proof_2034_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2053_; 
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2053_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2053_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
uint8_t v___y_2046_; 
if (v_contextDependent_2014_ == 0)
{
v___y_2046_ = v_contextDependent_2036_;
goto v___jp_2045_;
}
else
{
v___y_2046_ = v_contextDependent_2014_;
goto v___jp_2045_;
}
v___jp_2045_:
{
lean_object* v___x_2048_; 
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 1, v_a_2041_);
v___x_2048_ = v___x_2038_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_e_x27_2033_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_a_2041_);
lean_ctor_set_uint8(v_reuseFailAlloc_2052_, sizeof(void*)*2, v_done_2035_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*2 + 1, v___y_2046_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 0, v___x_2048_);
v___x_2050_ = v___x_2043_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_del_object(v___x_2038_);
lean_dec_ref(v_e_x27_2033_);
v_a_2054_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2040_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2040_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2016_);
lean_dec_ref(v_proof_2013_);
lean_dec_ref(v_e_x27_2012_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1980_);
return v___x_2018_;
}
}
}
else
{
lean_dec_ref_known(v_a_1992_, 2);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec_ref(v___f_1979_);
return v___x_1991_;
}
}
}
else
{
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec_ref(v___f_1979_);
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__1___boxed(lean_object* v___f_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__1(v___f_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2(lean_object* v_a_2079_, lean_object* v_x_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2092_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___closed__0));
v___x_2093_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_2079_, v___x_2092_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___boxed(lean_object* v_a_2094_, lean_object* v_x_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2(v_a_2094_, v_x_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v_a_2094_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__4(lean_object* v___f_2108_, lean_object* v___x_2109_, lean_object* v___f_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v___y_2123_; lean_object* v___y_2124_; uint8_t v___y_2125_; uint8_t v___y_2126_; lean_object* v___y_2130_; uint8_t v___y_2131_; lean_object* v___y_2132_; uint8_t v___y_2133_; lean_object* v___y_2137_; lean_object* v_e_x27_2138_; lean_object* v_proof_2139_; uint8_t v_done_2140_; uint8_t v_contextDependent_2141_; lean_object* v___y_2164_; lean_object* v___y_2165_; uint8_t v___y_2166_; lean_object* v___y_2170_; lean_object* v_a_2171_; lean_object* v___y_2184_; lean_object* v___x_2186_; 
lean_inc_ref(v___y_2111_);
v___x_2186_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_2109_, v___y_2111_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; lean_object* v___x_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
v___x_2188_ = lean_box(0);
if (lean_obj_tag(v_a_2187_) == 0)
{
uint8_t v_done_2189_; 
v_done_2189_ = lean_ctor_get_uint8(v_a_2187_, 0);
if (v_done_2189_ == 0)
{
uint8_t v_contextDependent_2190_; lean_object* v___x_2191_; 
lean_dec_ref_known(v___x_2186_, 1);
v_contextDependent_2190_ = lean_ctor_get_uint8(v_a_2187_, 1);
lean_dec_ref_known(v_a_2187_, 0);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc(v___y_2118_);
lean_inc_ref(v___y_2117_);
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v___y_2111_);
v___x_2191_ = lean_apply_12(v___f_2110_, v___x_2188_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, lean_box(0));
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v_a_2192_; uint8_t v___y_2194_; 
v_a_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_a_2192_);
if (v_contextDependent_2190_ == 0)
{
v___y_2170_ = v___x_2191_;
v_a_2171_ = v_a_2192_;
goto v___jp_2169_;
}
else
{
if (lean_obj_tag(v_a_2192_) == 0)
{
uint8_t v_contextDependent_2204_; 
v_contextDependent_2204_ = lean_ctor_get_uint8(v_a_2192_, 1);
v___y_2194_ = v_contextDependent_2204_;
goto v___jp_2193_;
}
else
{
uint8_t v_contextDependent_2205_; 
v_contextDependent_2205_ = lean_ctor_get_uint8(v_a_2192_, sizeof(void*)*2 + 1);
v___y_2194_ = v_contextDependent_2205_;
goto v___jp_2193_;
}
}
v___jp_2193_:
{
if (v___y_2194_ == 0)
{
lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2202_; 
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; 
v_unused_2203_ = lean_ctor_get(v___x_2191_, 0);
lean_dec(v_unused_2203_);
v___x_2196_ = v___x_2191_;
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
else
{
lean_dec(v___x_2191_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2202_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2192_);
lean_inc_ref(v___x_2198_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v___x_2198_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
v___y_2170_ = v___x_2200_;
v_a_2171_ = v___x_2198_;
goto v___jp_2169_;
}
}
}
else
{
v___y_2170_ = v___x_2191_;
v_a_2171_ = v_a_2192_;
goto v___jp_2169_;
}
}
}
else
{
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___f_2108_);
return v___x_2191_;
}
}
else
{
lean_dec_ref_known(v_a_2187_, 0);
lean_dec_ref(v___f_2110_);
v___y_2184_ = v___x_2186_;
goto v___jp_2183_;
}
}
else
{
uint8_t v_done_2206_; 
v_done_2206_ = lean_ctor_get_uint8(v_a_2187_, sizeof(void*)*2);
if (v_done_2206_ == 0)
{
lean_object* v_e_x27_2207_; lean_object* v_proof_2208_; uint8_t v_contextDependent_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2259_; 
lean_dec_ref_known(v___x_2186_, 1);
v_e_x27_2207_ = lean_ctor_get(v_a_2187_, 0);
v_proof_2208_ = lean_ctor_get(v_a_2187_, 1);
v_contextDependent_2209_ = lean_ctor_get_uint8(v_a_2187_, sizeof(void*)*2 + 1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_a_2187_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2211_ = v_a_2187_;
v_isShared_2212_ = v_isSharedCheck_2259_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_proof_2208_);
lean_inc(v_e_x27_2207_);
lean_dec(v_a_2187_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2259_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2213_; 
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc(v___y_2118_);
lean_inc_ref(v___y_2117_);
lean_inc(v___y_2116_);
lean_inc_ref(v___y_2115_);
lean_inc(v___y_2114_);
lean_inc_ref(v___y_2113_);
lean_inc(v___y_2112_);
lean_inc_ref(v_e_x27_2207_);
v___x_2213_ = lean_apply_12(v___f_2110_, v___x_2188_, v_e_x27_2207_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, lean_box(0));
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2258_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2216_ = v___x_2213_;
v_isShared_2217_ = v_isSharedCheck_2258_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2213_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2258_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
if (lean_obj_tag(v_a_2214_) == 0)
{
uint8_t v_done_2218_; uint8_t v_contextDependent_2219_; uint8_t v___y_2221_; 
v_done_2218_ = lean_ctor_get_uint8(v_a_2214_, 0);
v_contextDependent_2219_ = lean_ctor_get_uint8(v_a_2214_, 1);
lean_dec_ref_known(v_a_2214_, 0);
if (v_contextDependent_2209_ == 0)
{
v___y_2221_ = v_contextDependent_2219_;
goto v___jp_2220_;
}
else
{
v___y_2221_ = v_contextDependent_2209_;
goto v___jp_2220_;
}
v___jp_2220_:
{
lean_object* v___x_2223_; 
lean_inc_ref(v_proof_2208_);
lean_inc_ref(v_e_x27_2207_);
if (v_isShared_2212_ == 0)
{
v___x_2223_ = v___x_2211_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_e_x27_2207_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_proof_2208_);
v___x_2223_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2225_; 
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*2, v_done_2218_);
lean_ctor_set_uint8(v___x_2223_, sizeof(void*)*2 + 1, v___y_2221_);
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 0, v___x_2223_);
v___x_2225_ = v___x_2216_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
v___y_2137_ = v___x_2225_;
v_e_x27_2138_ = v_e_x27_2207_;
v_proof_2139_ = v_proof_2208_;
v_done_2140_ = v_done_2218_;
v_contextDependent_2141_ = v___y_2221_;
goto v___jp_2136_;
}
}
}
}
else
{
lean_object* v_e_x27_2228_; lean_object* v_proof_2229_; uint8_t v_done_2230_; uint8_t v_contextDependent_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2257_; 
lean_del_object(v___x_2216_);
lean_del_object(v___x_2211_);
v_e_x27_2228_ = lean_ctor_get(v_a_2214_, 0);
v_proof_2229_ = lean_ctor_get(v_a_2214_, 1);
v_done_2230_ = lean_ctor_get_uint8(v_a_2214_, sizeof(void*)*2);
v_contextDependent_2231_ = lean_ctor_get_uint8(v_a_2214_, sizeof(void*)*2 + 1);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_a_2214_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2233_ = v_a_2214_;
v_isShared_2234_ = v_isSharedCheck_2257_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_proof_2229_);
lean_inc(v_e_x27_2228_);
lean_dec(v_a_2214_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2257_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2235_; 
lean_inc_ref(v_e_x27_2228_);
lean_inc_ref(v___y_2111_);
v___x_2235_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2111_, v_e_x27_2207_, v_proof_2208_, v_e_x27_2228_, v_proof_2229_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2248_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2248_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2248_ == 0)
{
v___x_2238_ = v___x_2235_;
v_isShared_2239_ = v_isSharedCheck_2248_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_a_2236_);
lean_dec(v___x_2235_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2248_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
uint8_t v___y_2241_; 
if (v_contextDependent_2209_ == 0)
{
v___y_2241_ = v_contextDependent_2231_;
goto v___jp_2240_;
}
else
{
v___y_2241_ = v_contextDependent_2209_;
goto v___jp_2240_;
}
v___jp_2240_:
{
lean_object* v___x_2243_; 
lean_inc(v_a_2236_);
lean_inc_ref(v_e_x27_2228_);
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 1, v_a_2236_);
v___x_2243_ = v___x_2233_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2247_; 
v_reuseFailAlloc_2247_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_e_x27_2228_);
lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_a_2236_);
lean_ctor_set_uint8(v_reuseFailAlloc_2247_, sizeof(void*)*2, v_done_2230_);
v___x_2243_ = v_reuseFailAlloc_2247_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
lean_object* v___x_2245_; 
lean_ctor_set_uint8(v___x_2243_, sizeof(void*)*2 + 1, v___y_2241_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 0, v___x_2243_);
v___x_2245_ = v___x_2238_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2243_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
v___y_2137_ = v___x_2245_;
v_e_x27_2138_ = v_e_x27_2228_;
v_proof_2139_ = v_a_2236_;
v_done_2140_ = v_done_2230_;
v_contextDependent_2141_ = v___y_2241_;
goto v___jp_2136_;
}
}
}
}
}
else
{
lean_object* v_a_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
lean_del_object(v___x_2233_);
lean_dec_ref(v_e_x27_2228_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___f_2108_);
v_a_2249_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v___x_2235_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_a_2249_);
lean_dec(v___x_2235_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_a_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2211_);
lean_dec_ref(v_proof_2208_);
lean_dec_ref(v_e_x27_2207_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___f_2108_);
return v___x_2213_;
}
}
}
else
{
lean_dec_ref_known(v_a_2187_, 2);
lean_dec_ref(v___f_2110_);
v___y_2184_ = v___x_2186_;
goto v___jp_2183_;
}
}
}
else
{
lean_dec_ref(v___f_2110_);
v___y_2184_ = v___x_2186_;
goto v___jp_2183_;
}
v___jp_2122_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2127_, 0, v___y_2124_);
lean_ctor_set(v___x_2127_, 1, v___y_2123_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*2, v___y_2125_);
lean_ctor_set_uint8(v___x_2127_, sizeof(void*)*2 + 1, v___y_2126_);
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
v___jp_2129_:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2134_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2134_, 0, v___y_2132_);
lean_ctor_set(v___x_2134_, 1, v___y_2130_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*2, v___y_2131_);
lean_ctor_set_uint8(v___x_2134_, sizeof(void*)*2 + 1, v___y_2133_);
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
return v___x_2135_;
}
v___jp_2136_:
{
if (v_done_2140_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec_ref(v___y_2137_);
v___x_2142_ = lean_box(0);
lean_inc(v___y_2120_);
lean_inc_ref(v___y_2119_);
lean_inc(v___y_2118_);
lean_inc_ref(v___y_2117_);
lean_inc(v___y_2116_);
lean_inc_ref(v_e_x27_2138_);
v___x_2143_ = lean_apply_12(v___f_2108_, v___x_2142_, v_e_x27_2138_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, lean_box(0));
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
if (lean_obj_tag(v_a_2144_) == 0)
{
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2111_);
if (v_contextDependent_2141_ == 0)
{
uint8_t v_done_2145_; uint8_t v_contextDependent_2146_; 
v_done_2145_ = lean_ctor_get_uint8(v_a_2144_, 0);
v_contextDependent_2146_ = lean_ctor_get_uint8(v_a_2144_, 1);
lean_dec_ref_known(v_a_2144_, 0);
v___y_2123_ = v_proof_2139_;
v___y_2124_ = v_e_x27_2138_;
v___y_2125_ = v_done_2145_;
v___y_2126_ = v_contextDependent_2146_;
goto v___jp_2122_;
}
else
{
uint8_t v_done_2147_; 
v_done_2147_ = lean_ctor_get_uint8(v_a_2144_, 0);
lean_dec_ref_known(v_a_2144_, 0);
v___y_2123_ = v_proof_2139_;
v___y_2124_ = v_e_x27_2138_;
v___y_2125_ = v_done_2147_;
v___y_2126_ = v_contextDependent_2141_;
goto v___jp_2122_;
}
}
else
{
lean_object* v_e_x27_2148_; lean_object* v_proof_2149_; uint8_t v_done_2150_; uint8_t v_contextDependent_2151_; lean_object* v___x_2152_; 
v_e_x27_2148_ = lean_ctor_get(v_a_2144_, 0);
lean_inc_ref_n(v_e_x27_2148_, 2);
v_proof_2149_ = lean_ctor_get(v_a_2144_, 1);
lean_inc_ref(v_proof_2149_);
v_done_2150_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*2);
v_contextDependent_2151_ = lean_ctor_get_uint8(v_a_2144_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2144_, 2);
v___x_2152_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2111_, v_e_x27_2138_, v_proof_2139_, v_e_x27_2148_, v_proof_2149_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
if (lean_obj_tag(v___x_2152_) == 0)
{
if (v_contextDependent_2141_ == 0)
{
lean_object* v_a_2153_; 
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2153_);
lean_dec_ref_known(v___x_2152_, 1);
v___y_2130_ = v_a_2153_;
v___y_2131_ = v_done_2150_;
v___y_2132_ = v_e_x27_2148_;
v___y_2133_ = v_contextDependent_2151_;
goto v___jp_2129_;
}
else
{
lean_object* v_a_2154_; 
v_a_2154_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_a_2154_);
lean_dec_ref_known(v___x_2152_, 1);
v___y_2130_ = v_a_2154_;
v___y_2131_ = v_done_2150_;
v___y_2132_ = v_e_x27_2148_;
v___y_2133_ = v_contextDependent_2141_;
goto v___jp_2129_;
}
}
else
{
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec_ref(v_e_x27_2148_);
v_a_2155_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2152_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2152_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_2139_);
lean_dec_ref(v_e_x27_2138_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2111_);
return v___x_2143_;
}
}
else
{
lean_dec_ref(v_proof_2139_);
lean_dec_ref(v_e_x27_2138_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___f_2108_);
return v___y_2137_;
}
}
v___jp_2163_:
{
if (v___y_2166_ == 0)
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec_ref(v___y_2164_);
v___x_2167_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_2165_);
v___x_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2167_);
return v___x_2168_;
}
else
{
lean_dec_ref(v___y_2165_);
return v___y_2164_;
}
}
v___jp_2169_:
{
if (lean_obj_tag(v_a_2171_) == 0)
{
uint8_t v_done_2172_; 
v_done_2172_ = lean_ctor_get_uint8(v_a_2171_, 0);
if (v_done_2172_ == 0)
{
uint8_t v_contextDependent_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v___y_2170_);
v_contextDependent_2173_ = lean_ctor_get_uint8(v_a_2171_, 1);
lean_dec_ref_known(v_a_2171_, 0);
v___x_2174_ = lean_box(0);
v___x_2175_ = lean_apply_12(v___f_2108_, v___x_2174_, v___y_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_, v___y_2120_, lean_box(0));
if (lean_obj_tag(v___x_2175_) == 0)
{
if (v_contextDependent_2173_ == 0)
{
return v___x_2175_;
}
else
{
lean_object* v_a_2176_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
if (lean_obj_tag(v_a_2176_) == 0)
{
uint8_t v_contextDependent_2177_; 
v_contextDependent_2177_ = lean_ctor_get_uint8(v_a_2176_, 1);
v___y_2164_ = v___x_2175_;
v___y_2165_ = v_a_2176_;
v___y_2166_ = v_contextDependent_2177_;
goto v___jp_2163_;
}
else
{
uint8_t v_contextDependent_2178_; 
v_contextDependent_2178_ = lean_ctor_get_uint8(v_a_2176_, sizeof(void*)*2 + 1);
v___y_2164_ = v___x_2175_;
v___y_2165_ = v_a_2176_;
v___y_2166_ = v_contextDependent_2178_;
goto v___jp_2163_;
}
}
}
else
{
return v___x_2175_;
}
}
else
{
lean_dec_ref_known(v_a_2171_, 0);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___f_2108_);
return v___y_2170_;
}
}
else
{
lean_object* v_e_x27_2179_; lean_object* v_proof_2180_; uint8_t v_done_2181_; uint8_t v_contextDependent_2182_; 
v_e_x27_2179_ = lean_ctor_get(v_a_2171_, 0);
lean_inc_ref(v_e_x27_2179_);
v_proof_2180_ = lean_ctor_get(v_a_2171_, 1);
lean_inc_ref(v_proof_2180_);
v_done_2181_ = lean_ctor_get_uint8(v_a_2171_, sizeof(void*)*2);
v_contextDependent_2182_ = lean_ctor_get_uint8(v_a_2171_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_2171_, 2);
v___y_2137_ = v___y_2170_;
v_e_x27_2138_ = v_e_x27_2179_;
v_proof_2139_ = v_proof_2180_;
v_done_2140_ = v_done_2181_;
v_contextDependent_2141_ = v_contextDependent_2182_;
goto v___jp_2136_;
}
}
v___jp_2183_:
{
if (lean_obj_tag(v___y_2184_) == 0)
{
lean_object* v_a_2185_; 
v_a_2185_ = lean_ctor_get(v___y_2184_, 0);
lean_inc(v_a_2185_);
v___y_2170_ = v___y_2184_;
v_a_2171_ = v_a_2185_;
goto v___jp_2169_;
}
else
{
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___f_2108_);
return v___y_2184_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__4___boxed(lean_object* v___f_2260_, lean_object* v___x_2261_, lean_object* v___f_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__4(v___f_2260_, v___x_2261_, v___f_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___x_2261_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__3(lean_object* v___x_2275_, lean_object* v___f_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
lean_inc_ref(v___y_2277_);
v___x_2288_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_2275_, v___y_2277_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2290_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
v___x_2290_ = lean_box(0);
if (lean_obj_tag(v_a_2289_) == 0)
{
uint8_t v_done_2291_; 
v_done_2291_ = lean_ctor_get_uint8(v_a_2289_, 0);
if (v_done_2291_ == 0)
{
uint8_t v_contextDependent_2292_; lean_object* v___x_2293_; 
lean_dec_ref_known(v___x_2288_, 1);
v_contextDependent_2292_ = lean_ctor_get_uint8(v_a_2289_, 1);
lean_dec_ref_known(v_a_2289_, 0);
v___x_2293_ = lean_apply_12(v___f_2276_, v___x_2290_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, lean_box(0));
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; uint8_t v___y_2296_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_a_2294_);
if (v_contextDependent_2292_ == 0)
{
lean_dec(v_a_2294_);
return v___x_2293_;
}
else
{
if (lean_obj_tag(v_a_2294_) == 0)
{
uint8_t v_contextDependent_2306_; 
v_contextDependent_2306_ = lean_ctor_get_uint8(v_a_2294_, 1);
v___y_2296_ = v_contextDependent_2306_;
goto v___jp_2295_;
}
else
{
uint8_t v_contextDependent_2307_; 
v_contextDependent_2307_ = lean_ctor_get_uint8(v_a_2294_, sizeof(void*)*2 + 1);
v___y_2296_ = v_contextDependent_2307_;
goto v___jp_2295_;
}
}
v___jp_2295_:
{
if (v___y_2296_ == 0)
{
lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2304_; 
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2304_ == 0)
{
lean_object* v_unused_2305_; 
v_unused_2305_ = lean_ctor_get(v___x_2293_, 0);
lean_dec(v_unused_2305_);
v___x_2298_ = v___x_2293_;
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
else
{
lean_dec(v___x_2293_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_2294_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v___x_2300_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
else
{
lean_dec(v_a_2294_);
return v___x_2293_;
}
}
}
else
{
return v___x_2293_;
}
}
else
{
lean_dec_ref_known(v_a_2289_, 0);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v___f_2276_);
return v___x_2288_;
}
}
else
{
uint8_t v_done_2308_; 
v_done_2308_ = lean_ctor_get_uint8(v_a_2289_, sizeof(void*)*2);
if (v_done_2308_ == 0)
{
lean_object* v_e_x27_2309_; lean_object* v_proof_2310_; uint8_t v_contextDependent_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref_known(v___x_2288_, 1);
v_e_x27_2309_ = lean_ctor_get(v_a_2289_, 0);
v_proof_2310_ = lean_ctor_get(v_a_2289_, 1);
v_contextDependent_2311_ = lean_ctor_get_uint8(v_a_2289_, sizeof(void*)*2 + 1);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_a_2289_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2313_ = v_a_2289_;
v_isShared_2314_ = v_isSharedCheck_2361_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_proof_2310_);
lean_inc(v_e_x27_2309_);
lean_dec(v_a_2289_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2361_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; 
lean_inc(v___y_2286_);
lean_inc_ref(v___y_2285_);
lean_inc(v___y_2284_);
lean_inc_ref(v___y_2283_);
lean_inc(v___y_2282_);
lean_inc_ref(v_e_x27_2309_);
v___x_2315_ = lean_apply_12(v___f_2276_, v___x_2290_, v_e_x27_2309_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, lean_box(0));
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2360_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2360_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2360_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
if (lean_obj_tag(v_a_2316_) == 0)
{
uint8_t v_done_2320_; uint8_t v_contextDependent_2321_; uint8_t v___y_2323_; 
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2277_);
v_done_2320_ = lean_ctor_get_uint8(v_a_2316_, 0);
v_contextDependent_2321_ = lean_ctor_get_uint8(v_a_2316_, 1);
lean_dec_ref_known(v_a_2316_, 0);
if (v_contextDependent_2311_ == 0)
{
v___y_2323_ = v_contextDependent_2321_;
goto v___jp_2322_;
}
else
{
v___y_2323_ = v_contextDependent_2311_;
goto v___jp_2322_;
}
v___jp_2322_:
{
lean_object* v___x_2325_; 
if (v_isShared_2314_ == 0)
{
v___x_2325_ = v___x_2313_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_e_x27_2309_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v_proof_2310_);
v___x_2325_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
lean_object* v___x_2327_; 
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*2, v_done_2320_);
lean_ctor_set_uint8(v___x_2325_, sizeof(void*)*2 + 1, v___y_2323_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2325_);
v___x_2327_ = v___x_2318_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
else
{
lean_object* v_e_x27_2330_; lean_object* v_proof_2331_; uint8_t v_done_2332_; uint8_t v_contextDependent_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2359_; 
lean_del_object(v___x_2318_);
lean_del_object(v___x_2313_);
v_e_x27_2330_ = lean_ctor_get(v_a_2316_, 0);
v_proof_2331_ = lean_ctor_get(v_a_2316_, 1);
v_done_2332_ = lean_ctor_get_uint8(v_a_2316_, sizeof(void*)*2);
v_contextDependent_2333_ = lean_ctor_get_uint8(v_a_2316_, sizeof(void*)*2 + 1);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_a_2316_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2335_ = v_a_2316_;
v_isShared_2336_ = v_isSharedCheck_2359_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_proof_2331_);
lean_inc(v_e_x27_2330_);
lean_dec(v_a_2316_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2359_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; 
lean_inc_ref(v_e_x27_2330_);
v___x_2337_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_2277_, v_e_x27_2309_, v_proof_2310_, v_e_x27_2330_, v_proof_2331_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2350_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2340_ = v___x_2337_;
v_isShared_2341_ = v_isSharedCheck_2350_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_a_2338_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2350_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
uint8_t v___y_2343_; 
if (v_contextDependent_2311_ == 0)
{
v___y_2343_ = v_contextDependent_2333_;
goto v___jp_2342_;
}
else
{
v___y_2343_ = v_contextDependent_2311_;
goto v___jp_2342_;
}
v___jp_2342_:
{
lean_object* v___x_2345_; 
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 1, v_a_2338_);
v___x_2345_ = v___x_2335_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_e_x27_2330_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_a_2338_);
lean_ctor_set_uint8(v_reuseFailAlloc_2349_, sizeof(void*)*2, v_done_2332_);
v___x_2345_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
lean_object* v___x_2347_; 
lean_ctor_set_uint8(v___x_2345_, sizeof(void*)*2 + 1, v___y_2343_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2345_);
v___x_2347_ = v___x_2340_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2345_);
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
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_del_object(v___x_2335_);
lean_dec_ref(v_e_x27_2330_);
v_a_2351_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2337_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2337_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_2313_);
lean_dec_ref(v_proof_2310_);
lean_dec_ref(v_e_x27_2309_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2277_);
return v___x_2315_;
}
}
}
else
{
lean_dec_ref_known(v_a_2289_, 2);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v___f_2276_);
return v___x_2288_;
}
}
}
else
{
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v___y_2280_);
lean_dec_ref(v___y_2279_);
lean_dec(v___y_2278_);
lean_dec_ref(v___y_2277_);
lean_dec_ref(v___f_2276_);
return v___x_2288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__3___boxed(lean_object* v___x_2362_, lean_object* v___f_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__3(v___x_2362_, v___f_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
lean_dec(v___x_2362_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg(lean_object* v_msg_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_ref_2382_; lean_object* v___x_2383_; lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2392_; 
v_ref_2382_ = lean_ctor_get(v___y_2379_, 5);
v___x_2383_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v_msg_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2392_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2392_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2390_; 
lean_inc(v_ref_2382_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v_ref_2382_);
lean_ctor_set(v___x_2388_, 1, v_a_2384_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set_tag(v___x_2386_, 1);
lean_ctor_set(v___x_2386_, 0, v___x_2388_);
v___x_2390_ = v___x_2386_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v___x_2388_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg___boxed(lean_object* v_msg_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg(v_msg_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
lean_dec(v___y_2397_);
lean_dec_ref(v___y_2396_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg(lean_object* v_as_2400_, size_t v_sz_2401_, size_t v_i_2402_, lean_object* v_b_2403_){
_start:
{
uint8_t v___x_2405_; 
v___x_2405_ = lean_usize_dec_lt(v_i_2402_, v_sz_2401_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v_b_2403_);
return v___x_2406_;
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2408_; size_t v___x_2409_; size_t v___x_2410_; 
v_a_2407_ = lean_array_uget_borrowed(v_as_2400_, v_i_2402_);
lean_inc(v_a_2407_);
v___x_2408_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_2403_, v_a_2407_);
v___x_2409_ = ((size_t)1ULL);
v___x_2410_ = lean_usize_add(v_i_2402_, v___x_2409_);
v_i_2402_ = v___x_2410_;
v_b_2403_ = v___x_2408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg___boxed(lean_object* v_as_2412_, lean_object* v_sz_2413_, lean_object* v_i_2414_, lean_object* v_b_2415_, lean_object* v___y_2416_){
_start:
{
size_t v_sz_boxed_2417_; size_t v_i_boxed_2418_; lean_object* v_res_2419_; 
v_sz_boxed_2417_ = lean_unbox_usize(v_sz_2413_);
lean_dec(v_sz_2413_);
v_i_boxed_2418_ = lean_unbox_usize(v_i_2414_);
lean_dec(v_i_2414_);
v_res_2419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg(v_as_2412_, v_sz_boxed_2417_, v_i_boxed_2418_, v_b_2415_);
lean_dec_ref(v_as_2412_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__1(lean_object* v___x_2420_, lean_object* v_as_2421_, size_t v_sz_2422_, size_t v_i_2423_, lean_object* v_b_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_a_2431_; uint8_t v___x_2435_; 
v___x_2435_ = lean_usize_dec_lt(v_i_2423_, v_sz_2422_);
if (v___x_2435_ == 0)
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v_b_2424_);
return v___x_2436_;
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v_a_2437_ = lean_array_uget_borrowed(v_as_2421_, v_i_2423_);
v___x_2438_ = l_Lean_TSyntax_getId(v_a_2437_);
v___x_2439_ = l_Lean_LocalContext_findFromUserName_x3f(v___x_2420_, v___x_2438_);
lean_dec(v___x_2438_);
if (lean_obj_tag(v___x_2439_) == 1)
{
lean_object* v_val_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_val_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc(v_val_2440_);
lean_dec_ref_known(v___x_2439_, 1);
v___x_2441_ = l_Lean_LocalDecl_toExpr(v_val_2440_);
v___x_2442_ = l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(v___x_2441_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2444_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_a_2443_);
lean_dec_ref_known(v___x_2442_, 1);
v___x_2444_ = lean_array_push(v_b_2424_, v_a_2443_);
v_a_2431_ = v___x_2444_;
goto v___jp_2430_;
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v_b_2424_);
v_a_2445_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2442_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2442_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_object* v___x_2453_; 
lean_dec(v___x_2439_);
lean_inc(v_a_2437_);
v___x_2453_ = l_Lean_realizeGlobalConstNoOverload(v_a_2437_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2455_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2455_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_a_2454_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2457_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2457_ = lean_array_push(v_b_2424_, v_a_2456_);
v_a_2431_ = v___x_2457_;
goto v___jp_2430_;
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec_ref(v_b_2424_);
v_a_2458_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2455_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2455_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v_b_2424_);
v_a_2466_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2453_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2453_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
v___jp_2430_:
{
size_t v___x_2432_; size_t v___x_2433_; 
v___x_2432_ = ((size_t)1ULL);
v___x_2433_ = lean_usize_add(v_i_2423_, v___x_2432_);
v_i_2423_ = v___x_2433_;
v_b_2424_ = v_a_2431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__1___boxed(lean_object* v___x_2474_, lean_object* v_as_2475_, lean_object* v_sz_2476_, lean_object* v_i_2477_, lean_object* v_b_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
size_t v_sz_boxed_2484_; size_t v_i_boxed_2485_; lean_object* v_res_2486_; 
v_sz_boxed_2484_ = lean_unbox_usize(v_sz_2476_);
lean_dec(v_sz_2476_);
v_i_boxed_2485_ = lean_unbox_usize(v_i_2477_);
lean_dec(v_i_2477_);
v_res_2486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__1(v___x_2474_, v_as_2475_, v_sz_boxed_2484_, v_i_boxed_2485_, v_b_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec_ref(v_as_2475_);
lean_dec_ref(v___x_2474_);
return v_res_2486_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__2(void){
_start:
{
lean_object* v___x_2490_; 
v___x_2490_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2490_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__3(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__2);
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
return v___x_2492_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__6(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__5));
v___x_2497_ = l_Lean_stringToMessageData(v___x_2496_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts(lean_object* v_variantId_x3f_2498_, lean_object* v_extraIds_x3f_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v___f_2505_; lean_object* v_post_2507_; lean_object* v_extraThms_2511_; lean_object* v___y_2512_; lean_object* v___y_2513_; lean_object* v___y_2514_; lean_object* v___y_2515_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2568_; 
v___f_2505_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__1));
if (lean_obj_tag(v_variantId_x3f_2498_) == 0)
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_box(0);
v___y_2568_ = v___x_2580_;
goto v___jp_2567_;
}
else
{
lean_object* v_val_2581_; lean_object* v___x_2582_; 
v_val_2581_ = lean_ctor_get(v_variantId_x3f_2498_, 0);
v___x_2582_ = l_Lean_TSyntax_getId(v_val_2581_);
v___y_2568_ = v___x_2582_;
goto v___jp_2567_;
}
v___jp_2506_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___f_2505_);
lean_ctor_set(v___x_2508_, 1, v_post_2507_);
v___x_2509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2508_);
return v___x_2509_;
}
v___jp_2510_:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v___y_2515_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___f_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; uint8_t v___x_2522_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___f_2518_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___boxed), 13, 1);
lean_closure_set(v___f_2518_, 0, v_a_2517_);
v___x_2519_ = lean_unsigned_to_nat(255u);
v___x_2520_ = lean_array_get_size(v_extraThms_2511_);
v___x_2521_ = lean_unsigned_to_nat(0u);
v___x_2522_ = lean_nat_dec_eq(v___x_2520_, v___x_2521_);
if (v___x_2522_ == 0)
{
lean_object* v___x_2523_; size_t v_sz_2524_; size_t v___x_2525_; lean_object* v___x_2526_; 
v___x_2523_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__3);
v_sz_2524_ = lean_array_size(v_extraThms_2511_);
v___x_2525_ = ((size_t)0ULL);
v___x_2526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg(v_extraThms_2511_, v_sz_2524_, v___x_2525_, v___x_2523_);
lean_dec_ref(v_extraThms_2511_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_object* v_a_2527_; lean_object* v___f_2528_; lean_object* v___f_2529_; 
v_a_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_a_2527_);
lean_dec_ref_known(v___x_2526_, 1);
v___f_2528_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___boxed), 13, 1);
lean_closure_set(v___f_2528_, 0, v_a_2527_);
v___f_2529_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__4___boxed), 14, 3);
lean_closure_set(v___f_2529_, 0, v___f_2528_);
lean_closure_set(v___f_2529_, 1, v___x_2519_);
lean_closure_set(v___f_2529_, 2, v___f_2518_);
v_post_2507_ = v___f_2529_;
goto v___jp_2506_;
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref(v___f_2518_);
v_a_2530_ = lean_ctor_get(v___x_2526_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2526_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2526_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2526_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v___f_2538_; 
lean_dec_ref(v_extraThms_2511_);
v___f_2538_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__3___boxed), 13, 2);
lean_closure_set(v___f_2538_, 0, v___x_2519_);
lean_closure_set(v___f_2538_, 1, v___f_2518_);
v_post_2507_ = v___f_2538_;
goto v___jp_2506_;
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec_ref(v_extraThms_2511_);
v_a_2539_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2516_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2516_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
v___jp_2547_:
{
lean_object* v_extraThms_2552_; 
v_extraThms_2552_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__4));
if (lean_obj_tag(v_extraIds_x3f_2499_) == 1)
{
lean_object* v_val_2553_; lean_object* v_lctx_2554_; size_t v_sz_2555_; size_t v___x_2556_; lean_object* v___x_2557_; 
v_val_2553_ = lean_ctor_get(v_extraIds_x3f_2499_, 0);
v_lctx_2554_ = lean_ctor_get(v___y_2548_, 2);
v_sz_2555_ = lean_array_size(v_val_2553_);
v___x_2556_ = ((size_t)0ULL);
v___x_2557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__1(v_lctx_2554_, v_val_2553_, v_sz_2555_, v___x_2556_, v_extraThms_2552_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2557_, 1);
v_extraThms_2511_ = v_a_2558_;
v___y_2512_ = v___y_2548_;
v___y_2513_ = v___y_2549_;
v___y_2514_ = v___y_2550_;
v___y_2515_ = v___y_2551_;
goto v___jp_2510_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_a_2559_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2557_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2557_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
else
{
v_extraThms_2511_ = v_extraThms_2552_;
v___y_2512_ = v___y_2548_;
v___y_2513_ = v___y_2549_;
v___y_2514_ = v___y_2550_;
v___y_2515_ = v___y_2551_;
goto v___jp_2510_;
}
}
v___jp_2567_:
{
uint8_t v___x_2569_; 
v___x_2569_ = l_Lean_Name_isAnonymous(v___y_2568_);
lean_dec(v___y_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
v___x_2570_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__6, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__6);
v___x_2571_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg(v___x_2570_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2571_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2571_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
v___y_2548_ = v_a_2500_;
v___y_2549_ = v_a_2501_;
v___y_2550_ = v_a_2502_;
v___y_2551_ = v_a_2503_;
goto v___jp_2547_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___boxed(lean_object* v_variantId_x3f_2583_, lean_object* v_extraIds_x3f_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts(v_variantId_x3f_2583_, v_extraIds_x3f_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_extraIds_x3f_2584_);
lean_dec(v_variantId_x3f_2583_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0(lean_object* v_as_2591_, size_t v_sz_2592_, size_t v_i_2593_, lean_object* v_b_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v___x_2600_; 
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg(v_as_2591_, v_sz_2592_, v_i_2593_, v_b_2594_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___boxed(lean_object* v_as_2601_, lean_object* v_sz_2602_, lean_object* v_i_2603_, lean_object* v_b_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_){
_start:
{
size_t v_sz_boxed_2610_; size_t v_i_boxed_2611_; lean_object* v_res_2612_; 
v_sz_boxed_2610_ = lean_unbox_usize(v_sz_2602_);
lean_dec(v_sz_2602_);
v_i_boxed_2611_ = lean_unbox_usize(v_i_2603_);
lean_dec(v_i_2603_);
v_res_2612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0(v_as_2601_, v_sz_boxed_2610_, v_i_boxed_2611_, v_b_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec_ref(v_as_2601_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2(lean_object* v_00_u03b1_2613_, lean_object* v_msg_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg(v_msg_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
return v___x_2620_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___boxed(lean_object* v_00_u03b1_2621_, lean_object* v_msg_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2(v_00_u03b1_2621_, v_msg_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions_spec__0(size_t v_sz_2629_, size_t v_i_2630_, lean_object* v_bs_2631_){
_start:
{
uint8_t v___x_2632_; 
v___x_2632_ = lean_usize_dec_lt(v_i_2630_, v_sz_2629_);
if (v___x_2632_ == 0)
{
return v_bs_2631_;
}
else
{
lean_object* v_v_2633_; lean_object* v___x_2634_; lean_object* v_bs_x27_2635_; size_t v___x_2636_; size_t v___x_2637_; lean_object* v___x_2638_; 
v_v_2633_ = lean_array_uget(v_bs_2631_, v_i_2630_);
v___x_2634_ = lean_unsigned_to_nat(0u);
v_bs_x27_2635_ = lean_array_uset(v_bs_2631_, v_i_2630_, v___x_2634_);
v___x_2636_ = ((size_t)1ULL);
v___x_2637_ = lean_usize_add(v_i_2630_, v___x_2636_);
v___x_2638_ = lean_array_uset(v_bs_x27_2635_, v_i_2630_, v_v_2633_);
v_i_2630_ = v___x_2637_;
v_bs_2631_ = v___x_2638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions_spec__0___boxed(lean_object* v_sz_2640_, lean_object* v_i_2641_, lean_object* v_bs_2642_){
_start:
{
size_t v_sz_boxed_2643_; size_t v_i_boxed_2644_; lean_object* v_res_2645_; 
v_sz_boxed_2643_ = lean_unbox_usize(v_sz_2640_);
lean_dec(v_sz_2640_);
v_i_boxed_2644_ = lean_unbox_usize(v_i_2641_);
lean_dec(v_i_2641_);
v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions_spec__0(v_sz_boxed_2643_, v_i_boxed_2644_, v_bs_2642_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions(lean_object* v_simpClause_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v___x_2673_ = l_Lean_Syntax_getNumArgs(v_simpClause_2646_);
v___x_2674_ = lean_unsigned_to_nat(0u);
v___x_2675_ = lean_nat_dec_eq(v___x_2673_, v___x_2674_);
lean_dec(v___x_2673_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; lean_object* v___y_2678_; lean_object* v___y_2679_; lean_object* v___y_2687_; lean_object* v___x_2693_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v___x_2676_ = lean_unsigned_to_nat(1u);
v___x_2693_ = l_Lean_Syntax_getArg(v_simpClause_2646_, v___x_2676_);
v___x_2697_ = l_Lean_Syntax_getNumArgs(v___x_2693_);
v___x_2698_ = lean_nat_dec_eq(v___x_2697_, v___x_2674_);
lean_dec(v___x_2697_);
if (v___x_2698_ == 0)
{
goto v___jp_2694_;
}
else
{
if (v___x_2675_ == 0)
{
lean_object* v___x_2699_; 
lean_dec(v___x_2693_);
v___x_2699_ = lean_box(0);
v___y_2687_ = v___x_2699_;
goto v___jp_2686_;
}
else
{
goto v___jp_2694_;
}
}
v___jp_2677_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; size_t v_sz_2682_; size_t v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2680_ = l_Lean_Syntax_getArg(v___y_2678_, v___x_2676_);
lean_dec(v___y_2678_);
v___x_2681_ = l_Lean_Syntax_getSepArgs(v___x_2680_);
lean_dec(v___x_2680_);
v_sz_2682_ = lean_array_size(v___x_2681_);
v___x_2683_ = ((size_t)0ULL);
v___x_2684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions_spec__0(v_sz_2682_, v___x_2683_, v___x_2681_);
v___x_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
v___y_2653_ = v___y_2679_;
v___y_2654_ = v___x_2685_;
goto v___jp_2652_;
}
v___jp_2686_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2688_ = lean_unsigned_to_nat(2u);
v___x_2689_ = l_Lean_Syntax_getArg(v_simpClause_2646_, v___x_2688_);
v___x_2690_ = l_Lean_Syntax_getNumArgs(v___x_2689_);
v___x_2691_ = lean_nat_dec_eq(v___x_2690_, v___x_2674_);
lean_dec(v___x_2690_);
if (v___x_2691_ == 0)
{
v___y_2678_ = v___x_2689_;
v___y_2679_ = v___y_2687_;
goto v___jp_2677_;
}
else
{
if (v___x_2675_ == 0)
{
lean_object* v___x_2692_; 
lean_dec(v___x_2689_);
v___x_2692_ = lean_box(0);
v___y_2653_ = v___y_2687_;
v___y_2654_ = v___x_2692_;
goto v___jp_2652_;
}
else
{
v___y_2678_ = v___x_2689_;
v___y_2679_ = v___y_2687_;
goto v___jp_2677_;
}
}
}
v___jp_2694_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2695_ = l_Lean_Syntax_getArg(v___x_2693_, v___x_2674_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2696_, 0, v___x_2695_);
v___y_2687_ = v___x_2696_;
goto v___jp_2686_;
}
}
else
{
lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2700_ = lean_box(0);
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2700_);
return v___x_2701_;
}
v___jp_2652_:
{
lean_object* v___x_2655_; 
v___x_2655_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts(v___y_2653_, v___y_2654_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
lean_dec(v___y_2654_);
lean_dec(v___y_2653_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2664_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2664_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2664_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2660_, 0, v_a_2656_);
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2660_);
v___x_2662_ = v___x_2658_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
else
{
lean_object* v_a_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
v_a_2665_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2667_ = v___x_2655_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_inc(v_a_2665_);
lean_dec(v___x_2655_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions___boxed(lean_object* v_simpClause_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions(v_simpClause_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_);
lean_dec(v_a_2706_);
lean_dec_ref(v_a_2705_);
lean_dec(v_a_2704_);
lean_dec_ref(v_a_2703_);
lean_dec(v_simpClause_2702_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac(lean_object* v_goal_2728_, lean_object* v_withPreTac_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
uint8_t v___x_2737_; uint8_t v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2737_ = 0;
v___x_2738_ = 1;
v___x_2739_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__0));
v___x_2740_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_2739_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2790_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2790_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2790_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
uint8_t v_fst_2746_; lean_object* v_snd_2747_; lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; 
v___x_2775_ = l_Lean_Syntax_getNumArgs(v_withPreTac_2729_);
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = lean_nat_dec_eq(v___x_2775_, v___x_2776_);
lean_dec(v___x_2775_);
if (v___x_2777_ == 0)
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2778_ = lean_unsigned_to_nat(1u);
v___x_2779_ = l_Lean_Syntax_getArg(v_withPreTac_2729_, v___x_2778_);
lean_inc(v___x_2779_);
v___x_2780_ = l_Lean_Syntax_getKind(v___x_2779_);
v___x_2781_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___closed__2));
v___x_2782_ = lean_name_eq(v___x_2780_, v___x_2781_);
lean_dec(v___x_2780_);
if (v___x_2782_ == 0)
{
v_fst_2746_ = v___x_2737_;
v_snd_2747_ = v___x_2779_;
goto v___jp_2745_;
}
else
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2783_ = l_Lean_Syntax_getArg(v___x_2779_, v___x_2778_);
lean_dec(v___x_2779_);
v___x_2784_ = l_Lean_Syntax_getArg(v___x_2783_, v___x_2776_);
lean_dec(v___x_2783_);
v___x_2785_ = l_Lean_Syntax_getArg(v___x_2784_, v___x_2776_);
lean_dec(v___x_2784_);
v___x_2786_ = l_Lean_Syntax_getArg(v___x_2785_, v___x_2776_);
lean_dec(v___x_2785_);
v_fst_2746_ = v___x_2738_;
v_snd_2747_ = v___x_2786_;
goto v___jp_2745_;
}
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_del_object(v___x_2743_);
lean_dec(v_goal_2728_);
v___x_2787_ = lean_box(0);
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
lean_ctor_set(v___x_2788_, 1, v_a_2741_);
v___x_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2789_, 0, v___x_2788_);
return v___x_2789_;
}
v___jp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
lean_inc(v_snd_2747_);
v___x_2748_ = l_Lean_Syntax_getKind(v_snd_2747_);
v___x_2749_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams___closed__2));
v___x_2750_ = lean_name_eq(v___x_2748_, v___x_2749_);
lean_dec(v___x_2748_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; 
lean_dec(v_goal_2728_);
v___x_2751_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2751_, 0, v_snd_2747_);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
lean_ctor_set(v___x_2752_, 1, v_a_2741_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2752_);
v___x_2754_ = v___x_2743_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
else
{
lean_object* v___x_2756_; 
lean_del_object(v___x_2743_);
lean_dec(v_a_2741_);
v___x_2756_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabGrindParams(v_snd_2747_, v_goal_2728_, v_a_2730_, v_a_2731_, v_a_2732_, v_a_2733_, v_a_2734_, v_a_2735_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v___x_2759_; uint8_t v_isShared_2760_; uint8_t v_isSharedCheck_2766_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2759_ = v___x_2756_;
v_isShared_2760_ = v_isSharedCheck_2766_;
goto v_resetjp_2758_;
}
else
{
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2759_ = lean_box(0);
v_isShared_2760_ = v_isSharedCheck_2766_;
goto v_resetjp_2758_;
}
v_resetjp_2758_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2761_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_2761_, 0, v_fst_2746_);
v___x_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2761_);
lean_ctor_set(v___x_2762_, 1, v_a_2757_);
if (v_isShared_2760_ == 0)
{
lean_ctor_set(v___x_2759_, 0, v___x_2762_);
v___x_2764_ = v___x_2759_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
v_a_2767_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2756_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2756_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec(v_goal_2728_);
v_a_2791_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2740_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2740_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac___boxed(lean_object* v_goal_2799_, lean_object* v_withPreTac_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac(v_goal_2799_, v_withPreTac_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
lean_dec(v_a_2806_);
lean_dec_ref(v_a_2805_);
lean_dec(v_a_2804_);
lean_dec_ref(v_a_2803_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_withPreTac_2800_);
return v_res_2808_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__0));
v___x_2811_ = lean_string_utf8_byte_size(v___x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg(lean_object* v_s_2812_){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v___x_2813_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__0));
v___x_2814_ = lean_string_utf8_byte_size(v_s_2812_);
v___x_2815_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__1);
v___x_2816_ = lean_nat_dec_le(v___x_2815_, v___x_2814_);
if (v___x_2816_ == 0)
{
lean_object* v___x_2817_; 
lean_dec_ref(v_s_2812_);
v___x_2817_ = lean_box(0);
return v___x_2817_;
}
else
{
lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2818_ = lean_unsigned_to_nat(0u);
v___x_2819_ = lean_string_memcmp(v_s_2812_, v___x_2813_, v___x_2818_, v___x_2818_, v___x_2815_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
lean_dec_ref(v_s_2812_);
v___x_2820_ = lean_box(0);
return v___x_2820_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
lean_inc_ref(v_s_2812_);
v___x_2821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2821_, 0, v_s_2812_);
lean_ctor_set(v___x_2821_, 1, v___x_2818_);
lean_ctor_set(v___x_2821_, 2, v___x_2814_);
v___x_2822_ = l_String_Slice_pos_x21(v___x_2821_, v___x_2815_);
lean_dec_ref_known(v___x_2821_, 3);
v___x_2823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2823_, 0, v_s_2812_);
lean_ctor_set(v___x_2823_, 1, v___x_2822_);
lean_ctor_set(v___x_2823_, 2, v___x_2814_);
v___x_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2823_);
return v___x_2824_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2(lean_object* v_s_2825_, lean_object* v_pat_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg(v_s_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___boxed(lean_object* v_s_2828_, lean_object* v_pat_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2(v_s_2828_, v_pat_2829_);
lean_dec_ref(v_pat_2829_);
return v_res_2830_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(lean_object* v_a_2831_, lean_object* v_x_2832_){
_start:
{
if (lean_obj_tag(v_x_2832_) == 0)
{
uint8_t v___x_2833_; 
v___x_2833_ = 0;
return v___x_2833_;
}
else
{
lean_object* v_key_2834_; lean_object* v_tail_2835_; uint8_t v___x_2836_; 
v_key_2834_ = lean_ctor_get(v_x_2832_, 0);
v_tail_2835_ = lean_ctor_get(v_x_2832_, 2);
v___x_2836_ = lean_nat_dec_eq(v_key_2834_, v_a_2831_);
if (v___x_2836_ == 0)
{
v_x_2832_ = v_tail_2835_;
goto _start;
}
else
{
return v___x_2836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg___boxed(lean_object* v_a_2838_, lean_object* v_x_2839_){
_start:
{
uint8_t v_res_2840_; lean_object* v_r_2841_; 
v_res_2840_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(v_a_2838_, v_x_2839_);
lean_dec(v_x_2839_);
lean_dec(v_a_2838_);
v_r_2841_ = lean_box(v_res_2840_);
return v_r_2841_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(lean_object* v_m_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v_buckets_2844_; lean_object* v___x_2845_; uint64_t v___x_2846_; uint64_t v___x_2847_; uint64_t v___x_2848_; uint64_t v_fold_2849_; uint64_t v___x_2850_; uint64_t v___x_2851_; uint64_t v___x_2852_; size_t v___x_2853_; size_t v___x_2854_; size_t v___x_2855_; size_t v___x_2856_; size_t v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_buckets_2844_ = lean_ctor_get(v_m_2842_, 1);
v___x_2845_ = lean_array_get_size(v_buckets_2844_);
v___x_2846_ = lean_uint64_of_nat(v_a_2843_);
v___x_2847_ = 32ULL;
v___x_2848_ = lean_uint64_shift_right(v___x_2846_, v___x_2847_);
v_fold_2849_ = lean_uint64_xor(v___x_2846_, v___x_2848_);
v___x_2850_ = 16ULL;
v___x_2851_ = lean_uint64_shift_right(v_fold_2849_, v___x_2850_);
v___x_2852_ = lean_uint64_xor(v_fold_2849_, v___x_2851_);
v___x_2853_ = lean_uint64_to_usize(v___x_2852_);
v___x_2854_ = lean_usize_of_nat(v___x_2845_);
v___x_2855_ = ((size_t)1ULL);
v___x_2856_ = lean_usize_sub(v___x_2854_, v___x_2855_);
v___x_2857_ = lean_usize_land(v___x_2853_, v___x_2856_);
v___x_2858_ = lean_array_uget_borrowed(v_buckets_2844_, v___x_2857_);
v___x_2859_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(v_a_2843_, v___x_2858_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg___boxed(lean_object* v_m_2860_, lean_object* v_a_2861_){
_start:
{
uint8_t v_res_2862_; lean_object* v_r_2863_; 
v_res_2862_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(v_m_2860_, v_a_2861_);
lean_dec(v_a_2861_);
lean_dec_ref(v_m_2860_);
v_r_2863_ = lean_box(v_res_2862_);
return v_r_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2___redArg(lean_object* v_a_2864_, lean_object* v_b_2865_, lean_object* v_x_2866_){
_start:
{
if (lean_obj_tag(v_x_2866_) == 0)
{
lean_dec(v_b_2865_);
lean_dec(v_a_2864_);
return v_x_2866_;
}
else
{
lean_object* v_key_2867_; lean_object* v_value_2868_; lean_object* v_tail_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2881_; 
v_key_2867_ = lean_ctor_get(v_x_2866_, 0);
v_value_2868_ = lean_ctor_get(v_x_2866_, 1);
v_tail_2869_ = lean_ctor_get(v_x_2866_, 2);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2871_ = v_x_2866_;
v_isShared_2872_ = v_isSharedCheck_2881_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_tail_2869_);
lean_inc(v_value_2868_);
lean_inc(v_key_2867_);
lean_dec(v_x_2866_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2881_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
uint8_t v___x_2873_; 
v___x_2873_ = lean_nat_dec_eq(v_key_2867_, v_a_2864_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2874_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2___redArg(v_a_2864_, v_b_2865_, v_tail_2869_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 2, v___x_2874_);
v___x_2876_ = v___x_2871_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_key_2867_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_value_2868_);
lean_ctor_set(v_reuseFailAlloc_2877_, 2, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
else
{
lean_object* v___x_2879_; 
lean_dec(v_value_2868_);
lean_dec(v_key_2867_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 1, v_b_2865_);
lean_ctor_set(v___x_2871_, 0, v_a_2864_);
v___x_2879_ = v___x_2871_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2864_);
lean_ctor_set(v_reuseFailAlloc_2880_, 1, v_b_2865_);
lean_ctor_set(v_reuseFailAlloc_2880_, 2, v_tail_2869_);
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
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_2882_, lean_object* v_x_2883_){
_start:
{
if (lean_obj_tag(v_x_2883_) == 0)
{
return v_x_2882_;
}
else
{
lean_object* v_key_2884_; lean_object* v_value_2885_; lean_object* v_tail_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2909_; 
v_key_2884_ = lean_ctor_get(v_x_2883_, 0);
v_value_2885_ = lean_ctor_get(v_x_2883_, 1);
v_tail_2886_ = lean_ctor_get(v_x_2883_, 2);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_x_2883_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2888_ = v_x_2883_;
v_isShared_2889_ = v_isSharedCheck_2909_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_tail_2886_);
lean_inc(v_value_2885_);
lean_inc(v_key_2884_);
lean_dec(v_x_2883_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2909_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; uint64_t v___x_2891_; uint64_t v___x_2892_; uint64_t v___x_2893_; uint64_t v_fold_2894_; uint64_t v___x_2895_; uint64_t v___x_2896_; uint64_t v___x_2897_; size_t v___x_2898_; size_t v___x_2899_; size_t v___x_2900_; size_t v___x_2901_; size_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2905_; 
v___x_2890_ = lean_array_get_size(v_x_2882_);
v___x_2891_ = lean_uint64_of_nat(v_key_2884_);
v___x_2892_ = 32ULL;
v___x_2893_ = lean_uint64_shift_right(v___x_2891_, v___x_2892_);
v_fold_2894_ = lean_uint64_xor(v___x_2891_, v___x_2893_);
v___x_2895_ = 16ULL;
v___x_2896_ = lean_uint64_shift_right(v_fold_2894_, v___x_2895_);
v___x_2897_ = lean_uint64_xor(v_fold_2894_, v___x_2896_);
v___x_2898_ = lean_uint64_to_usize(v___x_2897_);
v___x_2899_ = lean_usize_of_nat(v___x_2890_);
v___x_2900_ = ((size_t)1ULL);
v___x_2901_ = lean_usize_sub(v___x_2899_, v___x_2900_);
v___x_2902_ = lean_usize_land(v___x_2898_, v___x_2901_);
v___x_2903_ = lean_array_uget_borrowed(v_x_2882_, v___x_2902_);
lean_inc(v___x_2903_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 2, v___x_2903_);
v___x_2905_ = v___x_2888_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_key_2884_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_value_2885_);
lean_ctor_set(v_reuseFailAlloc_2908_, 2, v___x_2903_);
v___x_2905_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
lean_object* v___x_2906_; 
v___x_2906_ = lean_array_uset(v_x_2882_, v___x_2902_, v___x_2905_);
v_x_2882_ = v___x_2906_;
v_x_2883_ = v_tail_2886_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3___redArg(lean_object* v_i_2910_, lean_object* v_source_2911_, lean_object* v_target_2912_){
_start:
{
lean_object* v___x_2913_; uint8_t v___x_2914_; 
v___x_2913_ = lean_array_get_size(v_source_2911_);
v___x_2914_ = lean_nat_dec_lt(v_i_2910_, v___x_2913_);
if (v___x_2914_ == 0)
{
lean_dec_ref(v_source_2911_);
lean_dec(v_i_2910_);
return v_target_2912_;
}
else
{
lean_object* v_es_2915_; lean_object* v___x_2916_; lean_object* v_source_2917_; lean_object* v_target_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_es_2915_ = lean_array_fget(v_source_2911_, v_i_2910_);
v___x_2916_ = lean_box(0);
v_source_2917_ = lean_array_fset(v_source_2911_, v_i_2910_, v___x_2916_);
v_target_2918_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3_spec__6___redArg(v_target_2912_, v_es_2915_);
v___x_2919_ = lean_unsigned_to_nat(1u);
v___x_2920_ = lean_nat_add(v_i_2910_, v___x_2919_);
lean_dec(v_i_2910_);
v_i_2910_ = v___x_2920_;
v_source_2911_ = v_source_2917_;
v_target_2912_ = v_target_2918_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1___redArg(lean_object* v_data_2922_){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v_nbuckets_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2923_ = lean_array_get_size(v_data_2922_);
v___x_2924_ = lean_unsigned_to_nat(2u);
v_nbuckets_2925_ = lean_nat_mul(v___x_2923_, v___x_2924_);
v___x_2926_ = lean_unsigned_to_nat(0u);
v___x_2927_ = lean_box(0);
v___x_2928_ = lean_mk_array(v_nbuckets_2925_, v___x_2927_);
v___x_2929_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3___redArg(v___x_2926_, v_data_2922_, v___x_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0___redArg(lean_object* v_m_2930_, lean_object* v_a_2931_, lean_object* v_b_2932_){
_start:
{
lean_object* v_size_2933_; lean_object* v_buckets_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2977_; 
v_size_2933_ = lean_ctor_get(v_m_2930_, 0);
v_buckets_2934_ = lean_ctor_get(v_m_2930_, 1);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_m_2930_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2936_ = v_m_2930_;
v_isShared_2937_ = v_isSharedCheck_2977_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_buckets_2934_);
lean_inc(v_size_2933_);
lean_dec(v_m_2930_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2977_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; uint64_t v___x_2939_; uint64_t v___x_2940_; uint64_t v___x_2941_; uint64_t v_fold_2942_; uint64_t v___x_2943_; uint64_t v___x_2944_; uint64_t v___x_2945_; size_t v___x_2946_; size_t v___x_2947_; size_t v___x_2948_; size_t v___x_2949_; size_t v___x_2950_; lean_object* v_bkt_2951_; uint8_t v___x_2952_; 
v___x_2938_ = lean_array_get_size(v_buckets_2934_);
v___x_2939_ = lean_uint64_of_nat(v_a_2931_);
v___x_2940_ = 32ULL;
v___x_2941_ = lean_uint64_shift_right(v___x_2939_, v___x_2940_);
v_fold_2942_ = lean_uint64_xor(v___x_2939_, v___x_2941_);
v___x_2943_ = 16ULL;
v___x_2944_ = lean_uint64_shift_right(v_fold_2942_, v___x_2943_);
v___x_2945_ = lean_uint64_xor(v_fold_2942_, v___x_2944_);
v___x_2946_ = lean_uint64_to_usize(v___x_2945_);
v___x_2947_ = lean_usize_of_nat(v___x_2938_);
v___x_2948_ = ((size_t)1ULL);
v___x_2949_ = lean_usize_sub(v___x_2947_, v___x_2948_);
v___x_2950_ = lean_usize_land(v___x_2946_, v___x_2949_);
v_bkt_2951_ = lean_array_uget_borrowed(v_buckets_2934_, v___x_2950_);
v___x_2952_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(v_a_2931_, v_bkt_2951_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v_size_x27_2954_; lean_object* v___x_2955_; lean_object* v_buckets_x27_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v___x_2953_ = lean_unsigned_to_nat(1u);
v_size_x27_2954_ = lean_nat_add(v_size_2933_, v___x_2953_);
lean_dec(v_size_2933_);
lean_inc(v_bkt_2951_);
v___x_2955_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2955_, 0, v_a_2931_);
lean_ctor_set(v___x_2955_, 1, v_b_2932_);
lean_ctor_set(v___x_2955_, 2, v_bkt_2951_);
v_buckets_x27_2956_ = lean_array_uset(v_buckets_2934_, v___x_2950_, v___x_2955_);
v___x_2957_ = lean_unsigned_to_nat(4u);
v___x_2958_ = lean_nat_mul(v_size_x27_2954_, v___x_2957_);
v___x_2959_ = lean_unsigned_to_nat(3u);
v___x_2960_ = lean_nat_div(v___x_2958_, v___x_2959_);
lean_dec(v___x_2958_);
v___x_2961_ = lean_array_get_size(v_buckets_x27_2956_);
v___x_2962_ = lean_nat_dec_le(v___x_2960_, v___x_2961_);
lean_dec(v___x_2960_);
if (v___x_2962_ == 0)
{
lean_object* v_val_2963_; lean_object* v___x_2965_; 
v_val_2963_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1___redArg(v_buckets_x27_2956_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 1, v_val_2963_);
lean_ctor_set(v___x_2936_, 0, v_size_x27_2954_);
v___x_2965_ = v___x_2936_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_size_x27_2954_);
lean_ctor_set(v_reuseFailAlloc_2966_, 1, v_val_2963_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
else
{
lean_object* v___x_2968_; 
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 1, v_buckets_x27_2956_);
lean_ctor_set(v___x_2936_, 0, v_size_x27_2954_);
v___x_2968_ = v___x_2936_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_size_x27_2954_);
lean_ctor_set(v_reuseFailAlloc_2969_, 1, v_buckets_x27_2956_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
else
{
lean_object* v___x_2970_; lean_object* v_buckets_x27_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2975_; 
lean_inc(v_bkt_2951_);
v___x_2970_ = lean_box(0);
v_buckets_x27_2971_ = lean_array_uset(v_buckets_2934_, v___x_2950_, v___x_2970_);
v___x_2972_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2___redArg(v_a_2931_, v_b_2932_, v_bkt_2951_);
v___x_2973_ = lean_array_uset(v_buckets_x27_2971_, v___x_2950_, v___x_2972_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 1, v___x_2973_);
v___x_2975_ = v___x_2936_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_size_2933_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v___x_2973_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2981_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__1));
v___x_2982_ = l_Lean_MessageData_ofFormat(v___x_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0(lean_object* v_fst_2987_, lean_object* v___x_2988_, lean_object* v___x_2989_, lean_object* v___x_2990_, lean_object* v_a_2991_, lean_object* v___x_2992_, lean_object* v___x_2993_, lean_object* v_____r_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_){
_start:
{
uint8_t v___x_3002_; lean_object* v___y_3026_; lean_object* v_val_3033_; uint8_t v___x_3051_; 
v___x_3002_ = 0;
lean_inc(v___x_2989_);
v___x_3051_ = l_Lean_Syntax_isOfKind(v___x_2989_, v___x_2990_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; 
v___x_3052_ = lean_nat_add(v_a_2991_, v___x_2992_);
v_val_3033_ = v___x_3052_;
goto v___jp_3032_;
}
else
{
lean_object* v___x_3053_; lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3053_ = l_Lean_Syntax_getArg(v___x_2989_, v___x_2993_);
v___x_3054_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__5));
lean_inc(v___x_3053_);
v___x_3055_ = l_Lean_Syntax_isOfKind(v___x_3053_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_dec(v___x_3053_);
v___x_3056_ = lean_nat_add(v_a_2991_, v___x_2992_);
v_val_3033_ = v___x_3056_;
goto v___jp_3032_;
}
else
{
lean_object* v___x_3057_; 
v___x_3057_ = l_Lean_TSyntax_getId(v___x_3053_);
lean_dec(v___x_3053_);
if (lean_obj_tag(v___x_3057_) == 1)
{
lean_object* v_pre_3058_; 
v_pre_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_pre_3058_);
if (lean_obj_tag(v_pre_3058_) == 0)
{
lean_object* v_str_3059_; lean_object* v___x_3060_; 
v_str_3059_ = lean_ctor_get(v___x_3057_, 1);
lean_inc_ref(v_str_3059_);
lean_dec_ref_known(v___x_3057_, 2);
v___x_3060_ = l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg(v_str_3059_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_dec(v___x_2988_);
goto v___jp_3003_;
}
else
{
lean_object* v_val_3061_; lean_object* v___x_3062_; 
v_val_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_val_3061_);
lean_dec_ref_known(v___x_3060_, 1);
v___x_3062_ = l_String_Slice_toNat_x3f(v_val_3061_);
lean_dec(v_val_3061_);
if (lean_obj_tag(v___x_3062_) == 1)
{
lean_object* v_val_3063_; 
v_val_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_val_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v_val_3033_ = v_val_3063_;
goto v___jp_3032_;
}
else
{
lean_dec(v___x_3062_);
lean_dec(v___x_2988_);
goto v___jp_3003_;
}
}
}
else
{
lean_dec_ref_known(v___x_3057_, 2);
lean_dec(v_pre_3058_);
lean_dec(v___x_2988_);
goto v___jp_3003_;
}
}
else
{
lean_dec(v___x_3057_);
lean_dec(v___x_2988_);
goto v___jp_3003_;
}
}
}
v___jp_3003_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__2);
v___x_3005_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(v___x_2989_, v___x_3004_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___x_2989_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3015_; 
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v___x_3005_, 0);
lean_dec(v_unused_3016_);
v___x_3007_ = v___x_3005_;
v_isShared_3008_ = v_isSharedCheck_3015_;
goto v_resetjp_3006_;
}
else
{
lean_dec(v___x_3005_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3015_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3009_ = lean_box(v___x_3002_);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v_fst_2987_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 0, v___x_3011_);
v___x_3013_ = v___x_3007_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec(v_fst_2987_);
v_a_3017_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3005_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3005_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3022_; 
if (v_isShared_3020_ == 0)
{
v___x_3022_ = v___x_3019_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3017_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
v___jp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3027_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0___redArg(v_fst_2987_, v___y_3026_, v___x_2988_);
v___x_3028_ = lean_box(v___x_3002_);
v___x_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3029_);
v___x_3031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
return v___x_3031_;
}
v___jp_3032_:
{
uint8_t v___x_3034_; 
v___x_3034_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(v_fst_2987_, v_val_3033_);
if (v___x_3034_ == 0)
{
lean_dec(v___x_2989_);
v___y_3026_ = v_val_3033_;
goto v___jp_3025_;
}
else
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3035_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__3));
lean_inc(v_val_3033_);
v___x_3036_ = l_Nat_reprFast(v_val_3033_);
v___x_3037_ = lean_string_append(v___x_3035_, v___x_3036_);
lean_dec_ref(v___x_3036_);
v___x_3038_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__12_spec__13___redArg___closed__14));
v___x_3039_ = lean_string_append(v___x_3037_, v___x_3038_);
v___x_3040_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
v___x_3041_ = l_Lean_MessageData_ofFormat(v___x_3040_);
v___x_3042_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(v___x_2989_, v___x_3041_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___x_2989_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_dec_ref_known(v___x_3042_, 1);
v___y_3026_ = v_val_3033_;
goto v___jp_3025_;
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec(v_val_3033_);
lean_dec(v___x_2988_);
lean_dec(v_fst_2987_);
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3042_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3042_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___boxed(lean_object* v_fst_3064_, lean_object* v___x_3065_, lean_object* v___x_3066_, lean_object* v___x_3067_, lean_object* v_a_3068_, lean_object* v___x_3069_, lean_object* v___x_3070_, lean_object* v_____r_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
lean_object* v_res_3079_; 
v_res_3079_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0(v_fst_3064_, v___x_3065_, v___x_3066_, v___x_3067_, v_a_3068_, v___x_3069_, v___x_3070_, v_____r_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___x_3070_);
lean_dec(v___x_3069_);
lean_dec(v_a_3068_);
lean_dec(v___x_3067_);
return v_res_3079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1(lean_object* v_a_3080_, lean_object* v___x_3081_, lean_object* v_fst_3082_, lean_object* v___x_3083_, lean_object* v_____r_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
uint8_t v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3092_ = 1;
v___x_3093_ = lean_nat_add(v_a_3080_, v___x_3081_);
v___x_3094_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0___redArg(v_fst_3082_, v___x_3093_, v___x_3083_);
v___x_3095_ = lean_box(v___x_3092_);
v___x_3096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3094_);
lean_ctor_set(v___x_3096_, 1, v___x_3095_);
v___x_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
v___x_3098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1___boxed(lean_object* v_a_3099_, lean_object* v___x_3100_, lean_object* v_fst_3101_, lean_object* v___x_3102_, lean_object* v_____r_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1(v_a_3099_, v___x_3100_, v_fst_3101_, v___x_3102_, v_____r_3103_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___x_3100_);
lean_dec(v_a_3099_);
return v_res_3111_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
v___x_3125_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__4));
v___x_3126_ = l_Lean_stringToMessageData(v___x_3125_);
return v___x_3126_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11(void){
_start:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__10));
v___x_3139_ = l_Lean_stringToMessageData(v___x_3138_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(lean_object* v_upperBound_3144_, lean_object* v_alts_3145_, lean_object* v___x_3146_, lean_object* v_a_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
uint8_t v___x_3156_; 
v___x_3156_ = lean_nat_dec_lt(v_a_3147_, v_upperBound_3144_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; 
lean_dec(v_a_3147_);
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v_b_3148_);
return v___x_3157_;
}
else
{
lean_object* v_fst_3158_; lean_object* v_snd_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3274_; 
v_fst_3158_ = lean_ctor_get(v_b_3148_, 0);
v_snd_3159_ = lean_ctor_get(v_b_3148_, 1);
v_isSharedCheck_3274_ = !lean_is_exclusive(v_b_3148_);
if (v_isSharedCheck_3274_ == 0)
{
v___x_3161_ = v_b_3148_;
v_isShared_3162_ = v_isSharedCheck_3274_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_snd_3159_);
lean_inc(v_fst_3158_);
lean_dec(v_b_3148_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3274_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v_a_3166_; lean_object* v___y_3170_; lean_object* v___x_3189_; lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___x_3163_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1));
v___x_3164_ = lean_unsigned_to_nat(1u);
v___x_3189_ = lean_unsigned_to_nat(0u);
v___x_3190_ = lean_array_fget_borrowed(v_alts_3145_, v_a_3147_);
lean_inc(v___x_3190_);
v___x_3191_ = l_Lean_Syntax_isOfKind(v___x_3190_, v___x_3163_);
if (v___x_3191_ == 0)
{
lean_object* v___x_3192_; uint8_t v___x_3193_; 
v___x_3192_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3));
lean_inc(v___x_3190_);
v___x_3193_ = l_Lean_Syntax_isOfKind(v___x_3190_, v___x_3192_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5);
v___x_3195_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(v___x_3190_, v___x_3194_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v___x_3197_; 
lean_dec_ref_known(v___x_3195_, 1);
if (v_isShared_3162_ == 0)
{
v___x_3197_ = v___x_3161_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_fst_3158_);
lean_ctor_set(v_reuseFailAlloc_3198_, 1, v_snd_3159_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
v_a_3166_ = v___x_3197_;
goto v___jp_3165_;
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_del_object(v___x_3161_);
lean_dec(v_snd_3159_);
lean_dec(v_fst_3158_);
lean_dec(v_a_3147_);
v_a_3199_ = lean_ctor_get(v___x_3195_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3195_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3195_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3195_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v___x_3207_ = l_Lean_Syntax_getArg(v___x_3190_, v___x_3164_);
v___x_3208_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7));
lean_inc(v___x_3207_);
v___x_3209_ = l_Lean_Syntax_isOfKind(v___x_3207_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec(v___x_3207_);
v___x_3210_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5);
v___x_3211_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(v___x_3190_, v___x_3210_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v___x_3213_; 
lean_dec_ref_known(v___x_3211_, 1);
if (v_isShared_3162_ == 0)
{
v___x_3213_ = v___x_3161_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_fst_3158_);
lean_ctor_set(v_reuseFailAlloc_3214_, 1, v_snd_3159_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
v_a_3166_ = v___x_3213_;
goto v___jp_3165_;
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_del_object(v___x_3161_);
lean_dec(v_snd_3159_);
lean_dec(v_fst_3158_);
lean_dec(v_a_3147_);
v_a_3215_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3211_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3211_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3224_; uint8_t v___x_3238_; 
lean_del_object(v___x_3161_);
v___x_3223_ = l_Lean_Syntax_getArg(v___x_3207_, v___x_3189_);
lean_dec(v___x_3207_);
v___x_3224_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9));
v___x_3238_ = lean_unbox(v_snd_3159_);
lean_dec(v_snd_3159_);
if (v___x_3238_ == 1)
{
goto v___jp_3225_;
}
else
{
if (v___x_3191_ == 0)
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = lean_box(0);
lean_inc(v___x_3190_);
v___x_3240_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0(v_fst_3158_, v___x_3190_, v___x_3223_, v___x_3224_, v_a_3147_, v___x_3164_, v___x_3189_, v___x_3239_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
v___y_3170_ = v___x_3240_;
goto v___jp_3169_;
}
else
{
goto v___jp_3225_;
}
}
v___jp_3225_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11);
v___x_3227_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(v___x_3190_, v___x_3226_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3229_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref_known(v___x_3227_, 1);
lean_inc(v___x_3190_);
v___x_3229_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0(v_fst_3158_, v___x_3190_, v___x_3223_, v___x_3224_, v_a_3147_, v___x_3164_, v___x_3189_, v_a_3228_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
v___y_3170_ = v___x_3229_;
goto v___jp_3169_;
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec(v___x_3223_);
lean_dec(v_fst_3158_);
lean_dec(v_a_3147_);
v_a_3230_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3227_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3227_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3241_; lean_object* v___x_3242_; uint8_t v___x_3243_; 
v___x_3241_ = l_Lean_Syntax_getArg(v___x_3190_, v___x_3189_);
v___x_3242_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13));
v___x_3243_ = l_Lean_Syntax_isOfKind(v___x_3241_, v___x_3242_);
if (v___x_3243_ == 0)
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5);
v___x_3245_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(v___x_3190_, v___x_3244_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
if (lean_obj_tag(v___x_3245_) == 0)
{
lean_object* v___x_3247_; 
lean_dec_ref_known(v___x_3245_, 1);
if (v_isShared_3162_ == 0)
{
v___x_3247_ = v___x_3161_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_fst_3158_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_snd_3159_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
v_a_3166_ = v___x_3247_;
goto v___jp_3165_;
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_del_object(v___x_3161_);
lean_dec(v_snd_3159_);
lean_dec(v_fst_3158_);
lean_dec(v_a_3147_);
v_a_3249_ = lean_ctor_get(v___x_3245_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3245_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3245_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3245_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
else
{
uint8_t v___x_3270_; 
lean_del_object(v___x_3161_);
v___x_3270_ = lean_unbox(v_snd_3159_);
lean_dec(v_snd_3159_);
if (v___x_3270_ == 0)
{
goto v___jp_3257_;
}
else
{
uint8_t v___x_3271_; 
v___x_3271_ = lean_nat_dec_eq(v___x_3146_, v___x_3189_);
if (v___x_3271_ == 0)
{
lean_object* v___x_3272_; lean_object* v___x_3273_; 
v___x_3272_ = lean_box(0);
lean_inc(v___x_3190_);
v___x_3273_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1(v_a_3147_, v___x_3164_, v_fst_3158_, v___x_3190_, v___x_3272_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
v___y_3170_ = v___x_3273_;
goto v___jp_3169_;
}
else
{
goto v___jp_3257_;
}
}
v___jp_3257_:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11);
v___x_3259_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2_spec__4_spec__9_spec__13___redArg(v___x_3190_, v___x_3258_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3261_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
lean_inc(v___x_3190_);
v___x_3261_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1(v_a_3147_, v___x_3164_, v_fst_3158_, v___x_3190_, v_a_3260_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
v___y_3170_ = v___x_3261_;
goto v___jp_3169_;
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec(v_fst_3158_);
lean_dec(v_a_3147_);
v_a_3262_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3259_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3259_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
}
}
}
v___jp_3165_:
{
lean_object* v___x_3167_; 
v___x_3167_ = lean_nat_add(v_a_3147_, v___x_3164_);
lean_dec(v_a_3147_);
v_a_3147_ = v___x_3167_;
v_b_3148_ = v_a_3166_;
goto _start;
}
v___jp_3169_:
{
if (lean_obj_tag(v___y_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3180_; 
v_a_3171_ = lean_ctor_get(v___y_3170_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___y_3170_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3173_ = v___y_3170_;
v_isShared_3174_ = v_isSharedCheck_3180_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_a_3171_);
lean_dec(v___y_3170_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3180_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
if (lean_obj_tag(v_a_3171_) == 0)
{
lean_object* v_a_3175_; lean_object* v___x_3177_; 
lean_dec(v_a_3147_);
v_a_3175_ = lean_ctor_get(v_a_3171_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v_a_3171_, 1);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v_a_3175_);
v___x_3177_ = v___x_3173_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3175_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
else
{
lean_object* v_a_3179_; 
lean_del_object(v___x_3173_);
v_a_3179_ = lean_ctor_get(v_a_3171_, 0);
lean_inc(v_a_3179_);
lean_dec_ref_known(v_a_3171_, 1);
v_a_3166_ = v_a_3179_;
goto v___jp_3165_;
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v_a_3147_);
v_a_3181_ = lean_ctor_get(v___y_3170_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___y_3170_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___y_3170_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___y_3170_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___boxed(lean_object* v_upperBound_3275_, lean_object* v_alts_3276_, lean_object* v___x_3277_, lean_object* v_a_3278_, lean_object* v_b_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(v_upperBound_3275_, v_alts_3276_, v___x_3277_, v_a_3278_, v_b_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec(v___x_3277_);
lean_dec_ref(v_alts_3276_);
lean_dec(v_upperBound_3275_);
return v_res_3287_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2(void){
_start:
{
uint8_t v_dotOrCase_3294_; lean_object* v_map_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_dotOrCase_3294_ = 2;
v_map_3295_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41);
v___x_3296_ = lean_box(v_dotOrCase_3294_);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v_map_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
return v___x_3297_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41);
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap(lean_object* v_stx_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Lean_Syntax_getOptional_x3f(v_stx_3311_);
if (lean_obj_tag(v___x_3319_) == 1)
{
lean_object* v_val_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3429_; 
v_val_3320_ = lean_ctor_get(v___x_3319_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3319_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3322_ = v___x_3319_;
v_isShared_3323_ = v_isSharedCheck_3429_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_val_3320_);
lean_dec(v___x_3319_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3429_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3324_; uint8_t v___x_3325_; 
v___x_3324_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1));
lean_inc(v_val_3320_);
v___x_3325_ = l_Lean_Syntax_isOfKind(v_val_3320_, v___x_3324_);
if (v___x_3325_ == 0)
{
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
lean_del_object(v___x_3322_);
lean_dec(v_val_3320_);
v___x_3326_ = lean_box(0);
v___x_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
return v___x_3327_;
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v_alts_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; uint8_t v___x_3333_; 
v___x_3328_ = lean_unsigned_to_nat(1u);
v___x_3329_ = l_Lean_Syntax_getArg(v_val_3320_, v___x_3328_);
lean_dec(v_val_3320_);
v_alts_3330_ = l_Lean_Syntax_getArgs(v___x_3329_);
lean_dec(v___x_3329_);
v___x_3331_ = lean_array_get_size(v_alts_3330_);
v___x_3332_ = lean_unsigned_to_nat(0u);
v___x_3333_ = lean_nat_dec_eq(v___x_3331_, v___x_3332_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2);
v___x_3335_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(v___x_3331_, v_alts_3330_, v___x_3331_, v___x_3332_, v___x_3334_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
lean_dec_ref(v_alts_3330_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3338_; uint8_t v_isShared_3339_; uint8_t v_isSharedCheck_3347_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3338_ = v___x_3335_;
v_isShared_3339_ = v_isSharedCheck_3347_;
goto v_resetjp_3337_;
}
else
{
lean_inc(v_a_3336_);
lean_dec(v___x_3335_);
v___x_3338_ = lean_box(0);
v_isShared_3339_ = v_isSharedCheck_3347_;
goto v_resetjp_3337_;
}
v_resetjp_3337_:
{
lean_object* v_fst_3340_; lean_object* v___x_3342_; 
v_fst_3340_ = lean_ctor_get(v_a_3336_, 0);
lean_inc(v_fst_3340_);
lean_dec(v_a_3336_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v_fst_3340_);
v___x_3342_ = v___x_3322_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_fst_3340_);
v___x_3342_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
lean_object* v___x_3344_; 
if (v_isShared_3339_ == 0)
{
lean_ctor_set(v___x_3338_, 0, v___x_3342_);
v___x_3344_ = v___x_3338_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_del_object(v___x_3322_);
v_a_3348_ = lean_ctor_get(v___x_3335_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3335_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3335_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3335_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec_ref(v_alts_3330_);
lean_del_object(v___x_3322_);
v___x_3356_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3);
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
return v___x_3357_;
}
}
}
else
{
lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; uint8_t v___x_3361_; 
v___x_3358_ = lean_unsigned_to_nat(0u);
v___x_3359_ = l_Lean_Syntax_getArg(v_val_3320_, v___x_3358_);
v___x_3360_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5));
lean_inc(v___x_3359_);
v___x_3361_ = l_Lean_Syntax_isOfKind(v___x_3359_, v___x_3360_);
if (v___x_3361_ == 0)
{
lean_dec(v___x_3359_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3362_; lean_object* v___x_3363_; 
lean_del_object(v___x_3322_);
lean_dec(v_val_3320_);
v___x_3362_ = lean_box(0);
v___x_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
return v___x_3363_;
}
else
{
lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v_alts_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; 
v___x_3364_ = lean_unsigned_to_nat(1u);
v___x_3365_ = l_Lean_Syntax_getArg(v_val_3320_, v___x_3364_);
lean_dec(v_val_3320_);
v_alts_3366_ = l_Lean_Syntax_getArgs(v___x_3365_);
lean_dec(v___x_3365_);
v___x_3367_ = lean_array_get_size(v_alts_3366_);
v___x_3368_ = lean_nat_dec_eq(v___x_3367_, v___x_3358_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2);
v___x_3370_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(v___x_3367_, v_alts_3366_, v___x_3367_, v___x_3358_, v___x_3369_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
lean_dec_ref(v_alts_3366_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3382_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3382_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3382_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v_fst_3375_; lean_object* v___x_3377_; 
v_fst_3375_ = lean_ctor_get(v_a_3371_, 0);
lean_inc(v_fst_3375_);
lean_dec(v_a_3371_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v_fst_3375_);
v___x_3377_ = v___x_3322_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_fst_3375_);
v___x_3377_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3377_);
v___x_3379_ = v___x_3373_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3380_; 
v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
v___x_3379_ = v_reuseFailAlloc_3380_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
return v___x_3379_;
}
}
}
}
else
{
lean_object* v_a_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3390_; 
lean_del_object(v___x_3322_);
v_a_3383_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3385_ = v___x_3370_;
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
else
{
lean_inc(v_a_3383_);
lean_dec(v___x_3370_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3390_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3388_; 
if (v_isShared_3386_ == 0)
{
v___x_3388_ = v___x_3385_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3383_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
}
else
{
lean_object* v___x_3391_; lean_object* v___x_3392_; 
lean_dec_ref(v_alts_3366_);
lean_del_object(v___x_3322_);
v___x_3391_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3);
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
return v___x_3392_;
}
}
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3393_ = l_Lean_Syntax_getArg(v___x_3359_, v___x_3358_);
lean_dec(v___x_3359_);
v___x_3394_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__8));
v___x_3395_ = l_Lean_Syntax_isOfKind(v___x_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
if (v___x_3325_ == 0)
{
lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_del_object(v___x_3322_);
lean_dec(v_val_3320_);
v___x_3396_ = lean_box(0);
v___x_3397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
return v___x_3397_;
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v_alts_3400_; lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3398_ = lean_unsigned_to_nat(1u);
v___x_3399_ = l_Lean_Syntax_getArg(v_val_3320_, v___x_3398_);
lean_dec(v_val_3320_);
v_alts_3400_ = l_Lean_Syntax_getArgs(v___x_3399_);
lean_dec(v___x_3399_);
v___x_3401_ = lean_array_get_size(v_alts_3400_);
v___x_3402_ = lean_nat_dec_eq(v___x_3401_, v___x_3358_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2);
v___x_3404_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(v___x_3401_, v_alts_3400_, v___x_3401_, v___x_3358_, v___x_3403_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
lean_dec_ref(v_alts_3400_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v_a_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3416_; 
v_a_3405_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3407_ = v___x_3404_;
v_isShared_3408_ = v_isSharedCheck_3416_;
goto v_resetjp_3406_;
}
else
{
lean_inc(v_a_3405_);
lean_dec(v___x_3404_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3416_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v_fst_3409_; lean_object* v___x_3411_; 
v_fst_3409_ = lean_ctor_get(v_a_3405_, 0);
lean_inc(v_fst_3409_);
lean_dec(v_a_3405_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v_fst_3409_);
v___x_3411_ = v___x_3322_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_fst_3409_);
v___x_3411_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3413_; 
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3411_);
v___x_3413_ = v___x_3407_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_del_object(v___x_3322_);
v_a_3417_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3404_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3404_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
lean_dec_ref(v_alts_3400_);
lean_del_object(v___x_3322_);
v___x_3425_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3);
v___x_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3425_);
return v___x_3426_;
}
}
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_del_object(v___x_3322_);
lean_dec(v_val_3320_);
v___x_3427_ = lean_box(0);
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3427_);
return v___x_3428_;
}
}
}
}
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3431_; 
lean_dec(v___x_3319_);
v___x_3430_ = lean_box(0);
v___x_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___boxed(lean_object* v_stx_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap(v_stx_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec(v_stx_3432_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0(lean_object* v_00_u03b2_3441_, lean_object* v_m_3442_, lean_object* v_a_3443_, lean_object* v_b_3444_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0___redArg(v_m_3442_, v_a_3443_, v_b_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1(lean_object* v_00_u03b2_3446_, lean_object* v_m_3447_, lean_object* v_a_3448_){
_start:
{
uint8_t v___x_3449_; 
v___x_3449_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(v_m_3447_, v_a_3448_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___boxed(lean_object* v_00_u03b2_3450_, lean_object* v_m_3451_, lean_object* v_a_3452_){
_start:
{
uint8_t v_res_3453_; lean_object* v_r_3454_; 
v_res_3453_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1(v_00_u03b2_3450_, v_m_3451_, v_a_3452_);
lean_dec(v_a_3452_);
lean_dec_ref(v_m_3451_);
v_r_3454_ = lean_box(v_res_3453_);
return v_r_3454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3(lean_object* v_upperBound_3455_, lean_object* v_alts_3456_, lean_object* v___x_3457_, lean_object* v_inst_3458_, lean_object* v_R_3459_, lean_object* v_a_3460_, lean_object* v_b_3461_, lean_object* v_c_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_){
_start:
{
lean_object* v___x_3470_; 
v___x_3470_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(v_upperBound_3455_, v_alts_3456_, v___x_3457_, v_a_3460_, v_b_3461_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
return v___x_3470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___boxed(lean_object* v_upperBound_3471_, lean_object* v_alts_3472_, lean_object* v___x_3473_, lean_object* v_inst_3474_, lean_object* v_R_3475_, lean_object* v_a_3476_, lean_object* v_b_3477_, lean_object* v_c_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_, lean_object* v___y_3483_, lean_object* v___y_3484_, lean_object* v___y_3485_){
_start:
{
lean_object* v_res_3486_; 
v_res_3486_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3(v_upperBound_3471_, v_alts_3472_, v___x_3473_, v_inst_3474_, v_R_3475_, v_a_3476_, v_b_3477_, v_c_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_, v___y_3484_);
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3483_);
lean_dec(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___x_3473_);
lean_dec_ref(v_alts_3472_);
lean_dec(v_upperBound_3471_);
return v_res_3486_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0(lean_object* v_00_u03b2_3487_, lean_object* v_a_3488_, lean_object* v_x_3489_){
_start:
{
uint8_t v___x_3490_; 
v___x_3490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(v_a_3488_, v_x_3489_);
return v___x_3490_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3491_, lean_object* v_a_3492_, lean_object* v_x_3493_){
_start:
{
uint8_t v_res_3494_; lean_object* v_r_3495_; 
v_res_3494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0(v_00_u03b2_3491_, v_a_3492_, v_x_3493_);
lean_dec(v_x_3493_);
lean_dec(v_a_3492_);
v_r_3495_ = lean_box(v_res_3494_);
return v_r_3495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1(lean_object* v_00_u03b2_3496_, lean_object* v_data_3497_){
_start:
{
lean_object* v___x_3498_; 
v___x_3498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1___redArg(v_data_3497_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2(lean_object* v_00_u03b2_3499_, lean_object* v_a_3500_, lean_object* v_b_3501_, lean_object* v_x_3502_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2___redArg(v_a_3500_, v_b_3501_, v_x_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3504_, lean_object* v_i_3505_, lean_object* v_source_3506_, lean_object* v_target_3507_){
_start:
{
lean_object* v___x_3508_; 
v___x_3508_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3___redArg(v_i_3505_, v_source_3506_, v_target_3507_);
return v___x_3508_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3509_, lean_object* v_x_3510_, lean_object* v_x_3511_){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3_spec__6___redArg(v_x_3510_, v_x_3511_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg(lean_object* v_a_3513_, lean_object* v_x_3514_){
_start:
{
if (lean_obj_tag(v_x_3514_) == 0)
{
lean_object* v___x_3515_; 
v___x_3515_ = lean_box(0);
return v___x_3515_;
}
else
{
lean_object* v_key_3516_; lean_object* v_value_3517_; lean_object* v_tail_3518_; uint8_t v___x_3519_; 
v_key_3516_ = lean_ctor_get(v_x_3514_, 0);
v_value_3517_ = lean_ctor_get(v_x_3514_, 1);
v_tail_3518_ = lean_ctor_get(v_x_3514_, 2);
v___x_3519_ = lean_nat_dec_eq(v_key_3516_, v_a_3513_);
if (v___x_3519_ == 0)
{
v_x_3514_ = v_tail_3518_;
goto _start;
}
else
{
lean_object* v___x_3521_; 
lean_inc(v_value_3517_);
v___x_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3521_, 0, v_value_3517_);
return v___x_3521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg___boxed(lean_object* v_a_3522_, lean_object* v_x_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg(v_a_3522_, v_x_3523_);
lean_dec(v_x_3523_);
lean_dec(v_a_3522_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg(lean_object* v_m_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v_buckets_3527_; lean_object* v___x_3528_; uint64_t v___x_3529_; uint64_t v___x_3530_; uint64_t v___x_3531_; uint64_t v_fold_3532_; uint64_t v___x_3533_; uint64_t v___x_3534_; uint64_t v___x_3535_; size_t v___x_3536_; size_t v___x_3537_; size_t v___x_3538_; size_t v___x_3539_; size_t v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v_buckets_3527_ = lean_ctor_get(v_m_3525_, 1);
v___x_3528_ = lean_array_get_size(v_buckets_3527_);
v___x_3529_ = lean_uint64_of_nat(v_a_3526_);
v___x_3530_ = 32ULL;
v___x_3531_ = lean_uint64_shift_right(v___x_3529_, v___x_3530_);
v_fold_3532_ = lean_uint64_xor(v___x_3529_, v___x_3531_);
v___x_3533_ = 16ULL;
v___x_3534_ = lean_uint64_shift_right(v_fold_3532_, v___x_3533_);
v___x_3535_ = lean_uint64_xor(v_fold_3532_, v___x_3534_);
v___x_3536_ = lean_uint64_to_usize(v___x_3535_);
v___x_3537_ = lean_usize_of_nat(v___x_3528_);
v___x_3538_ = ((size_t)1ULL);
v___x_3539_ = lean_usize_sub(v___x_3537_, v___x_3538_);
v___x_3540_ = lean_usize_land(v___x_3536_, v___x_3539_);
v___x_3541_ = lean_array_uget_borrowed(v_buckets_3527_, v___x_3540_);
v___x_3542_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg(v_a_3526_, v___x_3541_);
return v___x_3542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg___boxed(lean_object* v_m_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg(v_m_3543_, v_a_3544_);
lean_dec(v_a_3544_);
lean_dec_ref(v_m_3543_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__5___redArg(lean_object* v_m_3546_, lean_object* v_a_3547_, lean_object* v_b_3548_){
_start:
{
lean_object* v_size_3549_; lean_object* v_buckets_3550_; lean_object* v___x_3551_; uint64_t v___x_3552_; uint64_t v___x_3553_; uint64_t v___x_3554_; uint64_t v_fold_3555_; uint64_t v___x_3556_; uint64_t v___x_3557_; uint64_t v___x_3558_; size_t v___x_3559_; size_t v___x_3560_; size_t v___x_3561_; size_t v___x_3562_; size_t v___x_3563_; lean_object* v_bkt_3564_; uint8_t v___x_3565_; 
v_size_3549_ = lean_ctor_get(v_m_3546_, 0);
v_buckets_3550_ = lean_ctor_get(v_m_3546_, 1);
v___x_3551_ = lean_array_get_size(v_buckets_3550_);
v___x_3552_ = lean_uint64_of_nat(v_a_3547_);
v___x_3553_ = 32ULL;
v___x_3554_ = lean_uint64_shift_right(v___x_3552_, v___x_3553_);
v_fold_3555_ = lean_uint64_xor(v___x_3552_, v___x_3554_);
v___x_3556_ = 16ULL;
v___x_3557_ = lean_uint64_shift_right(v_fold_3555_, v___x_3556_);
v___x_3558_ = lean_uint64_xor(v_fold_3555_, v___x_3557_);
v___x_3559_ = lean_uint64_to_usize(v___x_3558_);
v___x_3560_ = lean_usize_of_nat(v___x_3551_);
v___x_3561_ = ((size_t)1ULL);
v___x_3562_ = lean_usize_sub(v___x_3560_, v___x_3561_);
v___x_3563_ = lean_usize_land(v___x_3559_, v___x_3562_);
v_bkt_3564_ = lean_array_uget_borrowed(v_buckets_3550_, v___x_3563_);
v___x_3565_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(v_a_3547_, v_bkt_3564_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3586_; 
lean_inc_ref(v_buckets_3550_);
lean_inc(v_size_3549_);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_m_3546_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; lean_object* v_unused_3588_; 
v_unused_3587_ = lean_ctor_get(v_m_3546_, 1);
lean_dec(v_unused_3587_);
v_unused_3588_ = lean_ctor_get(v_m_3546_, 0);
lean_dec(v_unused_3588_);
v___x_3567_ = v_m_3546_;
v_isShared_3568_ = v_isSharedCheck_3586_;
goto v_resetjp_3566_;
}
else
{
lean_dec(v_m_3546_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3586_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v_size_x27_3570_; lean_object* v___x_3571_; lean_object* v_buckets_x27_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3569_ = lean_unsigned_to_nat(1u);
v_size_x27_3570_ = lean_nat_add(v_size_3549_, v___x_3569_);
lean_dec(v_size_3549_);
lean_inc(v_bkt_3564_);
v___x_3571_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3571_, 0, v_a_3547_);
lean_ctor_set(v___x_3571_, 1, v_b_3548_);
lean_ctor_set(v___x_3571_, 2, v_bkt_3564_);
v_buckets_x27_3572_ = lean_array_uset(v_buckets_3550_, v___x_3563_, v___x_3571_);
v___x_3573_ = lean_unsigned_to_nat(4u);
v___x_3574_ = lean_nat_mul(v_size_x27_3570_, v___x_3573_);
v___x_3575_ = lean_unsigned_to_nat(3u);
v___x_3576_ = lean_nat_div(v___x_3574_, v___x_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_array_get_size(v_buckets_x27_3572_);
v___x_3578_ = lean_nat_dec_le(v___x_3576_, v___x_3577_);
lean_dec(v___x_3576_);
if (v___x_3578_ == 0)
{
lean_object* v_val_3579_; lean_object* v___x_3581_; 
v_val_3579_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1___redArg(v_buckets_x27_3572_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 1, v_val_3579_);
lean_ctor_set(v___x_3567_, 0, v_size_x27_3570_);
v___x_3581_ = v___x_3567_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_size_x27_3570_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_val_3579_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
else
{
lean_object* v___x_3584_; 
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 1, v_buckets_x27_3572_);
lean_ctor_set(v___x_3567_, 0, v_size_x27_3570_);
v___x_3584_ = v___x_3567_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_size_x27_3570_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_buckets_x27_3572_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
else
{
lean_dec(v_b_3548_);
lean_dec(v_a_3547_);
return v_m_3546_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg(lean_object* v_upperBound_3589_, lean_object* v_alts_3590_, lean_object* v_invariants_3591_, lean_object* v_a_3592_, lean_object* v_b_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v_a_3602_; uint8_t v___x_3606_; 
v___x_3606_ = lean_nat_dec_lt(v_a_3592_, v_upperBound_3589_);
if (v___x_3606_ == 0)
{
lean_object* v___x_3607_; 
lean_dec(v_a_3592_);
v___x_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3607_, 0, v_b_3593_);
return v___x_3607_;
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v___x_3608_ = lean_unsigned_to_nat(1u);
v___x_3609_ = lean_nat_add(v_a_3592_, v___x_3608_);
v___x_3610_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(v_b_3593_, v___x_3609_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg(v_alts_3590_, v___x_3609_);
if (lean_obj_tag(v___x_3611_) == 1)
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
lean_dec_ref_known(v___x_3611_, 1);
v___x_3612_ = lean_array_fget_borrowed(v_invariants_3591_, v_a_3592_);
lean_inc(v___x_3612_);
v___x_3613_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(v_alts_3590_, v___x_3609_, v___x_3612_, v___y_3594_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
lean_dec_ref_known(v___x_3613_, 1);
v___x_3614_ = lean_box(0);
v___x_3615_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__5___redArg(v_b_3593_, v___x_3609_, v___x_3614_);
v_a_3602_ = v___x_3615_;
goto v___jp_3601_;
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec(v___x_3609_);
lean_dec_ref(v_b_3593_);
lean_dec(v_a_3592_);
v_a_3616_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3613_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3613_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
else
{
lean_dec(v___x_3611_);
lean_dec(v___x_3609_);
v_a_3602_ = v_b_3593_;
goto v___jp_3601_;
}
}
else
{
lean_dec(v___x_3609_);
v_a_3602_ = v_b_3593_;
goto v___jp_3601_;
}
}
v___jp_3601_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = lean_unsigned_to_nat(1u);
v___x_3604_ = lean_nat_add(v_a_3592_, v___x_3603_);
lean_dec(v_a_3592_);
v_a_3592_ = v___x_3604_;
v_b_3593_ = v_a_3602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg___boxed(lean_object* v_upperBound_3624_, lean_object* v_alts_3625_, lean_object* v_invariants_3626_, lean_object* v_a_3627_, lean_object* v_b_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg(v_upperBound_3624_, v_alts_3625_, v_invariants_3626_, v_a_3627_, v_b_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec_ref(v_invariants_3626_);
lean_dec_ref(v_alts_3625_);
lean_dec(v_upperBound_3624_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg(lean_object* v_ref_3637_, lean_object* v_msgData_3638_, uint8_t v_severity_3639_, uint8_t v_isSilent_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___y_3647_; uint8_t v___y_3648_; lean_object* v___y_3649_; uint8_t v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3683_; uint8_t v___y_3684_; uint8_t v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; uint8_t v___y_3689_; lean_object* v___y_3690_; lean_object* v___y_3708_; uint8_t v___y_3709_; uint8_t v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; uint8_t v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3719_; uint8_t v___y_3720_; lean_object* v___y_3721_; lean_object* v___y_3722_; uint8_t v___y_3723_; lean_object* v___y_3724_; uint8_t v___y_3725_; uint8_t v___x_3730_; uint8_t v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; uint8_t v___y_3737_; uint8_t v___y_3738_; uint8_t v___y_3740_; uint8_t v___x_3755_; 
v___x_3730_ = 2;
v___x_3755_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3639_, v___x_3730_);
if (v___x_3755_ == 0)
{
v___y_3740_ = v___x_3755_;
goto v___jp_3739_;
}
else
{
uint8_t v___x_3756_; 
lean_inc_ref(v_msgData_3638_);
v___x_3756_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3638_);
v___y_3740_ = v___x_3756_;
goto v___jp_3739_;
}
v___jp_3646_:
{
lean_object* v___x_3656_; lean_object* v_currNamespace_3657_; lean_object* v_openDecls_3658_; lean_object* v_env_3659_; lean_object* v_nextMacroScope_3660_; lean_object* v_ngen_3661_; lean_object* v_auxDeclNGen_3662_; lean_object* v_traceState_3663_; lean_object* v_cache_3664_; lean_object* v_messages_3665_; lean_object* v_infoState_3666_; lean_object* v_snapshotTasks_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3681_; 
v___x_3656_ = lean_st_ref_take(v___y_3655_);
v_currNamespace_3657_ = lean_ctor_get(v___y_3654_, 6);
v_openDecls_3658_ = lean_ctor_get(v___y_3654_, 7);
v_env_3659_ = lean_ctor_get(v___x_3656_, 0);
v_nextMacroScope_3660_ = lean_ctor_get(v___x_3656_, 1);
v_ngen_3661_ = lean_ctor_get(v___x_3656_, 2);
v_auxDeclNGen_3662_ = lean_ctor_get(v___x_3656_, 3);
v_traceState_3663_ = lean_ctor_get(v___x_3656_, 4);
v_cache_3664_ = lean_ctor_get(v___x_3656_, 5);
v_messages_3665_ = lean_ctor_get(v___x_3656_, 6);
v_infoState_3666_ = lean_ctor_get(v___x_3656_, 7);
v_snapshotTasks_3667_ = lean_ctor_get(v___x_3656_, 8);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3669_ = v___x_3656_;
v_isShared_3670_ = v_isSharedCheck_3681_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_snapshotTasks_3667_);
lean_inc(v_infoState_3666_);
lean_inc(v_messages_3665_);
lean_inc(v_cache_3664_);
lean_inc(v_traceState_3663_);
lean_inc(v_auxDeclNGen_3662_);
lean_inc(v_ngen_3661_);
lean_inc(v_nextMacroScope_3660_);
lean_inc(v_env_3659_);
lean_dec(v___x_3656_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3681_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
lean_inc(v_openDecls_3658_);
lean_inc(v_currNamespace_3657_);
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v_currNamespace_3657_);
lean_ctor_set(v___x_3671_, 1, v_openDecls_3658_);
v___x_3672_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3671_);
lean_ctor_set(v___x_3672_, 1, v___y_3651_);
lean_inc_ref(v___y_3647_);
lean_inc_ref(v___y_3649_);
v___x_3673_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3673_, 0, v___y_3649_);
lean_ctor_set(v___x_3673_, 1, v___y_3653_);
lean_ctor_set(v___x_3673_, 2, v___y_3652_);
lean_ctor_set(v___x_3673_, 3, v___y_3647_);
lean_ctor_set(v___x_3673_, 4, v___x_3672_);
lean_ctor_set_uint8(v___x_3673_, sizeof(void*)*5, v___y_3650_);
lean_ctor_set_uint8(v___x_3673_, sizeof(void*)*5 + 1, v___y_3648_);
lean_ctor_set_uint8(v___x_3673_, sizeof(void*)*5 + 2, v_isSilent_3640_);
v___x_3674_ = l_Lean_MessageLog_add(v___x_3673_, v_messages_3665_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 6, v___x_3674_);
v___x_3676_ = v___x_3669_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_env_3659_);
lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_nextMacroScope_3660_);
lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_ngen_3661_);
lean_ctor_set(v_reuseFailAlloc_3680_, 3, v_auxDeclNGen_3662_);
lean_ctor_set(v_reuseFailAlloc_3680_, 4, v_traceState_3663_);
lean_ctor_set(v_reuseFailAlloc_3680_, 5, v_cache_3664_);
lean_ctor_set(v_reuseFailAlloc_3680_, 6, v___x_3674_);
lean_ctor_set(v_reuseFailAlloc_3680_, 7, v_infoState_3666_);
lean_ctor_set(v_reuseFailAlloc_3680_, 8, v_snapshotTasks_3667_);
v___x_3676_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3677_ = lean_st_ref_set(v___y_3655_, v___x_3676_);
v___x_3678_ = lean_box(0);
v___x_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
return v___x_3679_;
}
}
}
v___jp_3682_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3706_; 
v___x_3691_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3638_);
v___x_3692_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v___x_3691_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3695_ = v___x_3692_;
v_isShared_3696_ = v_isSharedCheck_3706_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3692_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3706_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
lean_inc_ref_n(v___y_3687_, 2);
v___x_3697_ = l_Lean_FileMap_toPosition(v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
v___x_3698_ = l_Lean_FileMap_toPosition(v___y_3687_, v___y_3690_);
lean_dec(v___y_3690_);
v___x_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
v___x_3700_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___closed__0));
if (v___y_3684_ == 0)
{
lean_del_object(v___x_3695_);
lean_dec_ref(v___y_3683_);
v___y_3647_ = v___x_3700_;
v___y_3648_ = v___y_3685_;
v___y_3649_ = v___y_3686_;
v___y_3650_ = v___y_3689_;
v___y_3651_ = v_a_3693_;
v___y_3652_ = v___x_3699_;
v___y_3653_ = v___x_3697_;
v___y_3654_ = v___y_3643_;
v___y_3655_ = v___y_3644_;
goto v___jp_3646_;
}
else
{
uint8_t v___x_3701_; 
lean_inc(v_a_3693_);
v___x_3701_ = l_Lean_MessageData_hasTag(v___y_3683_, v_a_3693_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; lean_object* v___x_3704_; 
lean_dec_ref_known(v___x_3699_, 1);
lean_dec_ref(v___x_3697_);
lean_dec(v_a_3693_);
v___x_3702_ = lean_box(0);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 0, v___x_3702_);
v___x_3704_ = v___x_3695_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3702_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
else
{
lean_del_object(v___x_3695_);
v___y_3647_ = v___x_3700_;
v___y_3648_ = v___y_3685_;
v___y_3649_ = v___y_3686_;
v___y_3650_ = v___y_3689_;
v___y_3651_ = v_a_3693_;
v___y_3652_ = v___x_3699_;
v___y_3653_ = v___x_3697_;
v___y_3654_ = v___y_3643_;
v___y_3655_ = v___y_3644_;
goto v___jp_3646_;
}
}
}
}
v___jp_3707_:
{
lean_object* v___x_3716_; 
v___x_3716_ = l_Lean_Syntax_getTailPos_x3f(v___y_3714_, v___y_3713_);
lean_dec(v___y_3714_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_inc(v___y_3715_);
v___y_3683_ = v___y_3708_;
v___y_3684_ = v___y_3709_;
v___y_3685_ = v___y_3710_;
v___y_3686_ = v___y_3712_;
v___y_3687_ = v___y_3711_;
v___y_3688_ = v___y_3715_;
v___y_3689_ = v___y_3713_;
v___y_3690_ = v___y_3715_;
goto v___jp_3682_;
}
else
{
lean_object* v_val_3717_; 
v_val_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_val_3717_);
lean_dec_ref_known(v___x_3716_, 1);
v___y_3683_ = v___y_3708_;
v___y_3684_ = v___y_3709_;
v___y_3685_ = v___y_3710_;
v___y_3686_ = v___y_3712_;
v___y_3687_ = v___y_3711_;
v___y_3688_ = v___y_3715_;
v___y_3689_ = v___y_3713_;
v___y_3690_ = v_val_3717_;
goto v___jp_3682_;
}
}
v___jp_3718_:
{
lean_object* v_ref_3726_; lean_object* v___x_3727_; 
v_ref_3726_ = l_Lean_replaceRef(v_ref_3637_, v___y_3724_);
v___x_3727_ = l_Lean_Syntax_getPos_x3f(v_ref_3726_, v___y_3723_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_unsigned_to_nat(0u);
v___y_3708_ = v___y_3719_;
v___y_3709_ = v___y_3720_;
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3722_;
v___y_3712_ = v___y_3721_;
v___y_3713_ = v___y_3723_;
v___y_3714_ = v_ref_3726_;
v___y_3715_ = v___x_3728_;
goto v___jp_3707_;
}
else
{
lean_object* v_val_3729_; 
v_val_3729_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_val_3729_);
lean_dec_ref_known(v___x_3727_, 1);
v___y_3708_ = v___y_3719_;
v___y_3709_ = v___y_3720_;
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3722_;
v___y_3712_ = v___y_3721_;
v___y_3713_ = v___y_3723_;
v___y_3714_ = v_ref_3726_;
v___y_3715_ = v_val_3729_;
goto v___jp_3707_;
}
}
v___jp_3731_:
{
if (v___y_3738_ == 0)
{
v___y_3719_ = v___y_3735_;
v___y_3720_ = v___y_3732_;
v___y_3721_ = v___y_3734_;
v___y_3722_ = v___y_3733_;
v___y_3723_ = v___y_3737_;
v___y_3724_ = v___y_3736_;
v___y_3725_ = v_severity_3639_;
goto v___jp_3718_;
}
else
{
v___y_3719_ = v___y_3735_;
v___y_3720_ = v___y_3732_;
v___y_3721_ = v___y_3734_;
v___y_3722_ = v___y_3733_;
v___y_3723_ = v___y_3737_;
v___y_3724_ = v___y_3736_;
v___y_3725_ = v___x_3730_;
goto v___jp_3718_;
}
}
v___jp_3739_:
{
if (v___y_3740_ == 0)
{
lean_object* v_fileName_3741_; lean_object* v_fileMap_3742_; lean_object* v_options_3743_; lean_object* v_ref_3744_; uint8_t v_suppressElabErrors_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___f_3748_; uint8_t v___x_3749_; uint8_t v___x_3750_; 
v_fileName_3741_ = lean_ctor_get(v___y_3643_, 0);
v_fileMap_3742_ = lean_ctor_get(v___y_3643_, 1);
v_options_3743_ = lean_ctor_get(v___y_3643_, 2);
v_ref_3744_ = lean_ctor_get(v___y_3643_, 5);
v_suppressElabErrors_3745_ = lean_ctor_get_uint8(v___y_3643_, sizeof(void*)*14 + 1);
v___x_3746_ = lean_box(v___y_3740_);
v___x_3747_ = lean_box(v_suppressElabErrors_3745_);
v___f_3748_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3748_, 0, v___x_3746_);
lean_closure_set(v___f_3748_, 1, v___x_3747_);
v___x_3749_ = 1;
v___x_3750_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3639_, v___x_3749_);
if (v___x_3750_ == 0)
{
v___y_3732_ = v_suppressElabErrors_3745_;
v___y_3733_ = v_fileMap_3742_;
v___y_3734_ = v_fileName_3741_;
v___y_3735_ = v___f_3748_;
v___y_3736_ = v_ref_3744_;
v___y_3737_ = v___y_3740_;
v___y_3738_ = v___x_3750_;
goto v___jp_3731_;
}
else
{
lean_object* v___x_3751_; uint8_t v___x_3752_; 
v___x_3751_ = l_Lean_warningAsError;
v___x_3752_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_options_3743_, v___x_3751_);
v___y_3732_ = v_suppressElabErrors_3745_;
v___y_3733_ = v_fileMap_3742_;
v___y_3734_ = v_fileName_3741_;
v___y_3735_ = v___f_3748_;
v___y_3736_ = v_ref_3744_;
v___y_3737_ = v___y_3740_;
v___y_3738_ = v___x_3752_;
goto v___jp_3731_;
}
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
lean_dec_ref(v_msgData_3638_);
v___x_3753_ = lean_box(0);
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
return v___x_3754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg___boxed(lean_object* v_ref_3757_, lean_object* v_msgData_3758_, lean_object* v_severity_3759_, lean_object* v_isSilent_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
uint8_t v_severity_boxed_3766_; uint8_t v_isSilent_boxed_3767_; lean_object* v_res_3768_; 
v_severity_boxed_3766_ = lean_unbox(v_severity_3759_);
v_isSilent_boxed_3767_ = lean_unbox(v_isSilent_3760_);
v_res_3768_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg(v_ref_3757_, v_msgData_3758_, v_severity_boxed_3766_, v_isSilent_boxed_3767_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v_ref_3757_);
return v_res_3768_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0(lean_object* v_ref_3769_, lean_object* v_msgData_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
uint8_t v___x_3778_; uint8_t v___x_3779_; lean_object* v___x_3780_; 
v___x_3778_ = 1;
v___x_3779_ = 0;
v___x_3780_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg(v_ref_3769_, v_msgData_3770_, v___x_3778_, v___x_3779_, v___y_3773_, v___y_3774_, v___y_3775_, v___y_3776_);
return v___x_3780_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0___boxed(lean_object* v_ref_3781_, lean_object* v_msgData_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0(v_ref_3781_, v_msgData_3782_, v___y_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
lean_dec_ref(v___y_3783_);
lean_dec(v_ref_3781_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1(lean_object* v_a_3793_, lean_object* v_as_3794_, size_t v_sz_3795_, size_t v_i_3796_, lean_object* v_b_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_a_3806_; uint8_t v___x_3810_; 
v___x_3810_ = lean_usize_dec_lt(v_i_3796_, v_sz_3795_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; 
v___x_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3811_, 0, v_b_3797_);
return v___x_3811_;
}
else
{
lean_object* v_a_3812_; lean_object* v_fst_3813_; lean_object* v_snd_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v_a_3812_ = lean_array_uget_borrowed(v_as_3794_, v_i_3796_);
v_fst_3813_ = lean_ctor_get(v_a_3812_, 0);
v_snd_3814_ = lean_ctor_get(v_a_3812_, 1);
v___x_3815_ = lean_box(0);
v___x_3816_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(v_a_3793_, v_fst_3813_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3817_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___closed__0));
lean_inc(v_fst_3813_);
v___x_3818_ = l_Nat_reprFast(v_fst_3813_);
v___x_3819_ = lean_string_append(v___x_3817_, v___x_3818_);
lean_dec_ref(v___x_3818_);
v___x_3820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___closed__1));
v___x_3821_ = lean_string_append(v___x_3819_, v___x_3820_);
v___x_3822_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3821_);
v___x_3823_ = l_Lean_MessageData_ofFormat(v___x_3822_);
v___x_3824_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0(v_snd_3814_, v___x_3823_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_dec_ref_known(v___x_3824_, 1);
v_a_3806_ = v___x_3815_;
goto v___jp_3805_;
}
else
{
return v___x_3824_;
}
}
else
{
v_a_3806_ = v___x_3815_;
goto v___jp_3805_;
}
}
v___jp_3805_:
{
size_t v___x_3807_; size_t v___x_3808_; 
v___x_3807_ = ((size_t)1ULL);
v___x_3808_ = lean_usize_add(v_i_3796_, v___x_3807_);
v_i_3796_ = v___x_3808_;
v_b_3797_ = v_a_3806_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___boxed(lean_object* v_a_3825_, lean_object* v_as_3826_, lean_object* v_sz_3827_, lean_object* v_i_3828_, lean_object* v_b_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
size_t v_sz_boxed_3837_; size_t v_i_boxed_3838_; lean_object* v_res_3839_; 
v_sz_boxed_3837_ = lean_unbox_usize(v_sz_3827_);
lean_dec(v_sz_3827_);
v_i_boxed_3838_ = lean_unbox_usize(v_i_3828_);
lean_dec(v_i_3828_);
v_res_3839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1(v_a_3825_, v_as_3826_, v_sz_boxed_3837_, v_i_boxed_3838_, v_b_3829_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec(v___y_3831_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v_as_3826_);
lean_dec_ref(v_a_3825_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__2(lean_object* v_x_3840_, lean_object* v_x_3841_){
_start:
{
if (lean_obj_tag(v_x_3841_) == 0)
{
return v_x_3840_;
}
else
{
lean_object* v_key_3842_; lean_object* v_value_3843_; lean_object* v_tail_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v_key_3842_ = lean_ctor_get(v_x_3841_, 0);
v_value_3843_ = lean_ctor_get(v_x_3841_, 1);
v_tail_3844_ = lean_ctor_get(v_x_3841_, 2);
lean_inc(v_value_3843_);
lean_inc(v_key_3842_);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v_key_3842_);
lean_ctor_set(v___x_3845_, 1, v_value_3843_);
v___x_3846_ = lean_array_push(v_x_3840_, v___x_3845_);
v_x_3840_ = v___x_3846_;
v_x_3841_ = v_tail_3844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__2___boxed(lean_object* v_x_3848_, lean_object* v_x_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__2(v_x_3848_, v_x_3849_);
lean_dec(v_x_3849_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3(lean_object* v_as_3851_, size_t v_i_3852_, size_t v_stop_3853_, lean_object* v_b_3854_){
_start:
{
uint8_t v___x_3855_; 
v___x_3855_ = lean_usize_dec_eq(v_i_3852_, v_stop_3853_);
if (v___x_3855_ == 0)
{
lean_object* v___x_3856_; lean_object* v___x_3857_; size_t v___x_3858_; size_t v___x_3859_; 
v___x_3856_ = lean_array_uget_borrowed(v_as_3851_, v_i_3852_);
v___x_3857_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__2(v_b_3854_, v___x_3856_);
v___x_3858_ = ((size_t)1ULL);
v___x_3859_ = lean_usize_add(v_i_3852_, v___x_3858_);
v_i_3852_ = v___x_3859_;
v_b_3854_ = v___x_3857_;
goto _start;
}
else
{
return v_b_3854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3___boxed(lean_object* v_as_3861_, lean_object* v_i_3862_, lean_object* v_stop_3863_, lean_object* v_b_3864_){
_start:
{
size_t v_i_boxed_3865_; size_t v_stop_boxed_3866_; lean_object* v_res_3867_; 
v_i_boxed_3865_ = lean_unbox_usize(v_i_3862_);
lean_dec(v_i_3862_);
v_stop_boxed_3866_ = lean_unbox_usize(v_stop_3863_);
lean_dec(v_stop_3863_);
v_res_3867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3(v_as_3861_, v_i_boxed_3865_, v_stop_boxed_3866_, v_b_3864_);
lean_dec_ref(v_as_3861_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants(lean_object* v_alts_3868_, lean_object* v_invariants_3869_, lean_object* v_inlineHandled_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = lean_unsigned_to_nat(0u);
v___x_3879_ = lean_array_get_size(v_invariants_3869_);
v___x_3880_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg(v___x_3879_, v_alts_3868_, v_invariants_3869_, v___x_3878_, v_inlineHandled_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_);
if (lean_obj_tag(v___x_3880_) == 0)
{
lean_object* v_a_3881_; lean_object* v___y_3883_; lean_object* v_size_3896_; lean_object* v_buckets_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; uint8_t v___x_3900_; 
v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc(v_a_3881_);
lean_dec_ref_known(v___x_3880_, 1);
v_size_3896_ = lean_ctor_get(v_alts_3868_, 0);
v_buckets_3897_ = lean_ctor_get(v_alts_3868_, 1);
v___x_3898_ = lean_mk_empty_array_with_capacity(v_size_3896_);
v___x_3899_ = lean_array_get_size(v_buckets_3897_);
v___x_3900_ = lean_nat_dec_lt(v___x_3878_, v___x_3899_);
if (v___x_3900_ == 0)
{
v___y_3883_ = v___x_3898_;
goto v___jp_3882_;
}
else
{
uint8_t v___x_3901_; 
v___x_3901_ = lean_nat_dec_le(v___x_3899_, v___x_3899_);
if (v___x_3901_ == 0)
{
if (v___x_3900_ == 0)
{
v___y_3883_ = v___x_3898_;
goto v___jp_3882_;
}
else
{
size_t v___x_3902_; size_t v___x_3903_; lean_object* v___x_3904_; 
v___x_3902_ = ((size_t)0ULL);
v___x_3903_ = lean_usize_of_nat(v___x_3899_);
v___x_3904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3(v_buckets_3897_, v___x_3902_, v___x_3903_, v___x_3898_);
v___y_3883_ = v___x_3904_;
goto v___jp_3882_;
}
}
else
{
size_t v___x_3905_; size_t v___x_3906_; lean_object* v___x_3907_; 
v___x_3905_ = ((size_t)0ULL);
v___x_3906_ = lean_usize_of_nat(v___x_3899_);
v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3(v_buckets_3897_, v___x_3905_, v___x_3906_, v___x_3898_);
v___y_3883_ = v___x_3907_;
goto v___jp_3882_;
}
}
v___jp_3882_:
{
lean_object* v___x_3884_; size_t v_sz_3885_; size_t v___x_3886_; lean_object* v___x_3887_; 
v___x_3884_ = lean_box(0);
v_sz_3885_ = lean_array_size(v___y_3883_);
v___x_3886_ = ((size_t)0ULL);
v___x_3887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1(v_a_3881_, v___y_3883_, v_sz_3885_, v___x_3886_, v___x_3884_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_);
lean_dec_ref(v___y_3883_);
lean_dec(v_a_3881_);
if (lean_obj_tag(v___x_3887_) == 0)
{
lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3887_);
if (v_isSharedCheck_3894_ == 0)
{
lean_object* v_unused_3895_; 
v_unused_3895_ = lean_ctor_get(v___x_3887_, 0);
lean_dec(v_unused_3895_);
v___x_3889_ = v___x_3887_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_dec(v___x_3887_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3884_);
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3884_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
else
{
return v___x_3887_;
}
}
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
v_a_3908_ = lean_ctor_get(v___x_3880_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3880_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3880_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3880_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants___boxed(lean_object* v_alts_3916_, lean_object* v_invariants_3917_, lean_object* v_inlineHandled_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants(v_alts_3916_, v_invariants_3917_, v_inlineHandled_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec_ref(v_a_3919_);
lean_dec_ref(v_invariants_3917_);
lean_dec_ref(v_alts_3916_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4(lean_object* v_00_u03b2_3927_, lean_object* v_m_3928_, lean_object* v_a_3929_){
_start:
{
lean_object* v___x_3930_; 
v___x_3930_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg(v_m_3928_, v_a_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___boxed(lean_object* v_00_u03b2_3931_, lean_object* v_m_3932_, lean_object* v_a_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4(v_00_u03b2_3931_, v_m_3932_, v_a_3933_);
lean_dec(v_a_3933_);
lean_dec_ref(v_m_3932_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__5(lean_object* v_00_u03b2_3935_, lean_object* v_m_3936_, lean_object* v_a_3937_, lean_object* v_b_3938_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__5___redArg(v_m_3936_, v_a_3937_, v_b_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6(lean_object* v_upperBound_3940_, lean_object* v_alts_3941_, lean_object* v_invariants_3942_, lean_object* v_inst_3943_, lean_object* v_R_3944_, lean_object* v_a_3945_, lean_object* v_b_3946_, lean_object* v_c_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg(v_upperBound_3940_, v_alts_3941_, v_invariants_3942_, v_a_3945_, v_b_3946_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___boxed(lean_object* v_upperBound_3956_, lean_object* v_alts_3957_, lean_object* v_invariants_3958_, lean_object* v_inst_3959_, lean_object* v_R_3960_, lean_object* v_a_3961_, lean_object* v_b_3962_, lean_object* v_c_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6(v_upperBound_3956_, v_alts_3957_, v_invariants_3958_, v_inst_3959_, v_R_3960_, v_a_3961_, v_b_3962_, v_c_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v___y_3965_);
lean_dec_ref(v___y_3964_);
lean_dec_ref(v_invariants_3958_);
lean_dec_ref(v_alts_3957_);
lean_dec(v_upperBound_3956_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0(lean_object* v_ref_3972_, lean_object* v_msgData_3973_, uint8_t v_severity_3974_, uint8_t v_isSilent_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_){
_start:
{
lean_object* v___x_3983_; 
v___x_3983_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg(v_ref_3972_, v_msgData_3973_, v_severity_3974_, v_isSilent_3975_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
return v___x_3983_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___boxed(lean_object* v_ref_3984_, lean_object* v_msgData_3985_, lean_object* v_severity_3986_, lean_object* v_isSilent_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
uint8_t v_severity_boxed_3995_; uint8_t v_isSilent_boxed_3996_; lean_object* v_res_3997_; 
v_severity_boxed_3995_ = lean_unbox(v_severity_3986_);
v_isSilent_boxed_3996_ = lean_unbox(v_isSilent_3987_);
v_res_3997_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0(v_ref_3984_, v_msgData_3985_, v_severity_boxed_3995_, v_isSilent_boxed_3996_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v_ref_3984_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5(lean_object* v_00_u03b2_3998_, lean_object* v_a_3999_, lean_object* v_x_4000_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg(v_a_3999_, v_x_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___boxed(lean_object* v_00_u03b2_4002_, lean_object* v_a_4003_, lean_object* v_x_4004_){
_start:
{
lean_object* v_res_4005_; 
v_res_4005_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5(v_00_u03b2_4002_, v_a_4003_, v_x_4004_);
lean_dec(v_x_4004_);
lean_dec(v_a_4003_);
return v_res_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___lam__0(lean_object* v_x_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; 
lean_inc(v___y_4008_);
lean_inc_ref(v___y_4007_);
v___x_4014_ = lean_apply_7(v_x_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, lean_box(0));
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___lam__0___boxed(lean_object* v_x_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___lam__0(v_x_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg(lean_object* v_mvarId_4024_, lean_object* v_x_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___f_4033_; lean_object* v___x_4034_; 
lean_inc(v___y_4027_);
lean_inc_ref(v___y_4026_);
v___f_4033_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4033_, 0, v_x_4025_);
lean_closure_set(v___f_4033_, 1, v___y_4026_);
lean_closure_set(v___f_4033_, 2, v___y_4027_);
v___x_4034_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4024_, v___f_4033_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
if (lean_obj_tag(v___x_4034_) == 0)
{
return v___x_4034_;
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4034_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4034_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4034_);
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
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___boxed(lean_object* v_mvarId_4043_, lean_object* v_x_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg(v_mvarId_4043_, v_x_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1(lean_object* v_00_u03b1_4053_, lean_object* v_mvarId_4054_, lean_object* v_x_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg(v_mvarId_4054_, v_x_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___boxed(lean_object* v_00_u03b1_4064_, lean_object* v_mvarId_4065_, lean_object* v_x_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1(v_00_u03b1_4064_, v_mvarId_4065_, v_x_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg(lean_object* v_ref_4075_, lean_object* v_msgData_4076_, uint8_t v_severity_4077_, uint8_t v_isSilent_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; uint8_t v___y_4090_; uint8_t v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4121_; uint8_t v___y_4122_; lean_object* v___y_4123_; uint8_t v___y_4124_; uint8_t v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4146_; uint8_t v___y_4147_; lean_object* v___y_4148_; uint8_t v___y_4149_; lean_object* v___y_4150_; uint8_t v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4157_; uint8_t v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; uint8_t v___y_4161_; lean_object* v___y_4162_; uint8_t v___y_4163_; uint8_t v___x_4168_; lean_object* v___y_4170_; uint8_t v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; uint8_t v___y_4175_; uint8_t v___y_4176_; uint8_t v___y_4178_; uint8_t v___x_4193_; 
v___x_4168_ = 2;
v___x_4193_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4077_, v___x_4168_);
if (v___x_4193_ == 0)
{
v___y_4178_ = v___x_4193_;
goto v___jp_4177_;
}
else
{
uint8_t v___x_4194_; 
lean_inc_ref(v_msgData_4076_);
v___x_4194_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4076_);
v___y_4178_ = v___x_4194_;
goto v___jp_4177_;
}
v___jp_4084_:
{
lean_object* v___x_4094_; lean_object* v_currNamespace_4095_; lean_object* v_openDecls_4096_; lean_object* v_env_4097_; lean_object* v_nextMacroScope_4098_; lean_object* v_ngen_4099_; lean_object* v_auxDeclNGen_4100_; lean_object* v_traceState_4101_; lean_object* v_cache_4102_; lean_object* v_messages_4103_; lean_object* v_infoState_4104_; lean_object* v_snapshotTasks_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4119_; 
v___x_4094_ = lean_st_ref_take(v___y_4093_);
v_currNamespace_4095_ = lean_ctor_get(v___y_4092_, 6);
v_openDecls_4096_ = lean_ctor_get(v___y_4092_, 7);
v_env_4097_ = lean_ctor_get(v___x_4094_, 0);
v_nextMacroScope_4098_ = lean_ctor_get(v___x_4094_, 1);
v_ngen_4099_ = lean_ctor_get(v___x_4094_, 2);
v_auxDeclNGen_4100_ = lean_ctor_get(v___x_4094_, 3);
v_traceState_4101_ = lean_ctor_get(v___x_4094_, 4);
v_cache_4102_ = lean_ctor_get(v___x_4094_, 5);
v_messages_4103_ = lean_ctor_get(v___x_4094_, 6);
v_infoState_4104_ = lean_ctor_get(v___x_4094_, 7);
v_snapshotTasks_4105_ = lean_ctor_get(v___x_4094_, 8);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4094_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4107_ = v___x_4094_;
v_isShared_4108_ = v_isSharedCheck_4119_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_snapshotTasks_4105_);
lean_inc(v_infoState_4104_);
lean_inc(v_messages_4103_);
lean_inc(v_cache_4102_);
lean_inc(v_traceState_4101_);
lean_inc(v_auxDeclNGen_4100_);
lean_inc(v_ngen_4099_);
lean_inc(v_nextMacroScope_4098_);
lean_inc(v_env_4097_);
lean_dec(v___x_4094_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4119_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4114_; 
lean_inc(v_openDecls_4096_);
lean_inc(v_currNamespace_4095_);
v___x_4109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4109_, 0, v_currNamespace_4095_);
lean_ctor_set(v___x_4109_, 1, v_openDecls_4096_);
v___x_4110_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
lean_ctor_set(v___x_4110_, 1, v___y_4089_);
lean_inc_ref(v___y_4087_);
lean_inc_ref(v___y_4088_);
v___x_4111_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4111_, 0, v___y_4088_);
lean_ctor_set(v___x_4111_, 1, v___y_4085_);
lean_ctor_set(v___x_4111_, 2, v___y_4086_);
lean_ctor_set(v___x_4111_, 3, v___y_4087_);
lean_ctor_set(v___x_4111_, 4, v___x_4110_);
lean_ctor_set_uint8(v___x_4111_, sizeof(void*)*5, v___y_4091_);
lean_ctor_set_uint8(v___x_4111_, sizeof(void*)*5 + 1, v___y_4090_);
lean_ctor_set_uint8(v___x_4111_, sizeof(void*)*5 + 2, v_isSilent_4078_);
v___x_4112_ = l_Lean_MessageLog_add(v___x_4111_, v_messages_4103_);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 6, v___x_4112_);
v___x_4114_ = v___x_4107_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_env_4097_);
lean_ctor_set(v_reuseFailAlloc_4118_, 1, v_nextMacroScope_4098_);
lean_ctor_set(v_reuseFailAlloc_4118_, 2, v_ngen_4099_);
lean_ctor_set(v_reuseFailAlloc_4118_, 3, v_auxDeclNGen_4100_);
lean_ctor_set(v_reuseFailAlloc_4118_, 4, v_traceState_4101_);
lean_ctor_set(v_reuseFailAlloc_4118_, 5, v_cache_4102_);
lean_ctor_set(v_reuseFailAlloc_4118_, 6, v___x_4112_);
lean_ctor_set(v_reuseFailAlloc_4118_, 7, v_infoState_4104_);
lean_ctor_set(v_reuseFailAlloc_4118_, 8, v_snapshotTasks_4105_);
v___x_4114_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v___x_4115_ = lean_st_ref_set(v___y_4093_, v___x_4114_);
v___x_4116_ = lean_box(0);
v___x_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
return v___x_4117_;
}
}
}
v___jp_4120_:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4144_; 
v___x_4129_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4076_);
v___x_4130_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v___x_4129_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4133_ = v___x_4130_;
v_isShared_4134_ = v_isSharedCheck_4144_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4130_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4144_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
lean_inc_ref_n(v___y_4127_, 2);
v___x_4135_ = l_Lean_FileMap_toPosition(v___y_4127_, v___y_4126_);
lean_dec(v___y_4126_);
v___x_4136_ = l_Lean_FileMap_toPosition(v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
v___x_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
v___x_4138_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___closed__0));
if (v___y_4122_ == 0)
{
lean_del_object(v___x_4133_);
lean_dec_ref(v___y_4121_);
v___y_4085_ = v___x_4135_;
v___y_4086_ = v___x_4137_;
v___y_4087_ = v___x_4138_;
v___y_4088_ = v___y_4123_;
v___y_4089_ = v_a_4131_;
v___y_4090_ = v___y_4124_;
v___y_4091_ = v___y_4125_;
v___y_4092_ = v___y_4081_;
v___y_4093_ = v___y_4082_;
goto v___jp_4084_;
}
else
{
uint8_t v___x_4139_; 
lean_inc(v_a_4131_);
v___x_4139_ = l_Lean_MessageData_hasTag(v___y_4121_, v_a_4131_);
if (v___x_4139_ == 0)
{
lean_object* v___x_4140_; lean_object* v___x_4142_; 
lean_dec_ref_known(v___x_4137_, 1);
lean_dec_ref(v___x_4135_);
lean_dec(v_a_4131_);
v___x_4140_ = lean_box(0);
if (v_isShared_4134_ == 0)
{
lean_ctor_set(v___x_4133_, 0, v___x_4140_);
v___x_4142_ = v___x_4133_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4140_);
v___x_4142_ = v_reuseFailAlloc_4143_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
return v___x_4142_;
}
}
else
{
lean_del_object(v___x_4133_);
v___y_4085_ = v___x_4135_;
v___y_4086_ = v___x_4137_;
v___y_4087_ = v___x_4138_;
v___y_4088_ = v___y_4123_;
v___y_4089_ = v_a_4131_;
v___y_4090_ = v___y_4124_;
v___y_4091_ = v___y_4125_;
v___y_4092_ = v___y_4081_;
v___y_4093_ = v___y_4082_;
goto v___jp_4084_;
}
}
}
}
v___jp_4145_:
{
lean_object* v___x_4154_; 
v___x_4154_ = l_Lean_Syntax_getTailPos_x3f(v___y_4150_, v___y_4151_);
lean_dec(v___y_4150_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_inc(v___y_4153_);
v___y_4121_ = v___y_4146_;
v___y_4122_ = v___y_4147_;
v___y_4123_ = v___y_4148_;
v___y_4124_ = v___y_4149_;
v___y_4125_ = v___y_4151_;
v___y_4126_ = v___y_4153_;
v___y_4127_ = v___y_4152_;
v___y_4128_ = v___y_4153_;
goto v___jp_4120_;
}
else
{
lean_object* v_val_4155_; 
v_val_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc(v_val_4155_);
lean_dec_ref_known(v___x_4154_, 1);
v___y_4121_ = v___y_4146_;
v___y_4122_ = v___y_4147_;
v___y_4123_ = v___y_4148_;
v___y_4124_ = v___y_4149_;
v___y_4125_ = v___y_4151_;
v___y_4126_ = v___y_4153_;
v___y_4127_ = v___y_4152_;
v___y_4128_ = v_val_4155_;
goto v___jp_4120_;
}
}
v___jp_4156_:
{
lean_object* v_ref_4164_; lean_object* v___x_4165_; 
v_ref_4164_ = l_Lean_replaceRef(v_ref_4075_, v___y_4160_);
v___x_4165_ = l_Lean_Syntax_getPos_x3f(v_ref_4164_, v___y_4161_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v___x_4166_; 
v___x_4166_ = lean_unsigned_to_nat(0u);
v___y_4146_ = v___y_4157_;
v___y_4147_ = v___y_4158_;
v___y_4148_ = v___y_4159_;
v___y_4149_ = v___y_4163_;
v___y_4150_ = v_ref_4164_;
v___y_4151_ = v___y_4161_;
v___y_4152_ = v___y_4162_;
v___y_4153_ = v___x_4166_;
goto v___jp_4145_;
}
else
{
lean_object* v_val_4167_; 
v_val_4167_ = lean_ctor_get(v___x_4165_, 0);
lean_inc(v_val_4167_);
lean_dec_ref_known(v___x_4165_, 1);
v___y_4146_ = v___y_4157_;
v___y_4147_ = v___y_4158_;
v___y_4148_ = v___y_4159_;
v___y_4149_ = v___y_4163_;
v___y_4150_ = v_ref_4164_;
v___y_4151_ = v___y_4161_;
v___y_4152_ = v___y_4162_;
v___y_4153_ = v_val_4167_;
goto v___jp_4145_;
}
}
v___jp_4169_:
{
if (v___y_4176_ == 0)
{
v___y_4157_ = v___y_4170_;
v___y_4158_ = v___y_4171_;
v___y_4159_ = v___y_4172_;
v___y_4160_ = v___y_4173_;
v___y_4161_ = v___y_4175_;
v___y_4162_ = v___y_4174_;
v___y_4163_ = v_severity_4077_;
goto v___jp_4156_;
}
else
{
v___y_4157_ = v___y_4170_;
v___y_4158_ = v___y_4171_;
v___y_4159_ = v___y_4172_;
v___y_4160_ = v___y_4173_;
v___y_4161_ = v___y_4175_;
v___y_4162_ = v___y_4174_;
v___y_4163_ = v___x_4168_;
goto v___jp_4156_;
}
}
v___jp_4177_:
{
if (v___y_4178_ == 0)
{
lean_object* v_fileName_4179_; lean_object* v_fileMap_4180_; lean_object* v_options_4181_; lean_object* v_ref_4182_; uint8_t v_suppressElabErrors_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___f_4186_; uint8_t v___x_4187_; uint8_t v___x_4188_; 
v_fileName_4179_ = lean_ctor_get(v___y_4081_, 0);
v_fileMap_4180_ = lean_ctor_get(v___y_4081_, 1);
v_options_4181_ = lean_ctor_get(v___y_4081_, 2);
v_ref_4182_ = lean_ctor_get(v___y_4081_, 5);
v_suppressElabErrors_4183_ = lean_ctor_get_uint8(v___y_4081_, sizeof(void*)*14 + 1);
v___x_4184_ = lean_box(v___y_4178_);
v___x_4185_ = lean_box(v_suppressElabErrors_4183_);
v___f_4186_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4186_, 0, v___x_4184_);
lean_closure_set(v___f_4186_, 1, v___x_4185_);
v___x_4187_ = 1;
v___x_4188_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4077_, v___x_4187_);
if (v___x_4188_ == 0)
{
v___y_4170_ = v___f_4186_;
v___y_4171_ = v_suppressElabErrors_4183_;
v___y_4172_ = v_fileName_4179_;
v___y_4173_ = v_ref_4182_;
v___y_4174_ = v_fileMap_4180_;
v___y_4175_ = v___y_4178_;
v___y_4176_ = v___x_4188_;
goto v___jp_4169_;
}
else
{
lean_object* v___x_4189_; uint8_t v___x_4190_; 
v___x_4189_ = l_Lean_warningAsError;
v___x_4190_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_options_4181_, v___x_4189_);
v___y_4170_ = v___f_4186_;
v___y_4171_ = v_suppressElabErrors_4183_;
v___y_4172_ = v_fileName_4179_;
v___y_4173_ = v_ref_4182_;
v___y_4174_ = v_fileMap_4180_;
v___y_4175_ = v___y_4178_;
v___y_4176_ = v___x_4190_;
goto v___jp_4169_;
}
}
else
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_dec_ref(v_msgData_4076_);
v___x_4191_ = lean_box(0);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg___boxed(lean_object* v_ref_4195_, lean_object* v_msgData_4196_, lean_object* v_severity_4197_, lean_object* v_isSilent_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
uint8_t v_severity_boxed_4204_; uint8_t v_isSilent_boxed_4205_; lean_object* v_res_4206_; 
v_severity_boxed_4204_ = lean_unbox(v_severity_4197_);
v_isSilent_boxed_4205_ = lean_unbox(v_isSilent_4198_);
v_res_4206_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg(v_ref_4195_, v_msgData_4196_, v_severity_boxed_4204_, v_isSilent_boxed_4205_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_);
lean_dec(v___y_4202_);
lean_dec_ref(v___y_4201_);
lean_dec(v___y_4200_);
lean_dec_ref(v___y_4199_);
lean_dec(v_ref_4195_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0(lean_object* v_ref_4207_, lean_object* v_msgData_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
uint8_t v___x_4216_; uint8_t v___x_4217_; lean_object* v___x_4218_; 
v___x_4216_ = 1;
v___x_4217_ = 0;
v___x_4218_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg(v_ref_4207_, v_msgData_4208_, v___x_4216_, v___x_4217_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0___boxed(lean_object* v_ref_4219_, lean_object* v_msgData_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0(v_ref_4219_, v_msgData_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v_ref_4219_);
return v_res_4228_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
v___x_4236_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__2));
v___x_4237_ = l_Lean_MessageData_ofFormat(v___x_4236_);
return v___x_4237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0(lean_object* v_stx_4238_, lean_object* v_goal_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v___y_4248_; lean_object* v___y_4249_; uint8_t v___y_4250_; uint8_t v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; uint8_t v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; uint8_t v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v_options_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v_options_4406_ = lean_ctor_get(v___y_4244_, 2);
v___x_4407_ = l_Lean_Elab_Tactic_Do_mvcgen_warning;
v___x_4408_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_options_4406_, v___x_4407_);
if (v___x_4408_ == 0)
{
v___y_4279_ = v___y_4240_;
v___y_4280_ = v___y_4241_;
v___y_4281_ = v___y_4242_;
v___y_4282_ = v___y_4243_;
v___y_4283_ = v___y_4244_;
v___y_4284_ = v___y_4245_;
goto v___jp_4278_;
}
else
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
v___x_4409_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__3);
v___x_4410_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0(v_stx_4238_, v___x_4409_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_dec_ref_known(v___x_4410_, 1);
v___y_4279_ = v___y_4240_;
v___y_4280_ = v___y_4241_;
v___y_4281_ = v___y_4242_;
v___y_4282_ = v___y_4243_;
v___y_4283_ = v___y_4244_;
v___y_4284_ = v___y_4245_;
goto v___jp_4278_;
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_goal_4239_);
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4410_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4410_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
v___jp_4247_:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4275_ = lean_alloc_ctor(0, 19, 4);
lean_ctor_set(v___x_4275_, 0, v___y_4258_);
lean_ctor_set(v___x_4275_, 1, v___y_4265_);
lean_ctor_set(v___x_4275_, 2, v___y_4252_);
lean_ctor_set(v___x_4275_, 3, v___y_4264_);
lean_ctor_set(v___x_4275_, 4, v___y_4249_);
lean_ctor_set(v___x_4275_, 5, v___y_4270_);
lean_ctor_set(v___x_4275_, 6, v___y_4267_);
lean_ctor_set(v___x_4275_, 7, v___y_4253_);
lean_ctor_set(v___x_4275_, 8, v___y_4254_);
lean_ctor_set(v___x_4275_, 9, v___y_4260_);
lean_ctor_set(v___x_4275_, 10, v___y_4266_);
lean_ctor_set(v___x_4275_, 11, v___y_4248_);
lean_ctor_set(v___x_4275_, 12, v___y_4269_);
lean_ctor_set(v___x_4275_, 13, v___y_4256_);
lean_ctor_set(v___x_4275_, 14, v___y_4257_);
lean_ctor_set(v___x_4275_, 15, v___y_4261_);
lean_ctor_set(v___x_4275_, 16, v___y_4273_);
lean_ctor_set(v___x_4275_, 17, v___y_4268_);
lean_ctor_set(v___x_4275_, 18, v___y_4274_);
lean_ctor_set_uint8(v___x_4275_, sizeof(void*)*19, v___y_4250_);
lean_ctor_set_uint8(v___x_4275_, sizeof(void*)*19 + 1, v___y_4251_);
lean_ctor_set_uint8(v___x_4275_, sizeof(void*)*19 + 2, v___y_4271_);
lean_ctor_set_uint8(v___x_4275_, sizeof(void*)*19 + 3, v___y_4262_);
v___x_4276_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4276_, 0, v___y_4272_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
lean_ctor_set(v___x_4276_, 2, v___y_4263_);
lean_ctor_set(v___x_4276_, 3, v___y_4259_);
lean_ctor_set(v___x_4276_, 4, v___y_4255_);
v___x_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4277_, 0, v___x_4276_);
return v___x_4277_;
}
v___jp_4278_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; uint8_t v___x_4287_; uint8_t v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4285_ = lean_unsigned_to_nat(1u);
v___x_4286_ = l_Lean_Syntax_getArg(v_stx_4238_, v___x_4285_);
v___x_4287_ = 1;
v___x_4288_ = 0;
v___x_4289_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__0));
v___x_4290_ = lean_box(v___x_4287_);
v___x_4291_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabConfig___boxed), 12, 3);
lean_closure_set(v___x_4291_, 0, v___x_4286_);
lean_closure_set(v___x_4291_, 1, v___x_4289_);
lean_closure_set(v___x_4291_, 2, v___x_4290_);
v___x_4292_ = lean_box(0);
v___x_4293_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg(v___x_4291_, v___x_4292_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4295_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v___x_4293_, 1);
v___x_4295_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig(v_a_4294_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
lean_dec_ref_known(v___x_4295_, 1);
v___x_4296_ = lean_unsigned_to_nat(2u);
v___x_4297_ = l_Lean_Syntax_getArg(v_stx_4238_, v___x_4296_);
lean_inc(v_goal_4239_);
v___x_4298_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext(v___x_4297_, v_goal_4239_, v___x_4288_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___x_4297_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v_fst_4300_; lean_object* v_snd_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
lean_dec_ref_known(v___x_4298_, 1);
v_fst_4300_ = lean_ctor_get(v_a_4299_, 0);
lean_inc(v_fst_4300_);
v_snd_4301_ = lean_ctor_get(v_a_4299_, 1);
lean_inc(v_snd_4301_);
lean_dec(v_a_4299_);
v___x_4302_ = lean_unsigned_to_nat(4u);
v___x_4303_ = l_Lean_Syntax_getArg(v_stx_4238_, v___x_4302_);
v___x_4304_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions(v___x_4303_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___x_4303_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
lean_inc(v_a_4305_);
lean_dec_ref_known(v___x_4304_, 1);
v___x_4306_ = lean_unsigned_to_nat(5u);
v___x_4307_ = l_Lean_Syntax_getArg(v_stx_4238_, v___x_4306_);
v___x_4308_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabPreTac(v_goal_4239_, v___x_4307_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___x_4307_);
if (lean_obj_tag(v___x_4308_) == 0)
{
lean_object* v_a_4309_; lean_object* v_fst_4310_; lean_object* v_snd_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; 
v_a_4309_ = lean_ctor_get(v___x_4308_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4308_, 1);
v_fst_4310_ = lean_ctor_get(v_a_4309_, 0);
lean_inc(v_fst_4310_);
v_snd_4311_ = lean_ctor_get(v_a_4309_, 1);
lean_inc(v_snd_4311_);
lean_dec(v_a_4309_);
v___x_4312_ = lean_unsigned_to_nat(3u);
v___x_4313_ = l_Lean_Syntax_getArg(v_stx_4238_, v___x_4312_);
v___x_4314_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap(v___x_4313_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
lean_dec(v___x_4313_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
if (lean_obj_tag(v_a_4315_) == 0)
{
lean_object* v_entailsConsIntroRule_4316_; lean_object* v_entailsNilPureIntroRule_4317_; lean_object* v_entailsNilIntroRule_4318_; lean_object* v_applyPureConsEntailsLRule_4319_; lean_object* v_applyPureConsEntailsRRule_4320_; lean_object* v_downPureIntroRule_4321_; lean_object* v_pureElimRule_4322_; lean_object* v_pureIntroRule_4323_; lean_object* v_postCondEntailsRflRule_4324_; lean_object* v_postCondEntailsMkRule_4325_; lean_object* v_exceptCondsEntailsRflRule_4326_; lean_object* v_exceptCondsEntailsPureRule_4327_; lean_object* v_exceptCondsEntailsFalseRule_4328_; lean_object* v_exceptCondsEntailsTrueRule_4329_; lean_object* v_tripleOfEntailsWPRule_4330_; lean_object* v_andIntroRule_4331_; uint8_t v_trivial_4332_; uint8_t v_jp_4333_; uint8_t v_errorOnMissingSpec_4334_; uint8_t v_debug_4335_; lean_object* v___x_4336_; 
v_entailsConsIntroRule_4316_ = lean_ctor_get(v_fst_4300_, 0);
lean_inc_ref(v_entailsConsIntroRule_4316_);
v_entailsNilPureIntroRule_4317_ = lean_ctor_get(v_fst_4300_, 1);
lean_inc_ref(v_entailsNilPureIntroRule_4317_);
v_entailsNilIntroRule_4318_ = lean_ctor_get(v_fst_4300_, 2);
lean_inc_ref(v_entailsNilIntroRule_4318_);
v_applyPureConsEntailsLRule_4319_ = lean_ctor_get(v_fst_4300_, 3);
lean_inc_ref(v_applyPureConsEntailsLRule_4319_);
v_applyPureConsEntailsRRule_4320_ = lean_ctor_get(v_fst_4300_, 4);
lean_inc_ref(v_applyPureConsEntailsRRule_4320_);
v_downPureIntroRule_4321_ = lean_ctor_get(v_fst_4300_, 5);
lean_inc_ref(v_downPureIntroRule_4321_);
v_pureElimRule_4322_ = lean_ctor_get(v_fst_4300_, 6);
lean_inc_ref(v_pureElimRule_4322_);
v_pureIntroRule_4323_ = lean_ctor_get(v_fst_4300_, 7);
lean_inc_ref(v_pureIntroRule_4323_);
v_postCondEntailsRflRule_4324_ = lean_ctor_get(v_fst_4300_, 8);
lean_inc_ref(v_postCondEntailsRflRule_4324_);
v_postCondEntailsMkRule_4325_ = lean_ctor_get(v_fst_4300_, 9);
lean_inc_ref(v_postCondEntailsMkRule_4325_);
v_exceptCondsEntailsRflRule_4326_ = lean_ctor_get(v_fst_4300_, 10);
lean_inc_ref(v_exceptCondsEntailsRflRule_4326_);
v_exceptCondsEntailsPureRule_4327_ = lean_ctor_get(v_fst_4300_, 11);
lean_inc_ref(v_exceptCondsEntailsPureRule_4327_);
v_exceptCondsEntailsFalseRule_4328_ = lean_ctor_get(v_fst_4300_, 12);
lean_inc_ref(v_exceptCondsEntailsFalseRule_4328_);
v_exceptCondsEntailsTrueRule_4329_ = lean_ctor_get(v_fst_4300_, 13);
lean_inc_ref(v_exceptCondsEntailsTrueRule_4329_);
v_tripleOfEntailsWPRule_4330_ = lean_ctor_get(v_fst_4300_, 14);
lean_inc_ref(v_tripleOfEntailsWPRule_4330_);
v_andIntroRule_4331_ = lean_ctor_get(v_fst_4300_, 15);
lean_inc_ref(v_andIntroRule_4331_);
lean_dec(v_fst_4300_);
v_trivial_4332_ = lean_ctor_get_uint8(v_a_4294_, sizeof(void*)*1);
v_jp_4333_ = lean_ctor_get_uint8(v_a_4294_, sizeof(void*)*1 + 3);
v_errorOnMissingSpec_4334_ = lean_ctor_get_uint8(v_a_4294_, sizeof(void*)*1 + 4);
v_debug_4335_ = lean_ctor_get_uint8(v_a_4294_, sizeof(void*)*1 + 5);
v___x_4336_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__41);
v___y_4248_ = v_exceptCondsEntailsPureRule_4327_;
v___y_4249_ = v_applyPureConsEntailsRRule_4320_;
v___y_4250_ = v_trivial_4332_;
v___y_4251_ = v_jp_4333_;
v___y_4252_ = v_entailsNilIntroRule_4318_;
v___y_4253_ = v_pureIntroRule_4323_;
v___y_4254_ = v_postCondEntailsRflRule_4324_;
v___y_4255_ = v_a_4315_;
v___y_4256_ = v_exceptCondsEntailsTrueRule_4329_;
v___y_4257_ = v_tripleOfEntailsWPRule_4330_;
v___y_4258_ = v_entailsConsIntroRule_4316_;
v___y_4259_ = v_snd_4311_;
v___y_4260_ = v_postCondEntailsMkRule_4325_;
v___y_4261_ = v_andIntroRule_4331_;
v___y_4262_ = v_debug_4335_;
v___y_4263_ = v_snd_4301_;
v___y_4264_ = v_applyPureConsEntailsLRule_4319_;
v___y_4265_ = v_entailsNilPureIntroRule_4317_;
v___y_4266_ = v_exceptCondsEntailsRflRule_4326_;
v___y_4267_ = v_pureElimRule_4322_;
v___y_4268_ = v_fst_4310_;
v___y_4269_ = v_exceptCondsEntailsFalseRule_4328_;
v___y_4270_ = v_downPureIntroRule_4321_;
v___y_4271_ = v_errorOnMissingSpec_4334_;
v___y_4272_ = v_a_4294_;
v___y_4273_ = v_a_4305_;
v___y_4274_ = v___x_4336_;
goto v___jp_4247_;
}
else
{
lean_object* v_entailsConsIntroRule_4337_; lean_object* v_entailsNilPureIntroRule_4338_; lean_object* v_entailsNilIntroRule_4339_; lean_object* v_applyPureConsEntailsLRule_4340_; lean_object* v_applyPureConsEntailsRRule_4341_; lean_object* v_downPureIntroRule_4342_; lean_object* v_pureElimRule_4343_; lean_object* v_pureIntroRule_4344_; lean_object* v_postCondEntailsRflRule_4345_; lean_object* v_postCondEntailsMkRule_4346_; lean_object* v_exceptCondsEntailsRflRule_4347_; lean_object* v_exceptCondsEntailsPureRule_4348_; lean_object* v_exceptCondsEntailsFalseRule_4349_; lean_object* v_exceptCondsEntailsTrueRule_4350_; lean_object* v_tripleOfEntailsWPRule_4351_; lean_object* v_andIntroRule_4352_; uint8_t v_trivial_4353_; uint8_t v_jp_4354_; uint8_t v_errorOnMissingSpec_4355_; uint8_t v_debug_4356_; lean_object* v_val_4357_; 
v_entailsConsIntroRule_4337_ = lean_ctor_get(v_fst_4300_, 0);
lean_inc_ref(v_entailsConsIntroRule_4337_);
v_entailsNilPureIntroRule_4338_ = lean_ctor_get(v_fst_4300_, 1);
lean_inc_ref(v_entailsNilPureIntroRule_4338_);
v_entailsNilIntroRule_4339_ = lean_ctor_get(v_fst_4300_, 2);
lean_inc_ref(v_entailsNilIntroRule_4339_);
v_applyPureConsEntailsLRule_4340_ = lean_ctor_get(v_fst_4300_, 3);
lean_inc_ref(v_applyPureConsEntailsLRule_4340_);
v_applyPureConsEntailsRRule_4341_ = lean_ctor_get(v_fst_4300_, 4);
lean_inc_ref(v_applyPureConsEntailsRRule_4341_);
v_downPureIntroRule_4342_ = lean_ctor_get(v_fst_4300_, 5);
lean_inc_ref(v_downPureIntroRule_4342_);
v_pureElimRule_4343_ = lean_ctor_get(v_fst_4300_, 6);
lean_inc_ref(v_pureElimRule_4343_);
v_pureIntroRule_4344_ = lean_ctor_get(v_fst_4300_, 7);
lean_inc_ref(v_pureIntroRule_4344_);
v_postCondEntailsRflRule_4345_ = lean_ctor_get(v_fst_4300_, 8);
lean_inc_ref(v_postCondEntailsRflRule_4345_);
v_postCondEntailsMkRule_4346_ = lean_ctor_get(v_fst_4300_, 9);
lean_inc_ref(v_postCondEntailsMkRule_4346_);
v_exceptCondsEntailsRflRule_4347_ = lean_ctor_get(v_fst_4300_, 10);
lean_inc_ref(v_exceptCondsEntailsRflRule_4347_);
v_exceptCondsEntailsPureRule_4348_ = lean_ctor_get(v_fst_4300_, 11);
lean_inc_ref(v_exceptCondsEntailsPureRule_4348_);
v_exceptCondsEntailsFalseRule_4349_ = lean_ctor_get(v_fst_4300_, 12);
lean_inc_ref(v_exceptCondsEntailsFalseRule_4349_);
v_exceptCondsEntailsTrueRule_4350_ = lean_ctor_get(v_fst_4300_, 13);
lean_inc_ref(v_exceptCondsEntailsTrueRule_4350_);
v_tripleOfEntailsWPRule_4351_ = lean_ctor_get(v_fst_4300_, 14);
lean_inc_ref(v_tripleOfEntailsWPRule_4351_);
v_andIntroRule_4352_ = lean_ctor_get(v_fst_4300_, 15);
lean_inc_ref(v_andIntroRule_4352_);
lean_dec(v_fst_4300_);
v_trivial_4353_ = lean_ctor_get_uint8(v_a_4294_, sizeof(void*)*1);
v_jp_4354_ = lean_ctor_get_uint8(v_a_4294_, sizeof(void*)*1 + 3);
v_errorOnMissingSpec_4355_ = lean_ctor_get_uint8(v_a_4294_, sizeof(void*)*1 + 4);
v_debug_4356_ = lean_ctor_get_uint8(v_a_4294_, sizeof(void*)*1 + 5);
v_val_4357_ = lean_ctor_get(v_a_4315_, 0);
lean_inc(v_val_4357_);
v___y_4248_ = v_exceptCondsEntailsPureRule_4348_;
v___y_4249_ = v_applyPureConsEntailsRRule_4341_;
v___y_4250_ = v_trivial_4353_;
v___y_4251_ = v_jp_4354_;
v___y_4252_ = v_entailsNilIntroRule_4339_;
v___y_4253_ = v_pureIntroRule_4344_;
v___y_4254_ = v_postCondEntailsRflRule_4345_;
v___y_4255_ = v_a_4315_;
v___y_4256_ = v_exceptCondsEntailsTrueRule_4350_;
v___y_4257_ = v_tripleOfEntailsWPRule_4351_;
v___y_4258_ = v_entailsConsIntroRule_4337_;
v___y_4259_ = v_snd_4311_;
v___y_4260_ = v_postCondEntailsMkRule_4346_;
v___y_4261_ = v_andIntroRule_4352_;
v___y_4262_ = v_debug_4356_;
v___y_4263_ = v_snd_4301_;
v___y_4264_ = v_applyPureConsEntailsLRule_4340_;
v___y_4265_ = v_entailsNilPureIntroRule_4338_;
v___y_4266_ = v_exceptCondsEntailsRflRule_4347_;
v___y_4267_ = v_pureElimRule_4343_;
v___y_4268_ = v_fst_4310_;
v___y_4269_ = v_exceptCondsEntailsFalseRule_4349_;
v___y_4270_ = v_downPureIntroRule_4342_;
v___y_4271_ = v_errorOnMissingSpec_4355_;
v___y_4272_ = v_a_4294_;
v___y_4273_ = v_a_4305_;
v___y_4274_ = v_val_4357_;
goto v___jp_4247_;
}
}
else
{
lean_object* v_a_4358_; lean_object* v___x_4360_; uint8_t v_isShared_4361_; uint8_t v_isSharedCheck_4365_; 
lean_dec(v_snd_4311_);
lean_dec(v_fst_4310_);
lean_dec(v_a_4305_);
lean_dec(v_snd_4301_);
lean_dec(v_fst_4300_);
lean_dec(v_a_4294_);
v_a_4358_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4365_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4365_ == 0)
{
v___x_4360_ = v___x_4314_;
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
else
{
lean_inc(v_a_4358_);
lean_dec(v___x_4314_);
v___x_4360_ = lean_box(0);
v_isShared_4361_ = v_isSharedCheck_4365_;
goto v_resetjp_4359_;
}
v_resetjp_4359_:
{
lean_object* v___x_4363_; 
if (v_isShared_4361_ == 0)
{
v___x_4363_ = v___x_4360_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v_a_4358_);
v___x_4363_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
return v___x_4363_;
}
}
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec(v_a_4305_);
lean_dec(v_snd_4301_);
lean_dec(v_fst_4300_);
lean_dec(v_a_4294_);
v_a_4366_ = lean_ctor_get(v___x_4308_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4308_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4308_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4308_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
else
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4381_; 
lean_dec(v_snd_4301_);
lean_dec(v_fst_4300_);
lean_dec(v_a_4294_);
lean_dec(v_goal_4239_);
v_a_4374_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4376_ = v___x_4304_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4304_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
lean_dec(v_a_4294_);
lean_dec(v_goal_4239_);
v_a_4382_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4298_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4298_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_dec(v_a_4294_);
lean_dec(v_goal_4239_);
v_a_4390_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4295_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4295_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
lean_dec(v_goal_4239_);
v_a_4398_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4293_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4293_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___boxed(lean_object* v_stx_4419_, lean_object* v_goal_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0(v_stx_4419_, v_goal_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
lean_dec_ref(v___y_4421_);
lean_dec(v_stx_4419_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs(lean_object* v_stx_4429_, lean_object* v_goal_4430_, lean_object* v_a_4431_, lean_object* v_a_4432_, lean_object* v_a_4433_, lean_object* v_a_4434_, lean_object* v_a_4435_, lean_object* v_a_4436_){
_start:
{
lean_object* v___f_4438_; lean_object* v___x_4439_; 
lean_inc(v_goal_4430_);
v___f_4438_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4438_, 0, v_stx_4429_);
lean_closure_set(v___f_4438_, 1, v_goal_4430_);
v___x_4439_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg(v_goal_4430_, v___f_4438_, v_a_4431_, v_a_4432_, v_a_4433_, v_a_4434_, v_a_4435_, v_a_4436_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___boxed(lean_object* v_stx_4440_, lean_object* v_goal_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_){
_start:
{
lean_object* v_res_4449_; 
v_res_4449_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs(v_stx_4440_, v_goal_4441_, v_a_4442_, v_a_4443_, v_a_4444_, v_a_4445_, v_a_4446_, v_a_4447_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
lean_dec(v_a_4445_);
lean_dec_ref(v_a_4444_);
lean_dec(v_a_4443_);
lean_dec_ref(v_a_4442_);
return v_res_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0(lean_object* v_ref_4450_, lean_object* v_msgData_4451_, uint8_t v_severity_4452_, uint8_t v_isSilent_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v___x_4461_; 
v___x_4461_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg(v_ref_4450_, v_msgData_4451_, v_severity_4452_, v_isSilent_4453_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_);
return v___x_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___boxed(lean_object* v_ref_4462_, lean_object* v_msgData_4463_, lean_object* v_severity_4464_, lean_object* v_isSilent_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
uint8_t v_severity_boxed_4473_; uint8_t v_isSilent_boxed_4474_; lean_object* v_res_4475_; 
v_severity_boxed_4473_ = lean_unbox(v_severity_4464_);
v_isSilent_boxed_4474_ = lean_unbox(v_isSilent_4465_);
v_res_4475_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0(v_ref_4462_, v_msgData_4463_, v_severity_boxed_4473_, v_isSilent_boxed_4474_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec_ref(v___y_4468_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v_ref_4462_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__0(lean_object* v_a_4476_, lean_object* v_ctx_4477_, lean_object* v_scope_4478_, lean_object* v_stepLimit_4479_, lean_object* v_invariantAlts_x3f_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_){
_start:
{
lean_object* v___x_4491_; 
v___x_4491_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run(v_a_4476_, v_ctx_4477_, v_scope_4478_, v_stepLimit_4479_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
if (lean_obj_tag(v___x_4491_) == 0)
{
if (lean_obj_tag(v_invariantAlts_x3f_4480_) == 1)
{
lean_object* v_a_4492_; lean_object* v_val_4493_; lean_object* v_invariants_4494_; lean_object* v_inlineHandledInvariants_4495_; lean_object* v___x_4496_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v___x_4491_, 1);
v_val_4493_ = lean_ctor_get(v_invariantAlts_x3f_4480_, 0);
v_invariants_4494_ = lean_ctor_get(v_a_4492_, 0);
v_inlineHandledInvariants_4495_ = lean_ctor_get(v_a_4492_, 2);
lean_inc_ref(v_inlineHandledInvariants_4495_);
v___x_4496_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants(v_val_4493_, v_invariants_4494_, v_inlineHandledInvariants_4495_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4503_ == 0)
{
lean_object* v_unused_4504_; 
v_unused_4504_ = lean_ctor_get(v___x_4496_, 0);
lean_dec(v_unused_4504_);
v___x_4498_ = v___x_4496_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_dec(v___x_4496_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
lean_ctor_set(v___x_4498_, 0, v_a_4492_);
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4492_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
lean_dec(v_a_4492_);
v_a_4505_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4496_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4496_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
else
{
return v___x_4491_;
}
}
else
{
return v___x_4491_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__0___boxed(lean_object* v_a_4513_, lean_object* v_ctx_4514_, lean_object* v_scope_4515_, lean_object* v_stepLimit_4516_, lean_object* v_invariantAlts_x3f_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_){
_start:
{
lean_object* v_res_4528_; 
v_res_4528_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__0(v_a_4513_, v_ctx_4514_, v_scope_4515_, v_stepLimit_4516_, v_invariantAlts_x3f_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
lean_dec(v___y_4526_);
lean_dec_ref(v___y_4525_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec(v_invariantAlts_x3f_4517_);
lean_dec_ref(v_ctx_4514_);
return v_res_4528_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__1(lean_object* v_x_4529_, lean_object* v_x_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
if (lean_obj_tag(v_x_4529_) == 0)
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
v___x_4541_ = l_List_reverse___redArg(v_x_4530_);
v___x_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4541_);
return v___x_4542_;
}
else
{
lean_object* v_head_4543_; lean_object* v_tail_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4562_; 
v_head_4543_ = lean_ctor_get(v_x_4529_, 0);
v_tail_4544_ = lean_ctor_get(v_x_4529_, 1);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_x_4529_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4546_ = v_x_4529_;
v_isShared_4547_ = v_isSharedCheck_4562_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_tail_4544_);
lean_inc(v_head_4543_);
lean_dec(v_x_4529_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4562_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Lean_Meta_Grind_mkGoalCore(v_head_4543_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_object* v_a_4549_; lean_object* v___x_4551_; 
v_a_4549_ = lean_ctor_get(v___x_4548_, 0);
lean_inc(v_a_4549_);
lean_dec_ref_known(v___x_4548_, 1);
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 1, v_x_4530_);
lean_ctor_set(v___x_4546_, 0, v_a_4549_);
v___x_4551_ = v___x_4546_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4549_);
lean_ctor_set(v_reuseFailAlloc_4553_, 1, v_x_4530_);
v___x_4551_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
v_x_4529_ = v_tail_4544_;
v_x_4530_ = v___x_4551_;
goto _start;
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_del_object(v___x_4546_);
lean_dec(v_tail_4544_);
lean_dec(v_x_4530_);
v_a_4554_ = lean_ctor_get(v___x_4548_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4548_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4548_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__1___boxed(lean_object* v_x_4563_, lean_object* v_x_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
lean_object* v_res_4575_; 
v_res_4575_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__1(v_x_4563_, v_x_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec(v___y_4565_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__2(lean_object* v_x_4576_, lean_object* v_x_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
if (lean_obj_tag(v_x_4576_) == 0)
{
lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4588_ = l_List_reverse___redArg(v_x_4577_);
v___x_4589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4588_);
return v___x_4589_;
}
else
{
lean_object* v_head_4590_; lean_object* v_tail_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4610_; 
v_head_4590_ = lean_ctor_get(v_x_4576_, 0);
v_tail_4591_ = lean_ctor_get(v_x_4576_, 1);
v_isSharedCheck_4610_ = !lean_is_exclusive(v_x_4576_);
if (v_isSharedCheck_4610_ == 0)
{
v___x_4593_ = v_x_4576_;
v_isShared_4594_ = v_isSharedCheck_4610_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_tail_4591_);
lean_inc(v_head_4590_);
lean_dec(v_x_4576_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4610_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_box(0);
v___x_4596_ = l_Lean_Meta_Grind_processHypotheses(v_head_4590_, v___x_4595_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4599_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref_known(v___x_4596_, 1);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 1, v_x_4577_);
lean_ctor_set(v___x_4593_, 0, v_a_4597_);
v___x_4599_ = v___x_4593_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4597_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v_x_4577_);
v___x_4599_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
v_x_4576_ = v_tail_4591_;
v_x_4577_ = v___x_4599_;
goto _start;
}
}
else
{
lean_object* v_a_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4609_; 
lean_del_object(v___x_4593_);
lean_dec(v_tail_4591_);
lean_dec(v_x_4577_);
v_a_4602_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4604_ = v___x_4596_;
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_a_4602_);
lean_dec(v___x_4596_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4607_; 
if (v_isShared_4605_ == 0)
{
v___x_4607_ = v___x_4604_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4602_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__2___boxed(lean_object* v_x_4611_, lean_object* v_x_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
lean_object* v_res_4623_; 
v_res_4623_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__2(v_x_4611_, v_x_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_, v___y_4621_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec(v___y_4619_);
lean_dec_ref(v___y_4618_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec(v___y_4613_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__1(lean_object* v___x_4624_, lean_object* v___x_4625_, lean_object* v_vcs_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_){
_start:
{
lean_object* v___x_4637_; 
lean_inc(v___x_4625_);
v___x_4637_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__1(v___x_4624_, v___x_4625_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
lean_inc(v_a_4638_);
lean_dec_ref_known(v___x_4637_, 1);
v___x_4639_ = lean_array_to_list(v_vcs_4626_);
v___x_4640_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__2(v___x_4639_, v___x_4625_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v___x_4643_; uint8_t v_isShared_4644_; uint8_t v_isSharedCheck_4649_; 
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4649_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4649_ == 0)
{
v___x_4643_ = v___x_4640_;
v_isShared_4644_ = v_isSharedCheck_4649_;
goto v_resetjp_4642_;
}
else
{
lean_inc(v_a_4641_);
lean_dec(v___x_4640_);
v___x_4643_ = lean_box(0);
v_isShared_4644_ = v_isSharedCheck_4649_;
goto v_resetjp_4642_;
}
v_resetjp_4642_:
{
lean_object* v___x_4645_; lean_object* v___x_4647_; 
v___x_4645_ = l_List_appendTR___redArg(v_a_4638_, v_a_4641_);
if (v_isShared_4644_ == 0)
{
lean_ctor_set(v___x_4643_, 0, v___x_4645_);
v___x_4647_ = v___x_4643_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4645_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
}
}
}
else
{
lean_dec(v_a_4638_);
return v___x_4640_;
}
}
else
{
lean_dec_ref(v_vcs_4626_);
lean_dec(v___x_4625_);
return v___x_4637_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__1___boxed(lean_object* v___x_4650_, lean_object* v___x_4651_, lean_object* v_vcs_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v_res_4663_; 
v_res_4663_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__1(v___x_4650_, v___x_4651_, v_vcs_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
lean_dec(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
lean_dec(v___y_4655_);
lean_dec_ref(v___y_4654_);
lean_dec(v___y_4653_);
return v_res_4663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3___redArg(lean_object* v_msg_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v_ref_4670_; lean_object* v___x_4671_; lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4680_; 
v_ref_4670_ = lean_ctor_get(v___y_4667_, 5);
v___x_4671_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v_msg_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4671_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4674_ = v___x_4671_;
v_isShared_4675_ = v_isSharedCheck_4680_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4671_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4680_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4676_; lean_object* v___x_4678_; 
lean_inc(v_ref_4670_);
v___x_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4676_, 0, v_ref_4670_);
lean_ctor_set(v___x_4676_, 1, v_a_4672_);
if (v_isShared_4675_ == 0)
{
lean_ctor_set_tag(v___x_4674_, 1);
lean_ctor_set(v___x_4674_, 0, v___x_4676_);
v___x_4678_ = v___x_4674_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3___redArg___boxed(lean_object* v_msg_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_){
_start:
{
lean_object* v_res_4687_; 
v_res_4687_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3___redArg(v_msg_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
return v_res_4687_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6___redArg(lean_object* v_keys_4688_, lean_object* v_i_4689_, lean_object* v_k_4690_){
_start:
{
lean_object* v___x_4691_; uint8_t v___x_4692_; 
v___x_4691_ = lean_array_get_size(v_keys_4688_);
v___x_4692_ = lean_nat_dec_lt(v_i_4689_, v___x_4691_);
if (v___x_4692_ == 0)
{
lean_dec(v_i_4689_);
return v___x_4692_;
}
else
{
lean_object* v_k_x27_4693_; uint8_t v___x_4694_; 
v_k_x27_4693_ = lean_array_fget_borrowed(v_keys_4688_, v_i_4689_);
v___x_4694_ = l_Lean_instBEqMVarId_beq(v_k_4690_, v_k_x27_4693_);
if (v___x_4694_ == 0)
{
lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4695_ = lean_unsigned_to_nat(1u);
v___x_4696_ = lean_nat_add(v_i_4689_, v___x_4695_);
lean_dec(v_i_4689_);
v_i_4689_ = v___x_4696_;
goto _start;
}
else
{
lean_dec(v_i_4689_);
return v___x_4694_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_keys_4698_, lean_object* v_i_4699_, lean_object* v_k_4700_){
_start:
{
uint8_t v_res_4701_; lean_object* v_r_4702_; 
v_res_4701_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6___redArg(v_keys_4698_, v_i_4699_, v_k_4700_);
lean_dec(v_k_4700_);
lean_dec_ref(v_keys_4698_);
v_r_4702_ = lean_box(v_res_4701_);
return v_r_4702_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
size_t v___x_4703_; size_t v___x_4704_; size_t v___x_4705_; 
v___x_4703_ = ((size_t)5ULL);
v___x_4704_ = ((size_t)1ULL);
v___x_4705_ = lean_usize_shift_left(v___x_4704_, v___x_4703_);
return v___x_4705_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_4706_; size_t v___x_4707_; size_t v___x_4708_; 
v___x_4706_ = ((size_t)1ULL);
v___x_4707_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_4708_ = lean_usize_sub(v___x_4707_, v___x_4706_);
return v___x_4708_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4709_, size_t v_x_4710_, lean_object* v_x_4711_){
_start:
{
if (lean_obj_tag(v_x_4709_) == 0)
{
lean_object* v_es_4712_; lean_object* v___x_4713_; size_t v___x_4714_; size_t v___x_4715_; size_t v___x_4716_; lean_object* v_j_4717_; lean_object* v___x_4718_; 
v_es_4712_ = lean_ctor_get(v_x_4709_, 0);
v___x_4713_ = lean_box(2);
v___x_4714_ = ((size_t)5ULL);
v___x_4715_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_4716_ = lean_usize_land(v_x_4710_, v___x_4715_);
v_j_4717_ = lean_usize_to_nat(v___x_4716_);
v___x_4718_ = lean_array_get_borrowed(v___x_4713_, v_es_4712_, v_j_4717_);
lean_dec(v_j_4717_);
switch(lean_obj_tag(v___x_4718_))
{
case 0:
{
lean_object* v_key_4719_; uint8_t v___x_4720_; 
v_key_4719_ = lean_ctor_get(v___x_4718_, 0);
v___x_4720_ = l_Lean_instBEqMVarId_beq(v_x_4711_, v_key_4719_);
return v___x_4720_;
}
case 1:
{
lean_object* v_node_4721_; size_t v___x_4722_; 
v_node_4721_ = lean_ctor_get(v___x_4718_, 0);
v___x_4722_ = lean_usize_shift_right(v_x_4710_, v___x_4714_);
v_x_4709_ = v_node_4721_;
v_x_4710_ = v___x_4722_;
goto _start;
}
default: 
{
uint8_t v___x_4724_; 
v___x_4724_ = 0;
return v___x_4724_;
}
}
}
else
{
lean_object* v_ks_4725_; lean_object* v___x_4726_; uint8_t v___x_4727_; 
v_ks_4725_ = lean_ctor_get(v_x_4709_, 0);
v___x_4726_ = lean_unsigned_to_nat(0u);
v___x_4727_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6___redArg(v_ks_4725_, v___x_4726_, v_x_4711_);
return v___x_4727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4728_, lean_object* v_x_4729_, lean_object* v_x_4730_){
_start:
{
size_t v_x_9309__boxed_4731_; uint8_t v_res_4732_; lean_object* v_r_4733_; 
v_x_9309__boxed_4731_ = lean_unbox_usize(v_x_4729_);
lean_dec(v_x_4729_);
v_res_4732_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg(v_x_4728_, v_x_9309__boxed_4731_, v_x_4730_);
lean_dec(v_x_4730_);
lean_dec_ref(v_x_4728_);
v_r_4733_ = lean_box(v_res_4732_);
return v_r_4733_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0___redArg(lean_object* v_x_4734_, lean_object* v_x_4735_){
_start:
{
uint64_t v___x_4736_; size_t v___x_4737_; uint8_t v___x_4738_; 
v___x_4736_ = l_Lean_instHashableMVarId_hash(v_x_4735_);
v___x_4737_ = lean_uint64_to_usize(v___x_4736_);
v___x_4738_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg(v_x_4734_, v___x_4737_, v_x_4735_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0___redArg___boxed(lean_object* v_x_4739_, lean_object* v_x_4740_){
_start:
{
uint8_t v_res_4741_; lean_object* v_r_4742_; 
v_res_4741_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0___redArg(v_x_4739_, v_x_4740_);
lean_dec(v_x_4740_);
lean_dec_ref(v_x_4739_);
v_r_4742_ = lean_box(v_res_4741_);
return v_r_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0___redArg(lean_object* v_mvarId_4743_, lean_object* v___y_4744_){
_start:
{
lean_object* v___x_4746_; lean_object* v_mctx_4747_; lean_object* v_eAssignment_4748_; uint8_t v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4746_ = lean_st_ref_get(v___y_4744_);
v_mctx_4747_ = lean_ctor_get(v___x_4746_, 0);
lean_inc_ref(v_mctx_4747_);
lean_dec(v___x_4746_);
v_eAssignment_4748_ = lean_ctor_get(v_mctx_4747_, 8);
lean_inc_ref(v_eAssignment_4748_);
lean_dec_ref(v_mctx_4747_);
v___x_4749_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0___redArg(v_eAssignment_4748_, v_mvarId_4743_);
lean_dec_ref(v_eAssignment_4748_);
v___x_4750_ = lean_box(v___x_4749_);
v___x_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4750_);
return v___x_4751_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0___redArg___boxed(lean_object* v_mvarId_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
lean_object* v_res_4755_; 
v_res_4755_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0___redArg(v_mvarId_4752_, v___y_4753_);
lean_dec(v___y_4753_);
lean_dec(v_mvarId_4752_);
return v_res_4755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__4(lean_object* v_as_4756_, size_t v_i_4757_, size_t v_stop_4758_, lean_object* v_b_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v_a_4770_; uint8_t v___x_4774_; 
v___x_4774_ = lean_usize_dec_eq(v_i_4757_, v_stop_4758_);
if (v___x_4774_ == 0)
{
lean_object* v___x_4775_; lean_object* v___x_4778_; 
v___x_4775_ = lean_array_uget_borrowed(v_as_4756_, v_i_4757_);
v___x_4778_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0___redArg(v___x_4775_, v___y_4765_);
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4779_; uint8_t v___x_4780_; 
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4779_);
lean_dec_ref_known(v___x_4778_, 1);
v___x_4780_ = lean_unbox(v_a_4779_);
lean_dec(v_a_4779_);
if (v___x_4780_ == 0)
{
goto v___jp_4776_;
}
else
{
v_a_4770_ = v_b_4759_;
goto v___jp_4769_;
}
}
else
{
if (lean_obj_tag(v___x_4778_) == 0)
{
lean_object* v_a_4781_; uint8_t v___x_4782_; 
v_a_4781_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4781_);
lean_dec_ref_known(v___x_4778_, 1);
v___x_4782_ = lean_unbox(v_a_4781_);
lean_dec(v_a_4781_);
if (v___x_4782_ == 0)
{
v_a_4770_ = v_b_4759_;
goto v___jp_4769_;
}
else
{
goto v___jp_4776_;
}
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
lean_dec_ref(v_b_4759_);
v_a_4783_ = lean_ctor_get(v___x_4778_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4778_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4778_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4778_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
v___jp_4776_:
{
lean_object* v___x_4777_; 
lean_inc(v___x_4775_);
v___x_4777_ = lean_array_push(v_b_4759_, v___x_4775_);
v_a_4770_ = v___x_4777_;
goto v___jp_4769_;
}
}
else
{
lean_object* v___x_4791_; 
v___x_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4791_, 0, v_b_4759_);
return v___x_4791_;
}
v___jp_4769_:
{
size_t v___x_4771_; size_t v___x_4772_; 
v___x_4771_ = ((size_t)1ULL);
v___x_4772_ = lean_usize_add(v_i_4757_, v___x_4771_);
v_i_4757_ = v___x_4772_;
v_b_4759_ = v_a_4770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__4___boxed(lean_object* v_as_4792_, lean_object* v_i_4793_, lean_object* v_stop_4794_, lean_object* v_b_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
size_t v_i_boxed_4805_; size_t v_stop_boxed_4806_; lean_object* v_res_4807_; 
v_i_boxed_4805_ = lean_unbox_usize(v_i_4793_);
lean_dec(v_i_4793_);
v_stop_boxed_4806_ = lean_unbox_usize(v_stop_4794_);
lean_dec(v_stop_4794_);
v_res_4807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__4(v_as_4792_, v_i_boxed_4805_, v_stop_boxed_4806_, v_b_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_, v___y_4803_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec_ref(v_as_4792_);
return v_res_4807_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__1(void){
_start:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4809_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__0));
v___x_4810_ = l_Lean_stringToMessageData(v___x_4809_);
return v___x_4810_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__4(void){
_start:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__3));
v___x_4815_ = l_Lean_stringToMessageData(v___x_4814_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27(lean_object* v_stx_4816_, lean_object* v_a_4817_, lean_object* v_a_4818_, lean_object* v_a_4819_, lean_object* v_a_4820_, lean_object* v_a_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_){
_start:
{
lean_object* v___y_4827_; lean_object* v___y_4828_; lean_object* v___y_4829_; lean_object* v___y_4830_; lean_object* v___y_4831_; lean_object* v___y_4832_; lean_object* v___y_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v___y_4836_; lean_object* v_a_4837_; lean_object* v___y_4865_; lean_object* v___y_4866_; lean_object* v___y_4867_; lean_object* v___y_4868_; lean_object* v___y_4869_; lean_object* v___y_4870_; lean_object* v___y_4871_; lean_object* v___y_4872_; lean_object* v___y_4873_; lean_object* v___y_4874_; lean_object* v___y_4875_; lean_object* v___x_4885_; 
v___x_4885_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_4818_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_);
if (lean_obj_tag(v___x_4885_) == 0)
{
lean_object* v_a_4886_; lean_object* v_mvarId_4887_; lean_object* v___x_4888_; 
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
lean_inc(v_a_4886_);
lean_dec_ref_known(v___x_4885_, 1);
v_mvarId_4887_ = lean_ctor_get(v_a_4886_, 1);
lean_inc(v_mvarId_4887_);
lean_inc(v_stx_4816_);
v___x_4888_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs(v_stx_4816_, v_mvarId_4887_, v_a_4819_, v_a_4820_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v_config_4890_; lean_object* v_ctx_4891_; lean_object* v_scope_4892_; lean_object* v_invariantAlts_x3f_4893_; lean_object* v___y_4895_; lean_object* v___y_4896_; lean_object* v___y_4897_; lean_object* v___y_4898_; lean_object* v___y_4899_; lean_object* v___y_4900_; lean_object* v___y_4901_; lean_object* v___y_4902_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
lean_inc(v_a_4889_);
lean_dec_ref_known(v___x_4888_, 1);
v_config_4890_ = lean_ctor_get(v_a_4889_, 0);
lean_inc_ref(v_config_4890_);
v_ctx_4891_ = lean_ctor_get(v_a_4889_, 1);
lean_inc_ref(v_ctx_4891_);
v_scope_4892_ = lean_ctor_get(v_a_4889_, 2);
lean_inc_ref(v_scope_4892_);
v_invariantAlts_x3f_4893_ = lean_ctor_get(v_a_4889_, 4);
lean_inc(v_invariantAlts_x3f_4893_);
lean_dec(v_a_4889_);
if (lean_obj_tag(v_invariantAlts_x3f_4893_) == 0)
{
lean_object* v___x_4928_; lean_object* v___x_4929_; uint8_t v___x_4930_; 
v___x_4928_ = lean_unsigned_to_nat(3u);
v___x_4929_ = l_Lean_Syntax_getArg(v_stx_4816_, v___x_4928_);
lean_dec(v_stx_4816_);
v___x_4930_ = l_Lean_Syntax_isNone(v___x_4929_);
lean_dec(v___x_4929_);
if (v___x_4930_ == 0)
{
lean_object* v___x_4931_; lean_object* v___x_4932_; 
lean_dec_ref(v_scope_4892_);
lean_dec_ref(v_ctx_4891_);
lean_dec_ref(v_config_4890_);
lean_dec(v_a_4886_);
v___x_4931_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__4, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__4_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__4);
v___x_4932_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3___redArg(v___x_4931_, v_a_4821_, v_a_4822_, v_a_4823_, v_a_4824_);
return v___x_4932_;
}
else
{
v___y_4895_ = v_a_4817_;
v___y_4896_ = v_a_4818_;
v___y_4897_ = v_a_4819_;
v___y_4898_ = v_a_4820_;
v___y_4899_ = v_a_4821_;
v___y_4900_ = v_a_4822_;
v___y_4901_ = v_a_4823_;
v___y_4902_ = v_a_4824_;
goto v___jp_4894_;
}
}
else
{
lean_dec(v_stx_4816_);
v___y_4895_ = v_a_4817_;
v___y_4896_ = v_a_4818_;
v___y_4897_ = v_a_4819_;
v___y_4898_ = v_a_4820_;
v___y_4899_ = v_a_4821_;
v___y_4900_ = v_a_4822_;
v___y_4901_ = v_a_4823_;
v___y_4902_ = v_a_4824_;
goto v___jp_4894_;
}
v___jp_4894_:
{
lean_object* v_stepLimit_4903_; lean_object* v___f_4904_; lean_object* v___x_4905_; 
v_stepLimit_4903_ = lean_ctor_get(v_config_4890_, 0);
lean_inc(v_stepLimit_4903_);
lean_dec_ref(v_config_4890_);
v___f_4904_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__0___boxed), 15, 5);
lean_closure_set(v___f_4904_, 0, v_a_4886_);
lean_closure_set(v___f_4904_, 1, v_ctx_4891_);
lean_closure_set(v___f_4904_, 2, v_scope_4892_);
lean_closure_set(v___f_4904_, 3, v_stepLimit_4903_);
lean_closure_set(v___f_4904_, 4, v_invariantAlts_x3f_4893_);
v___x_4905_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_4904_, v___y_4895_, v___y_4896_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_);
if (lean_obj_tag(v___x_4905_) == 0)
{
lean_object* v_a_4906_; lean_object* v_invariants_4907_; lean_object* v_vcs_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; uint8_t v___x_4912_; 
v_a_4906_ = lean_ctor_get(v___x_4905_, 0);
lean_inc(v_a_4906_);
lean_dec_ref_known(v___x_4905_, 1);
v_invariants_4907_ = lean_ctor_get(v_a_4906_, 0);
v_vcs_4908_ = lean_ctor_get(v_a_4906_, 1);
lean_inc_ref(v_vcs_4908_);
v___x_4909_ = lean_unsigned_to_nat(0u);
v___x_4910_ = lean_array_get_size(v_invariants_4907_);
v___x_4911_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__2));
v___x_4912_ = lean_nat_dec_lt(v___x_4909_, v___x_4910_);
if (v___x_4912_ == 0)
{
v___y_4827_ = v_vcs_4908_;
v___y_4828_ = v___y_4902_;
v___y_4829_ = v___y_4899_;
v___y_4830_ = v___y_4895_;
v___y_4831_ = v___y_4898_;
v___y_4832_ = v___y_4901_;
v___y_4833_ = v___y_4897_;
v___y_4834_ = v___y_4896_;
v___y_4835_ = v_a_4906_;
v___y_4836_ = v___y_4900_;
v_a_4837_ = v___x_4911_;
goto v___jp_4826_;
}
else
{
uint8_t v___x_4913_; 
v___x_4913_ = lean_nat_dec_le(v___x_4910_, v___x_4910_);
if (v___x_4913_ == 0)
{
if (v___x_4912_ == 0)
{
v___y_4827_ = v_vcs_4908_;
v___y_4828_ = v___y_4902_;
v___y_4829_ = v___y_4899_;
v___y_4830_ = v___y_4895_;
v___y_4831_ = v___y_4898_;
v___y_4832_ = v___y_4901_;
v___y_4833_ = v___y_4897_;
v___y_4834_ = v___y_4896_;
v___y_4835_ = v_a_4906_;
v___y_4836_ = v___y_4900_;
v_a_4837_ = v___x_4911_;
goto v___jp_4826_;
}
else
{
size_t v___x_4914_; size_t v___x_4915_; lean_object* v___x_4916_; 
v___x_4914_ = ((size_t)0ULL);
v___x_4915_ = lean_usize_of_nat(v___x_4910_);
v___x_4916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__4(v_invariants_4907_, v___x_4914_, v___x_4915_, v___x_4911_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_);
v___y_4865_ = v_vcs_4908_;
v___y_4866_ = v___y_4902_;
v___y_4867_ = v___y_4899_;
v___y_4868_ = v___y_4895_;
v___y_4869_ = v___y_4898_;
v___y_4870_ = v___y_4901_;
v___y_4871_ = v___y_4897_;
v___y_4872_ = v___y_4896_;
v___y_4873_ = v_a_4906_;
v___y_4874_ = v___y_4900_;
v___y_4875_ = v___x_4916_;
goto v___jp_4864_;
}
}
else
{
size_t v___x_4917_; size_t v___x_4918_; lean_object* v___x_4919_; 
v___x_4917_ = ((size_t)0ULL);
v___x_4918_ = lean_usize_of_nat(v___x_4910_);
v___x_4919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__4(v_invariants_4907_, v___x_4917_, v___x_4918_, v___x_4911_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_, v___y_4902_);
v___y_4865_ = v_vcs_4908_;
v___y_4866_ = v___y_4902_;
v___y_4867_ = v___y_4899_;
v___y_4868_ = v___y_4895_;
v___y_4869_ = v___y_4898_;
v___y_4870_ = v___y_4901_;
v___y_4871_ = v___y_4897_;
v___y_4872_ = v___y_4896_;
v___y_4873_ = v_a_4906_;
v___y_4874_ = v___y_4900_;
v___y_4875_ = v___x_4919_;
goto v___jp_4864_;
}
}
}
else
{
lean_object* v_a_4920_; lean_object* v___x_4922_; uint8_t v_isShared_4923_; uint8_t v_isSharedCheck_4927_; 
v_a_4920_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4922_ = v___x_4905_;
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
else
{
lean_inc(v_a_4920_);
lean_dec(v___x_4905_);
v___x_4922_ = lean_box(0);
v_isShared_4923_ = v_isSharedCheck_4927_;
goto v_resetjp_4921_;
}
v_resetjp_4921_:
{
lean_object* v___x_4925_; 
if (v_isShared_4923_ == 0)
{
v___x_4925_ = v___x_4922_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4920_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
}
else
{
lean_object* v_a_4933_; lean_object* v___x_4935_; uint8_t v_isShared_4936_; uint8_t v_isSharedCheck_4940_; 
lean_dec(v_a_4886_);
lean_dec(v_stx_4816_);
v_a_4933_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4940_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4940_ == 0)
{
v___x_4935_ = v___x_4888_;
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
else
{
lean_inc(v_a_4933_);
lean_dec(v___x_4888_);
v___x_4935_ = lean_box(0);
v_isShared_4936_ = v_isSharedCheck_4940_;
goto v_resetjp_4934_;
}
v_resetjp_4934_:
{
lean_object* v___x_4938_; 
if (v_isShared_4936_ == 0)
{
v___x_4938_ = v___x_4935_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v_a_4933_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
}
}
else
{
lean_object* v_a_4941_; lean_object* v___x_4943_; uint8_t v_isShared_4944_; uint8_t v_isSharedCheck_4948_; 
lean_dec(v_stx_4816_);
v_a_4941_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4948_ == 0)
{
v___x_4943_ = v___x_4885_;
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
else
{
lean_inc(v_a_4941_);
lean_dec(v___x_4885_);
v___x_4943_ = lean_box(0);
v_isShared_4944_ = v_isSharedCheck_4948_;
goto v_resetjp_4942_;
}
v_resetjp_4942_:
{
lean_object* v___x_4946_; 
if (v_isShared_4944_ == 0)
{
v___x_4946_ = v___x_4943_;
goto v_reusejp_4945_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v_a_4941_);
v___x_4946_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4945_;
}
v_reusejp_4945_:
{
return v___x_4946_;
}
}
}
v___jp_4826_:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___f_4840_; lean_object* v___x_4841_; 
v___x_4838_ = lean_array_to_list(v_a_4837_);
v___x_4839_ = lean_box(0);
v___f_4840_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4840_, 0, v___x_4838_);
lean_closure_set(v___f_4840_, 1, v___x_4839_);
lean_closure_set(v___f_4840_, 2, v___y_4827_);
v___x_4841_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_4840_, v___y_4830_, v___y_4834_, v___y_4829_, v___y_4836_, v___y_4832_, v___y_4828_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v_a_4842_; lean_object* v___x_4843_; 
v_a_4842_ = lean_ctor_get(v___x_4841_, 0);
lean_inc(v_a_4842_);
lean_dec_ref_known(v___x_4841_, 1);
v___x_4843_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v_a_4842_, v___y_4834_, v___y_4829_, v___y_4836_, v___y_4832_, v___y_4828_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v___x_4845_; uint8_t v_isShared_4846_; uint8_t v_isSharedCheck_4854_; 
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4854_ == 0)
{
lean_object* v_unused_4855_; 
v_unused_4855_ = lean_ctor_get(v___x_4843_, 0);
lean_dec(v_unused_4855_);
v___x_4845_ = v___x_4843_;
v_isShared_4846_ = v_isSharedCheck_4854_;
goto v_resetjp_4844_;
}
else
{
lean_dec(v___x_4843_);
v___x_4845_ = lean_box(0);
v_isShared_4846_ = v_isSharedCheck_4854_;
goto v_resetjp_4844_;
}
v_resetjp_4844_:
{
uint8_t v_preTacFailed_4847_; 
v_preTacFailed_4847_ = lean_ctor_get_uint8(v___y_4835_, sizeof(void*)*3);
lean_dec_ref(v___y_4835_);
if (v_preTacFailed_4847_ == 0)
{
lean_object* v___x_4848_; lean_object* v___x_4850_; 
v___x_4848_ = lean_box(0);
if (v_isShared_4846_ == 0)
{
lean_ctor_set(v___x_4845_, 0, v___x_4848_);
v___x_4850_ = v___x_4845_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v___x_4848_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
else
{
lean_object* v___x_4852_; lean_object* v___x_4853_; 
lean_del_object(v___x_4845_);
v___x_4852_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__1);
v___x_4853_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3___redArg(v___x_4852_, v___y_4829_, v___y_4836_, v___y_4832_, v___y_4828_);
return v___x_4853_;
}
}
}
else
{
lean_dec_ref(v___y_4835_);
return v___x_4843_;
}
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
lean_dec_ref(v___y_4835_);
v_a_4856_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4841_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4841_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
v___jp_4864_:
{
if (lean_obj_tag(v___y_4875_) == 0)
{
lean_object* v_a_4876_; 
v_a_4876_ = lean_ctor_get(v___y_4875_, 0);
lean_inc(v_a_4876_);
lean_dec_ref_known(v___y_4875_, 1);
v___y_4827_ = v___y_4865_;
v___y_4828_ = v___y_4866_;
v___y_4829_ = v___y_4867_;
v___y_4830_ = v___y_4868_;
v___y_4831_ = v___y_4869_;
v___y_4832_ = v___y_4870_;
v___y_4833_ = v___y_4871_;
v___y_4834_ = v___y_4872_;
v___y_4835_ = v___y_4873_;
v___y_4836_ = v___y_4874_;
v_a_4837_ = v_a_4876_;
goto v___jp_4826_;
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_dec_ref(v___y_4873_);
lean_dec_ref(v___y_4865_);
v_a_4877_ = lean_ctor_get(v___y_4875_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___y_4875_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___y_4875_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___y_4875_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___boxed(lean_object* v_stx_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_, lean_object* v_a_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27(v_stx_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_, v_a_4954_, v_a_4955_, v_a_4956_, v_a_4957_);
lean_dec(v_a_4957_);
lean_dec_ref(v_a_4956_);
lean_dec(v_a_4955_);
lean_dec_ref(v_a_4954_);
lean_dec(v_a_4953_);
lean_dec_ref(v_a_4952_);
lean_dec(v_a_4951_);
lean_dec_ref(v_a_4950_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0(lean_object* v_mvarId_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v___x_4970_; 
v___x_4970_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0___redArg(v_mvarId_4960_, v___y_4966_);
return v___x_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0___boxed(lean_object* v_mvarId_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_){
_start:
{
lean_object* v_res_4981_; 
v_res_4981_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0(v_mvarId_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec(v_mvarId_4971_);
return v_res_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3(lean_object* v_00_u03b1_4982_, lean_object* v_msg_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v___x_4993_; 
v___x_4993_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3___redArg(v_msg_4983_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_);
return v___x_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3___boxed(lean_object* v_00_u03b1_4994_, lean_object* v_msg_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v_res_5005_; 
v_res_5005_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__3(v_00_u03b1_4994_, v_msg_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_, v___y_5003_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
lean_dec(v___y_5001_);
lean_dec_ref(v___y_5000_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
return v_res_5005_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0(lean_object* v_00_u03b2_5006_, lean_object* v_x_5007_, lean_object* v_x_5008_){
_start:
{
uint8_t v___x_5009_; 
v___x_5009_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0___redArg(v_x_5007_, v_x_5008_);
return v___x_5009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5010_, lean_object* v_x_5011_, lean_object* v_x_5012_){
_start:
{
uint8_t v_res_5013_; lean_object* v_r_5014_; 
v_res_5013_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0(v_00_u03b2_5010_, v_x_5011_, v_x_5012_);
lean_dec(v_x_5012_);
lean_dec_ref(v_x_5011_);
v_r_5014_ = lean_box(v_res_5013_);
return v_r_5014_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5015_, lean_object* v_x_5016_, size_t v_x_5017_, lean_object* v_x_5018_){
_start:
{
uint8_t v___x_5019_; 
v___x_5019_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___redArg(v_x_5016_, v_x_5017_, v_x_5018_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5020_, lean_object* v_x_5021_, lean_object* v_x_5022_, lean_object* v_x_5023_){
_start:
{
size_t v_x_9782__boxed_5024_; uint8_t v_res_5025_; lean_object* v_r_5026_; 
v_x_9782__boxed_5024_ = lean_unbox_usize(v_x_5022_);
lean_dec(v_x_5022_);
v_res_5025_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1(v_00_u03b2_5020_, v_x_5021_, v_x_9782__boxed_5024_, v_x_5023_);
lean_dec(v_x_5023_);
lean_dec_ref(v_x_5021_);
v_r_5026_ = lean_box(v_res_5025_);
return v_r_5026_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_5027_, lean_object* v_keys_5028_, lean_object* v_vals_5029_, lean_object* v_heq_5030_, lean_object* v_i_5031_, lean_object* v_k_5032_){
_start:
{
uint8_t v___x_5033_; 
v___x_5033_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6___redArg(v_keys_5028_, v_i_5031_, v_k_5032_);
return v___x_5033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b2_5034_, lean_object* v_keys_5035_, lean_object* v_vals_5036_, lean_object* v_heq_5037_, lean_object* v_i_5038_, lean_object* v_k_5039_){
_start:
{
uint8_t v_res_5040_; lean_object* v_r_5041_; 
v_res_5040_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0_spec__1_spec__6(v_00_u03b2_5034_, v_keys_5035_, v_vals_5036_, v_heq_5037_, v_i_5038_, v_k_5039_);
lean_dec(v_k_5039_);
lean_dec_ref(v_vals_5036_);
lean_dec_ref(v_keys_5035_);
v_r_5041_ = lean_box(v_res_5040_);
return v_r_5041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1(){
_start:
{
lean_object* v___x_5100_; lean_object* v___x_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; 
v___x_5100_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_5101_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__1));
v___x_5102_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__21));
v___x_5103_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___boxed), 10, 0);
v___x_5104_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5100_, v___x_5101_, v___x_5102_, v___x_5103_);
return v___x_5104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___boxed(lean_object* v_a_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1();
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_docString__3(){
_start:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5109_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1___closed__21));
v___x_5110_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_docString__3___closed__0));
v___x_5111_ = l_Lean_addBuiltinDocString(v___x_5109_, v___x_5110_);
return v___x_5111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_docString__3___boxed(lean_object* v_a_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_docString__3();
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__0(lean_object* v_a_5114_, lean_object* v_config_5115_, lean_object* v_ctx_5116_, lean_object* v_scope_5117_, lean_object* v_invariantAlts_x3f_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_){
_start:
{
lean_object* v___x_5129_; 
v___x_5129_ = l_Lean_Meta_Grind_mkGoalCore(v_a_5114_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v_a_5130_; lean_object* v_stepLimit_5131_; lean_object* v___x_5132_; 
v_a_5130_ = lean_ctor_get(v___x_5129_, 0);
lean_inc(v_a_5130_);
lean_dec_ref_known(v___x_5129_, 1);
v_stepLimit_5131_ = lean_ctor_get(v_config_5115_, 0);
lean_inc(v_stepLimit_5131_);
lean_dec_ref(v_config_5115_);
v___x_5132_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run(v_a_5130_, v_ctx_5116_, v_scope_5117_, v_stepLimit_5131_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_);
if (lean_obj_tag(v___x_5132_) == 0)
{
if (lean_obj_tag(v_invariantAlts_x3f_5118_) == 1)
{
lean_object* v_a_5133_; lean_object* v_val_5134_; lean_object* v_invariants_5135_; lean_object* v_inlineHandledInvariants_5136_; lean_object* v___x_5137_; 
v_a_5133_ = lean_ctor_get(v___x_5132_, 0);
lean_inc(v_a_5133_);
lean_dec_ref_known(v___x_5132_, 1);
v_val_5134_ = lean_ctor_get(v_invariantAlts_x3f_5118_, 0);
v_invariants_5135_ = lean_ctor_get(v_a_5133_, 0);
v_inlineHandledInvariants_5136_ = lean_ctor_get(v_a_5133_, 2);
lean_inc_ref(v_inlineHandledInvariants_5136_);
v___x_5137_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants(v_val_5134_, v_invariants_5135_, v_inlineHandledInvariants_5136_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_, v___y_5127_);
if (lean_obj_tag(v___x_5137_) == 0)
{
lean_object* v___x_5139_; uint8_t v_isShared_5140_; uint8_t v_isSharedCheck_5144_; 
v_isSharedCheck_5144_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5144_ == 0)
{
lean_object* v_unused_5145_; 
v_unused_5145_ = lean_ctor_get(v___x_5137_, 0);
lean_dec(v_unused_5145_);
v___x_5139_ = v___x_5137_;
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
else
{
lean_dec(v___x_5137_);
v___x_5139_ = lean_box(0);
v_isShared_5140_ = v_isSharedCheck_5144_;
goto v_resetjp_5138_;
}
v_resetjp_5138_:
{
lean_object* v___x_5142_; 
if (v_isShared_5140_ == 0)
{
lean_ctor_set(v___x_5139_, 0, v_a_5133_);
v___x_5142_ = v___x_5139_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5143_; 
v_reuseFailAlloc_5143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5143_, 0, v_a_5133_);
v___x_5142_ = v_reuseFailAlloc_5143_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
return v___x_5142_;
}
}
}
else
{
lean_object* v_a_5146_; lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5153_; 
lean_dec(v_a_5133_);
v_a_5146_ = lean_ctor_get(v___x_5137_, 0);
v_isSharedCheck_5153_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5153_ == 0)
{
v___x_5148_ = v___x_5137_;
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
else
{
lean_inc(v_a_5146_);
lean_dec(v___x_5137_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5153_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5151_; 
if (v_isShared_5149_ == 0)
{
v___x_5151_ = v___x_5148_;
goto v_reusejp_5150_;
}
else
{
lean_object* v_reuseFailAlloc_5152_; 
v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_a_5146_);
v___x_5151_ = v_reuseFailAlloc_5152_;
goto v_reusejp_5150_;
}
v_reusejp_5150_:
{
return v___x_5151_;
}
}
}
}
else
{
return v___x_5132_;
}
}
else
{
return v___x_5132_;
}
}
else
{
lean_object* v_a_5154_; lean_object* v___x_5156_; uint8_t v_isShared_5157_; uint8_t v_isSharedCheck_5161_; 
lean_dec_ref(v_scope_5117_);
lean_dec_ref(v_config_5115_);
v_a_5154_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5161_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5161_ == 0)
{
v___x_5156_ = v___x_5129_;
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
else
{
lean_inc(v_a_5154_);
lean_dec(v___x_5129_);
v___x_5156_ = lean_box(0);
v_isShared_5157_ = v_isSharedCheck_5161_;
goto v_resetjp_5155_;
}
v_resetjp_5155_:
{
lean_object* v___x_5159_; 
if (v_isShared_5157_ == 0)
{
v___x_5159_ = v___x_5156_;
goto v_reusejp_5158_;
}
else
{
lean_object* v_reuseFailAlloc_5160_; 
v_reuseFailAlloc_5160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_a_5154_);
v___x_5159_ = v_reuseFailAlloc_5160_;
goto v_reusejp_5158_;
}
v_reusejp_5158_:
{
return v___x_5159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__0___boxed(lean_object* v_a_5162_, lean_object* v_config_5163_, lean_object* v_ctx_5164_, lean_object* v_scope_5165_, lean_object* v_invariantAlts_x3f_5166_, lean_object* v___y_5167_, lean_object* v___y_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_){
_start:
{
lean_object* v_res_5177_; 
v_res_5177_ = l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__0(v_a_5162_, v_config_5163_, v_ctx_5164_, v_scope_5165_, v_invariantAlts_x3f_5166_, v___y_5167_, v___y_5168_, v___y_5169_, v___y_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_, v___y_5175_);
lean_dec(v___y_5175_);
lean_dec_ref(v___y_5174_);
lean_dec(v___y_5173_);
lean_dec_ref(v___y_5172_);
lean_dec(v___y_5171_);
lean_dec_ref(v___y_5170_);
lean_dec(v___y_5169_);
lean_dec_ref(v___y_5168_);
lean_dec(v___y_5167_);
lean_dec(v_invariantAlts_x3f_5166_);
lean_dec_ref(v_ctx_5164_);
return v_res_5177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__4(size_t v_sz_5178_, size_t v_i_5179_, lean_object* v_bs_5180_){
_start:
{
uint8_t v___x_5181_; 
v___x_5181_ = lean_usize_dec_lt(v_i_5179_, v_sz_5178_);
if (v___x_5181_ == 0)
{
return v_bs_5180_;
}
else
{
lean_object* v_v_5182_; lean_object* v_mvarId_5183_; lean_object* v___x_5184_; lean_object* v_bs_x27_5185_; size_t v___x_5186_; size_t v___x_5187_; lean_object* v___x_5188_; 
v_v_5182_ = lean_array_uget_borrowed(v_bs_5180_, v_i_5179_);
v_mvarId_5183_ = lean_ctor_get(v_v_5182_, 1);
lean_inc(v_mvarId_5183_);
v___x_5184_ = lean_unsigned_to_nat(0u);
v_bs_x27_5185_ = lean_array_uset(v_bs_5180_, v_i_5179_, v___x_5184_);
v___x_5186_ = ((size_t)1ULL);
v___x_5187_ = lean_usize_add(v_i_5179_, v___x_5186_);
v___x_5188_ = lean_array_uset(v_bs_x27_5185_, v_i_5179_, v_mvarId_5183_);
v_i_5179_ = v___x_5187_;
v_bs_5180_ = v___x_5188_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__4___boxed(lean_object* v_sz_5190_, lean_object* v_i_5191_, lean_object* v_bs_5192_){
_start:
{
size_t v_sz_boxed_5193_; size_t v_i_boxed_5194_; lean_object* v_res_5195_; 
v_sz_boxed_5193_ = lean_unbox_usize(v_sz_5190_);
lean_dec(v_sz_5190_);
v_i_boxed_5194_ = lean_unbox_usize(v_i_5191_);
lean_dec(v_i_5191_);
v_res_5195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__4(v_sz_boxed_5193_, v_i_boxed_5194_, v_bs_5192_);
return v_res_5195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2___redArg(lean_object* v_msg_5196_, lean_object* v___y_5197_, lean_object* v___y_5198_, lean_object* v___y_5199_, lean_object* v___y_5200_){
_start:
{
lean_object* v_ref_5202_; lean_object* v___x_5203_; lean_object* v_a_5204_; lean_object* v___x_5206_; uint8_t v_isShared_5207_; uint8_t v_isSharedCheck_5212_; 
v_ref_5202_ = lean_ctor_get(v___y_5199_, 5);
v___x_5203_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v_msg_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_);
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5203_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5206_ = v___x_5203_;
v_isShared_5207_ = v_isSharedCheck_5212_;
goto v_resetjp_5205_;
}
else
{
lean_inc(v_a_5204_);
lean_dec(v___x_5203_);
v___x_5206_ = lean_box(0);
v_isShared_5207_ = v_isSharedCheck_5212_;
goto v_resetjp_5205_;
}
v_resetjp_5205_:
{
lean_object* v___x_5208_; lean_object* v___x_5210_; 
lean_inc(v_ref_5202_);
v___x_5208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5208_, 0, v_ref_5202_);
lean_ctor_set(v___x_5208_, 1, v_a_5204_);
if (v_isShared_5207_ == 0)
{
lean_ctor_set_tag(v___x_5206_, 1);
lean_ctor_set(v___x_5206_, 0, v___x_5208_);
v___x_5210_ = v___x_5206_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v___x_5208_);
v___x_5210_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
return v___x_5210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2___redArg___boxed(lean_object* v_msg_5213_, lean_object* v___y_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2___redArg(v_msg_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
lean_dec(v___y_5217_);
lean_dec_ref(v___y_5216_);
lean_dec(v___y_5215_);
lean_dec_ref(v___y_5214_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__1(lean_object* v_a_5220_, lean_object* v_a_5221_){
_start:
{
if (lean_obj_tag(v_a_5220_) == 0)
{
lean_object* v___x_5222_; 
v___x_5222_ = l_List_reverse___redArg(v_a_5221_);
return v___x_5222_;
}
else
{
lean_object* v_head_5223_; lean_object* v_tail_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5233_; 
v_head_5223_ = lean_ctor_get(v_a_5220_, 0);
v_tail_5224_ = lean_ctor_get(v_a_5220_, 1);
v_isSharedCheck_5233_ = !lean_is_exclusive(v_a_5220_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5226_ = v_a_5220_;
v_isShared_5227_ = v_isSharedCheck_5233_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_tail_5224_);
lean_inc(v_head_5223_);
lean_dec(v_a_5220_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5233_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v_mvarId_5228_; lean_object* v___x_5230_; 
v_mvarId_5228_ = lean_ctor_get(v_head_5223_, 1);
lean_inc(v_mvarId_5228_);
lean_dec(v_head_5223_);
if (v_isShared_5227_ == 0)
{
lean_ctor_set(v___x_5226_, 1, v_a_5221_);
lean_ctor_set(v___x_5226_, 0, v_mvarId_5228_);
v___x_5230_ = v___x_5226_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_mvarId_5228_);
lean_ctor_set(v_reuseFailAlloc_5232_, 1, v_a_5221_);
v___x_5230_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
v_a_5220_ = v_tail_5224_;
v_a_5221_ = v___x_5230_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0___redArg(lean_object* v_mvarId_5234_, lean_object* v___y_5235_){
_start:
{
lean_object* v___x_5237_; lean_object* v_mctx_5238_; lean_object* v_eAssignment_5239_; uint8_t v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; 
v___x_5237_ = lean_st_ref_get(v___y_5235_);
v_mctx_5238_ = lean_ctor_get(v___x_5237_, 0);
lean_inc_ref(v_mctx_5238_);
lean_dec(v___x_5237_);
v_eAssignment_5239_ = lean_ctor_get(v_mctx_5238_, 8);
lean_inc_ref(v_eAssignment_5239_);
lean_dec_ref(v_mctx_5238_);
v___x_5240_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_spec__0_spec__0___redArg(v_eAssignment_5239_, v_mvarId_5234_);
lean_dec_ref(v_eAssignment_5239_);
v___x_5241_ = lean_box(v___x_5240_);
v___x_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5242_, 0, v___x_5241_);
return v___x_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0___redArg___boxed(lean_object* v_mvarId_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_){
_start:
{
lean_object* v_res_5246_; 
v_res_5246_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0___redArg(v_mvarId_5243_, v___y_5244_);
lean_dec(v___y_5244_);
lean_dec(v_mvarId_5243_);
return v_res_5246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__3(lean_object* v_as_5247_, size_t v_i_5248_, size_t v_stop_5249_, lean_object* v_b_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_, lean_object* v___y_5258_){
_start:
{
lean_object* v_a_5261_; uint8_t v___x_5265_; 
v___x_5265_ = lean_usize_dec_eq(v_i_5248_, v_stop_5249_);
if (v___x_5265_ == 0)
{
lean_object* v___x_5266_; lean_object* v___x_5269_; 
v___x_5266_ = lean_array_uget_borrowed(v_as_5247_, v_i_5248_);
v___x_5269_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0___redArg(v___x_5266_, v___y_5256_);
if (lean_obj_tag(v___x_5269_) == 0)
{
lean_object* v_a_5270_; uint8_t v___x_5271_; 
v_a_5270_ = lean_ctor_get(v___x_5269_, 0);
lean_inc(v_a_5270_);
lean_dec_ref_known(v___x_5269_, 1);
v___x_5271_ = lean_unbox(v_a_5270_);
lean_dec(v_a_5270_);
if (v___x_5271_ == 0)
{
goto v___jp_5267_;
}
else
{
v_a_5261_ = v_b_5250_;
goto v___jp_5260_;
}
}
else
{
if (lean_obj_tag(v___x_5269_) == 0)
{
lean_object* v_a_5272_; uint8_t v___x_5273_; 
v_a_5272_ = lean_ctor_get(v___x_5269_, 0);
lean_inc(v_a_5272_);
lean_dec_ref_known(v___x_5269_, 1);
v___x_5273_ = lean_unbox(v_a_5272_);
lean_dec(v_a_5272_);
if (v___x_5273_ == 0)
{
v_a_5261_ = v_b_5250_;
goto v___jp_5260_;
}
else
{
goto v___jp_5267_;
}
}
else
{
lean_object* v_a_5274_; lean_object* v___x_5276_; uint8_t v_isShared_5277_; uint8_t v_isSharedCheck_5281_; 
lean_dec_ref(v_b_5250_);
v_a_5274_ = lean_ctor_get(v___x_5269_, 0);
v_isSharedCheck_5281_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5276_ = v___x_5269_;
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
else
{
lean_inc(v_a_5274_);
lean_dec(v___x_5269_);
v___x_5276_ = lean_box(0);
v_isShared_5277_ = v_isSharedCheck_5281_;
goto v_resetjp_5275_;
}
v_resetjp_5275_:
{
lean_object* v___x_5279_; 
if (v_isShared_5277_ == 0)
{
v___x_5279_ = v___x_5276_;
goto v_reusejp_5278_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5274_);
v___x_5279_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5278_;
}
v_reusejp_5278_:
{
return v___x_5279_;
}
}
}
}
v___jp_5267_:
{
lean_object* v___x_5268_; 
lean_inc(v___x_5266_);
v___x_5268_ = lean_array_push(v_b_5250_, v___x_5266_);
v_a_5261_ = v___x_5268_;
goto v___jp_5260_;
}
}
else
{
lean_object* v___x_5282_; 
v___x_5282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5282_, 0, v_b_5250_);
return v___x_5282_;
}
v___jp_5260_:
{
size_t v___x_5262_; size_t v___x_5263_; 
v___x_5262_ = ((size_t)1ULL);
v___x_5263_ = lean_usize_add(v_i_5248_, v___x_5262_);
v_i_5248_ = v___x_5263_;
v_b_5250_ = v_a_5261_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__3___boxed(lean_object* v_as_5283_, lean_object* v_i_5284_, lean_object* v_stop_5285_, lean_object* v_b_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
size_t v_i_boxed_5296_; size_t v_stop_boxed_5297_; lean_object* v_res_5298_; 
v_i_boxed_5296_ = lean_unbox_usize(v_i_5284_);
lean_dec(v_i_5284_);
v_stop_boxed_5297_ = lean_unbox_usize(v_stop_5285_);
lean_dec(v_stop_5285_);
v_res_5298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__3(v_as_5283_, v_i_boxed_5296_, v_stop_boxed_5297_, v_b_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
lean_dec(v___y_5294_);
lean_dec_ref(v___y_5293_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
lean_dec_ref(v_as_5283_);
return v_res_5298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__1(lean_object* v_stx_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_, lean_object* v___y_5307_){
_start:
{
lean_object* v___x_5309_; 
v___x_5309_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5301_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
if (lean_obj_tag(v___x_5309_) == 0)
{
lean_object* v_a_5310_; lean_object* v___x_5311_; 
v_a_5310_ = lean_ctor_get(v___x_5309_, 0);
lean_inc_n(v_a_5310_, 2);
lean_dec_ref_known(v___x_5309_, 1);
lean_inc(v_stx_5299_);
v___x_5311_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs(v_stx_5299_, v_a_5310_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
if (lean_obj_tag(v___x_5311_) == 0)
{
lean_object* v_a_5312_; lean_object* v_config_5313_; lean_object* v_ctx_5314_; lean_object* v_scope_5315_; lean_object* v_params_5316_; lean_object* v_invariantAlts_x3f_5317_; lean_object* v___f_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; 
v_a_5312_ = lean_ctor_get(v___x_5311_, 0);
lean_inc(v_a_5312_);
lean_dec_ref_known(v___x_5311_, 1);
v_config_5313_ = lean_ctor_get(v_a_5312_, 0);
lean_inc_ref(v_config_5313_);
v_ctx_5314_ = lean_ctor_get(v_a_5312_, 1);
lean_inc_ref(v_ctx_5314_);
v_scope_5315_ = lean_ctor_get(v_a_5312_, 2);
lean_inc_ref(v_scope_5315_);
v_params_5316_ = lean_ctor_get(v_a_5312_, 3);
lean_inc_ref(v_params_5316_);
v_invariantAlts_x3f_5317_ = lean_ctor_get(v_a_5312_, 4);
lean_inc_n(v_invariantAlts_x3f_5317_, 2);
lean_dec(v_a_5312_);
v___f_5318_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__0___boxed), 15, 5);
lean_closure_set(v___f_5318_, 0, v_a_5310_);
lean_closure_set(v___f_5318_, 1, v_config_5313_);
lean_closure_set(v___f_5318_, 2, v_ctx_5314_);
lean_closure_set(v___f_5318_, 3, v_scope_5315_);
lean_closure_set(v___f_5318_, 4, v_invariantAlts_x3f_5317_);
v___x_5319_ = lean_box(0);
v___x_5320_ = l_Lean_Meta_Grind_GrindM_run___redArg(v___f_5318_, v_params_5316_, v___x_5319_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
if (lean_obj_tag(v___x_5320_) == 0)
{
lean_object* v_a_5321_; lean_object* v___y_5323_; lean_object* v___y_5324_; lean_object* v___y_5325_; lean_object* v___y_5326_; lean_object* v___y_5327_; lean_object* v___y_5328_; lean_object* v___y_5329_; lean_object* v___y_5330_; lean_object* v_a_5331_; lean_object* v___y_5352_; lean_object* v___y_5353_; lean_object* v___y_5354_; lean_object* v___y_5355_; lean_object* v___y_5356_; lean_object* v___y_5357_; lean_object* v___y_5358_; lean_object* v___y_5359_; lean_object* v___y_5360_; lean_object* v___y_5371_; lean_object* v___y_5372_; lean_object* v___y_5373_; lean_object* v___y_5374_; lean_object* v___y_5375_; lean_object* v___y_5376_; lean_object* v___y_5377_; lean_object* v___y_5378_; 
v_a_5321_ = lean_ctor_get(v___x_5320_, 0);
lean_inc(v_a_5321_);
lean_dec_ref_known(v___x_5320_, 1);
if (lean_obj_tag(v_invariantAlts_x3f_5317_) == 0)
{
lean_object* v_invariants_5391_; lean_object* v_vcs_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; size_t v_sz_5395_; size_t v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; 
v_invariants_5391_ = lean_ctor_get(v_a_5321_, 0);
v_vcs_5392_ = lean_ctor_get(v_a_5321_, 1);
v___x_5393_ = lean_unsigned_to_nat(3u);
v___x_5394_ = l_Lean_Syntax_getArg(v_stx_5299_, v___x_5393_);
lean_dec(v_stx_5299_);
v_sz_5395_ = lean_array_size(v_vcs_5392_);
v___x_5396_ = ((size_t)0ULL);
lean_inc_ref(v_vcs_5392_);
v___x_5397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__4(v_sz_5395_, v___x_5396_, v_vcs_5392_);
v___x_5398_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___boxed), 11, 1);
lean_closure_set(v___x_5398_, 0, v___x_5397_);
v___x_5399_ = l_Lean_Elab_Tactic_Do_elabInvariants(v___x_5394_, v_invariants_5391_, v___x_5398_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_, v___y_5306_, v___y_5307_);
lean_dec(v___x_5394_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_dec_ref_known(v___x_5399_, 1);
v___y_5371_ = v___y_5300_;
v___y_5372_ = v___y_5301_;
v___y_5373_ = v___y_5302_;
v___y_5374_ = v___y_5303_;
v___y_5375_ = v___y_5304_;
v___y_5376_ = v___y_5305_;
v___y_5377_ = v___y_5306_;
v___y_5378_ = v___y_5307_;
goto v___jp_5370_;
}
else
{
lean_dec(v_a_5321_);
return v___x_5399_;
}
}
else
{
lean_dec_ref_known(v_invariantAlts_x3f_5317_, 1);
lean_dec(v_stx_5299_);
v___y_5371_ = v___y_5300_;
v___y_5372_ = v___y_5301_;
v___y_5373_ = v___y_5302_;
v___y_5374_ = v___y_5303_;
v___y_5375_ = v___y_5304_;
v___y_5376_ = v___y_5305_;
v___y_5377_ = v___y_5306_;
v___y_5378_ = v___y_5307_;
goto v___jp_5370_;
}
v___jp_5322_:
{
lean_object* v_vcs_5332_; uint8_t v_preTacFailed_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; 
v_vcs_5332_ = lean_ctor_get(v_a_5321_, 1);
lean_inc_ref(v_vcs_5332_);
v_preTacFailed_5333_ = lean_ctor_get_uint8(v_a_5321_, sizeof(void*)*3);
lean_dec(v_a_5321_);
v___x_5334_ = lean_array_to_list(v_a_5331_);
v___x_5335_ = lean_array_to_list(v_vcs_5332_);
v___x_5336_ = lean_box(0);
v___x_5337_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__1(v___x_5335_, v___x_5336_);
v___x_5338_ = l_List_appendTR___redArg(v___x_5334_, v___x_5337_);
v___x_5339_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5338_, v___y_5330_, v___y_5328_, v___y_5326_, v___y_5325_, v___y_5324_);
if (lean_obj_tag(v___x_5339_) == 0)
{
lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5349_; 
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5339_);
if (v_isSharedCheck_5349_ == 0)
{
lean_object* v_unused_5350_; 
v_unused_5350_ = lean_ctor_get(v___x_5339_, 0);
lean_dec(v_unused_5350_);
v___x_5341_ = v___x_5339_;
v_isShared_5342_ = v_isSharedCheck_5349_;
goto v_resetjp_5340_;
}
else
{
lean_dec(v___x_5339_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5349_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
if (v_preTacFailed_5333_ == 0)
{
lean_object* v___x_5343_; lean_object* v___x_5345_; 
v___x_5343_ = lean_box(0);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 0, v___x_5343_);
v___x_5345_ = v___x_5341_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5343_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
else
{
lean_object* v___x_5347_; lean_object* v___x_5348_; 
lean_del_object(v___x_5341_);
v___x_5347_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__1);
v___x_5348_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2___redArg(v___x_5347_, v___y_5328_, v___y_5326_, v___y_5325_, v___y_5324_);
return v___x_5348_;
}
}
}
else
{
return v___x_5339_;
}
}
v___jp_5351_:
{
if (lean_obj_tag(v___y_5360_) == 0)
{
lean_object* v_a_5361_; 
v_a_5361_ = lean_ctor_get(v___y_5360_, 0);
lean_inc(v_a_5361_);
lean_dec_ref_known(v___y_5360_, 1);
v___y_5323_ = v___y_5353_;
v___y_5324_ = v___y_5352_;
v___y_5325_ = v___y_5354_;
v___y_5326_ = v___y_5355_;
v___y_5327_ = v___y_5356_;
v___y_5328_ = v___y_5357_;
v___y_5329_ = v___y_5358_;
v___y_5330_ = v___y_5359_;
v_a_5331_ = v_a_5361_;
goto v___jp_5322_;
}
else
{
lean_object* v_a_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5369_; 
lean_dec(v_a_5321_);
v_a_5362_ = lean_ctor_get(v___y_5360_, 0);
v_isSharedCheck_5369_ = !lean_is_exclusive(v___y_5360_);
if (v_isSharedCheck_5369_ == 0)
{
v___x_5364_ = v___y_5360_;
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_a_5362_);
lean_dec(v___y_5360_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5369_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5368_; 
v_reuseFailAlloc_5368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5368_, 0, v_a_5362_);
v___x_5367_ = v_reuseFailAlloc_5368_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
return v___x_5367_;
}
}
}
}
v___jp_5370_:
{
lean_object* v_invariants_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; uint8_t v___x_5383_; 
v_invariants_5379_ = lean_ctor_get(v_a_5321_, 0);
v___x_5380_ = lean_unsigned_to_nat(0u);
v___x_5381_ = lean_array_get_size(v_invariants_5379_);
v___x_5382_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___closed__2));
v___x_5383_ = lean_nat_dec_lt(v___x_5380_, v___x_5381_);
if (v___x_5383_ == 0)
{
v___y_5323_ = v___y_5374_;
v___y_5324_ = v___y_5378_;
v___y_5325_ = v___y_5377_;
v___y_5326_ = v___y_5376_;
v___y_5327_ = v___y_5371_;
v___y_5328_ = v___y_5375_;
v___y_5329_ = v___y_5373_;
v___y_5330_ = v___y_5372_;
v_a_5331_ = v___x_5382_;
goto v___jp_5322_;
}
else
{
uint8_t v___x_5384_; 
v___x_5384_ = lean_nat_dec_le(v___x_5381_, v___x_5381_);
if (v___x_5384_ == 0)
{
if (v___x_5383_ == 0)
{
v___y_5323_ = v___y_5374_;
v___y_5324_ = v___y_5378_;
v___y_5325_ = v___y_5377_;
v___y_5326_ = v___y_5376_;
v___y_5327_ = v___y_5371_;
v___y_5328_ = v___y_5375_;
v___y_5329_ = v___y_5373_;
v___y_5330_ = v___y_5372_;
v_a_5331_ = v___x_5382_;
goto v___jp_5322_;
}
else
{
size_t v___x_5385_; size_t v___x_5386_; lean_object* v___x_5387_; 
v___x_5385_ = ((size_t)0ULL);
v___x_5386_ = lean_usize_of_nat(v___x_5381_);
v___x_5387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__3(v_invariants_5379_, v___x_5385_, v___x_5386_, v___x_5382_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_);
v___y_5352_ = v___y_5378_;
v___y_5353_ = v___y_5374_;
v___y_5354_ = v___y_5377_;
v___y_5355_ = v___y_5376_;
v___y_5356_ = v___y_5371_;
v___y_5357_ = v___y_5375_;
v___y_5358_ = v___y_5373_;
v___y_5359_ = v___y_5372_;
v___y_5360_ = v___x_5387_;
goto v___jp_5351_;
}
}
else
{
size_t v___x_5388_; size_t v___x_5389_; lean_object* v___x_5390_; 
v___x_5388_ = ((size_t)0ULL);
v___x_5389_ = lean_usize_of_nat(v___x_5381_);
v___x_5390_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__3(v_invariants_5379_, v___x_5388_, v___x_5389_, v___x_5382_, v___y_5371_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_);
v___y_5352_ = v___y_5378_;
v___y_5353_ = v___y_5374_;
v___y_5354_ = v___y_5377_;
v___y_5355_ = v___y_5376_;
v___y_5356_ = v___y_5371_;
v___y_5357_ = v___y_5375_;
v___y_5358_ = v___y_5373_;
v___y_5359_ = v___y_5372_;
v___y_5360_ = v___x_5390_;
goto v___jp_5351_;
}
}
}
}
else
{
lean_object* v_a_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5407_; 
lean_dec(v_invariantAlts_x3f_5317_);
lean_dec(v_stx_5299_);
v_a_5400_ = lean_ctor_get(v___x_5320_, 0);
v_isSharedCheck_5407_ = !lean_is_exclusive(v___x_5320_);
if (v_isSharedCheck_5407_ == 0)
{
v___x_5402_ = v___x_5320_;
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_a_5400_);
lean_dec(v___x_5320_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5407_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v___x_5405_; 
if (v_isShared_5403_ == 0)
{
v___x_5405_ = v___x_5402_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5406_; 
v_reuseFailAlloc_5406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_a_5400_);
v___x_5405_ = v_reuseFailAlloc_5406_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
return v___x_5405_;
}
}
}
}
else
{
lean_object* v_a_5408_; lean_object* v___x_5410_; uint8_t v_isShared_5411_; uint8_t v_isSharedCheck_5415_; 
lean_dec(v_a_5310_);
lean_dec(v_stx_5299_);
v_a_5408_ = lean_ctor_get(v___x_5311_, 0);
v_isSharedCheck_5415_ = !lean_is_exclusive(v___x_5311_);
if (v_isSharedCheck_5415_ == 0)
{
v___x_5410_ = v___x_5311_;
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
else
{
lean_inc(v_a_5408_);
lean_dec(v___x_5311_);
v___x_5410_ = lean_box(0);
v_isShared_5411_ = v_isSharedCheck_5415_;
goto v_resetjp_5409_;
}
v_resetjp_5409_:
{
lean_object* v___x_5413_; 
if (v_isShared_5411_ == 0)
{
v___x_5413_ = v___x_5410_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v_a_5408_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
}
else
{
lean_object* v_a_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5423_; 
lean_dec(v_stx_5299_);
v_a_5416_ = lean_ctor_get(v___x_5309_, 0);
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5309_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5418_ = v___x_5309_;
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v___x_5309_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5421_; 
if (v_isShared_5419_ == 0)
{
v___x_5421_ = v___x_5418_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5416_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__1___boxed(lean_object* v_stx_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__1(v_stx_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec(v___y_5430_);
lean_dec_ref(v___y_5429_);
lean_dec(v___y_5428_);
lean_dec_ref(v___y_5427_);
lean_dec(v___y_5426_);
lean_dec_ref(v___y_5425_);
return v_res_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27(lean_object* v_stx_5435_, lean_object* v_a_5436_, lean_object* v_a_5437_, lean_object* v_a_5438_, lean_object* v_a_5439_, lean_object* v_a_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_){
_start:
{
lean_object* v___f_5445_; lean_object* v___x_5446_; 
v___f_5445_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___lam__1___boxed), 10, 1);
lean_closure_set(v___f_5445_, 0, v_stx_5435_);
v___x_5446_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5445_, v_a_5436_, v_a_5437_, v_a_5438_, v_a_5439_, v_a_5440_, v_a_5441_, v_a_5442_, v_a_5443_);
return v___x_5446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___boxed(lean_object* v_stx_5447_, lean_object* v_a_5448_, lean_object* v_a_5449_, lean_object* v_a_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_, lean_object* v_a_5455_, lean_object* v_a_5456_){
_start:
{
lean_object* v_res_5457_; 
v_res_5457_ = l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27(v_stx_5447_, v_a_5448_, v_a_5449_, v_a_5450_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_, v_a_5455_);
lean_dec(v_a_5455_);
lean_dec_ref(v_a_5454_);
lean_dec(v_a_5453_);
lean_dec_ref(v_a_5452_);
lean_dec(v_a_5451_);
lean_dec_ref(v_a_5450_);
lean_dec(v_a_5449_);
lean_dec_ref(v_a_5448_);
return v_res_5457_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0(lean_object* v_mvarId_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
lean_object* v___x_5468_; 
v___x_5468_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0___redArg(v_mvarId_5458_, v___y_5464_);
return v___x_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0___boxed(lean_object* v_mvarId_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_){
_start:
{
lean_object* v_res_5479_; 
v_res_5479_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__0(v_mvarId_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_, v___y_5476_, v___y_5477_);
lean_dec(v___y_5477_);
lean_dec_ref(v___y_5476_);
lean_dec(v___y_5475_);
lean_dec_ref(v___y_5474_);
lean_dec(v___y_5473_);
lean_dec_ref(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
lean_dec(v_mvarId_5469_);
return v_res_5479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2(lean_object* v_00_u03b1_5480_, lean_object* v_msg_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_){
_start:
{
lean_object* v___x_5491_; 
v___x_5491_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2___redArg(v_msg_5481_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
return v___x_5491_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2___boxed(lean_object* v_00_u03b1_5492_, lean_object* v_msg_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_, lean_object* v___y_5502_){
_start:
{
lean_object* v_res_5503_; 
v_res_5503_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_spec__2(v_00_u03b1_5492_, v_msg_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_);
lean_dec(v___y_5501_);
lean_dec_ref(v___y_5500_);
lean_dec(v___y_5499_);
lean_dec_ref(v___y_5498_);
lean_dec(v___y_5497_);
lean_dec_ref(v___y_5496_);
lean_dec(v___y_5495_);
lean_dec_ref(v___y_5494_);
return v_res_5503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1(){
_start:
{
lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; 
v___x_5518_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5519_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__0));
v___x_5520_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2));
v___x_5521_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___boxed), 10, 0);
v___x_5522_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5518_, v___x_5519_, v___x_5520_, v___x_5521_);
return v___x_5522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___boxed(lean_object* v_a_5523_){
_start:
{
lean_object* v_res_5524_; 
v_res_5524_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1();
return v_res_5524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_docString__3(){
_start:
{
lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; 
v___x_5527_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1___closed__2));
v___x_5528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_docString__3___closed__0));
v___x_5529_ = l_Lean_addBuiltinDocString(v___x_5527_, v___x_5528_);
return v___x_5529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_docString__3___boxed(lean_object* v_a_5530_){
_start:
{
lean_object* v_res_5531_; 
v_res_5531_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_docString__3();
return v_res_5531_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymMVCGen_x27_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabMVCGen_x27_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_VCGen(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_ControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_EvalGround(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Forall(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Rewrite(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Main(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Grind_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_VCGen_SuggestInvariant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_VCGen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Driver(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend(builtin);
}
#ifdef __cplusplus
}
#endif
