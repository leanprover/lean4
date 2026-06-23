// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Frontend
// Imports: public import Lean.Elab.Tactic.Do.VCGen.SuggestInvariant public import Lean.Elab.Tactic.Do.VCGen public import Lean.Elab.Tactic.Do.Internal.VCGen.Context public import Lean.Elab.Tactic.Do.Internal.VCGen.Driver public import Lean.Meta.Sym.Simp.Attr public import Lean.Meta.Sym.Simp.ControlFlow public import Lean.Meta.Sym.Simp.EvalGround public import Lean.Meta.Sym.Simp.Forall public import Lean.Meta.Sym.Simp.Rewrite public import Lean.Meta.Sym.Simp.Simproc public import Lean.Elab.Tactic.Grind.Main public import Lean.Elab.Tactic.Grind.Basic import Lean.Meta.Sym.ProofInstInfo
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
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshTypeMVar(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectMVars(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* l_Lean_Meta_Sym_mkProofInstInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkProofInstArgInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutErrToSorryImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_TermElabM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkGoalCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkDefaultParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_evalGrindTactic___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_GrindTacticM_runAtGoal___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray3___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_mkArray2___redArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_hint_x27(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_appendConfig(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
lean_object* l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_pos_x21(lean_object*, lean_object*);
lean_object* l_String_Slice_toNat_x3f(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_elabConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems___redArg(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_extendWithSimpSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resolveId_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase(lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_specEraseProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Syntax_SepArray_ofElems(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_mvcgen_warning;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_suggestInvariant___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_elabInvariants___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpErase"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__4_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 24, 229, 171, 59, 186, 144, 157)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__6_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__6_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__6_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__5_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpStar"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__7_value),LEAN_SCALAR_PTR_LITERAL(125, 38, 251, 225, 228, 173, 11, 37)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Could not resolve spec theorem `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__10;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "not a spec theorem"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__11_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__12;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__13_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__4_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__6_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__10_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__12_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unfoldPartialApp"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__16;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15_value),LEAN_SCALAR_PTR_LITERAL(49, 203, 120, 209, 69, 128, 204, 215)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "negConfigItem"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__18_value),LEAN_SCALAR_PTR_LITERAL(196, 29, 29, 161, 247, 206, 181, 221)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zeta"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21_value),LEAN_SCALAR_PTR_LITERAL(56, 247, 87, 81, 188, 35, 250, 148)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__28;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__30;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__32_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__32;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__34;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "vcgen: the `leave` config option is currently ignored."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__0_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 149, .m_capacity = 149, .m_length = 144, .m_data = "named Sym.simp variants are not yet supported in `vcgen`; use `vcgen simplifying_assumptions [thm₁, thm₂, ...]` with the default variant instead"};
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 218, 225, 197, 89, 244, 133, 64)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "invariantCaseAlt"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__2_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__2_value),LEAN_SCALAR_PTR_LITERAL(163, 146, 32, 128, 83, 151, 179, 6)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Expected `invariantDotAlt` or `invariantCaseAlt`."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__6_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value_aux_2),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__6_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__8_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__8_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Alternation between labelled and bulleted invariants is not supported."};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__10 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__10_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "cdotTk"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__12 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__12_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13_value_aux_0),((lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__12_value),LEAN_SCALAR_PTR_LITERAL(117, 126, 44, 217, 38, 3, 69, 145)}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "invariantAlts"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 41, 254, 250, 50, 69, 99, 10)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "invariantsKW"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__0;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__1;
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 1, 0, 1, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 143, .m_capacity = 143, .m_length = 142, .m_data = "The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it. Avoid using it in production projects."};
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 105, 19, 51, 118, 250, 248, 43)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(113, 229, 87, 15, 155, 212, 124, 96)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__4_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__5_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__6_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__7_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__8 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__8_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__7_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(89, 242, 56, 182, 153, 42, 114, 203)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__9_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__10 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__10_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__9_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(132, 236, 244, 1, 128, 181, 211, 156)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "VCGen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__11_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(175, 167, 22, 210, 240, 170, 245, 185)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Frontend"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__13_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(18, 209, 67, 183, 120, 233, 44, 242)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__15_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(147, 197, 196, 233, 158, 77, 49, 202)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__16 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__16_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__16_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(254, 108, 164, 213, 221, 37, 180, 229)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__17 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__17_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__17_value),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 84, 138, 219, 247, 214, 26, 16)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__18 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__18_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__18_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(73, 168, 135, 192, 193, 202, 29, 136)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__19 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__19_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__19_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(109, 141, 169, 199, 171, 247, 59, 245)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__20_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__20_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(64, 59, 250, 17, 189, 47, 163, 133)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__21 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__21_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalSymVCGen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__21_value),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(213, 50, 189, 23, 213, 69, 69, 98)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__23_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 39, .m_data = "`vcgen` step inside `sym => …` blocks. "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_docString__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "vcgenDischargeGrind"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__1_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 199, 17, 154, 227, 108, 8, 170)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 76, .m_data = "`vcgen … with` expects a `grind`-mode discharging step, not a general tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__2_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__3;
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 54, .m_data = "Examples: `vcgen … with finish`, `vcgen … with intro`."};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__5;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__6;
static lean_once_cell_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grind_<;>_"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "simplifying_assumptions"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "until"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "internalize"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__5;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__4_value),LEAN_SCALAR_PTR_LITERAL(46, 126, 89, 140, 218, 11, 77, 16)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___boxed(lean_object**);
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 196, 10, 243, 239, 189, 222, 13)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "elabVCGen"};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value_aux_0),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(101, 141, 64, 183, 187, 157, 254, 157)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(232, 135, 166, 206, 84, 210, 155, 104)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 117, 83, 198, 85, 149, 107, 110)}};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen_docString__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 383, .m_capacity = 383, .m_length = 380, .m_data = "Tactic-level `vcgen`. Reuses the grind-mode implementation by re-quoting the\ninput as `Grind.vcgen …` and running it inside a `GrindTacticM` context built\nwithout `withProtectedMCtx`, so leftover `Grind.Goal`s flow back as the new tactic\ngoals. The optional `with $g:grind` clause runs as `<;> $g` and lets the user-supplied\ngrind step share an internalised E-graph with `vcgen`. "};
static const lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen_docString__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen_docString__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen_docString__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen_docString__3___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___lam__0(lean_object* v___x_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_96_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___lam__0___boxed(lean_object* v___x_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___lam__0(v___x_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_105_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_box(1);
v___x_107_ = l_Lean_MessageData_ofFormat(v___x_106_);
return v___x_107_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__3(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__2));
v___x_112_ = l_Lean_MessageData_ofFormat(v___x_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6(lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
if (lean_obj_tag(v_x_114_) == 0)
{
return v_x_113_;
}
else
{
lean_object* v_head_115_; lean_object* v_tail_116_; lean_object* v___x_118_; uint8_t v_isShared_119_; uint8_t v_isSharedCheck_138_; 
v_head_115_ = lean_ctor_get(v_x_114_, 0);
v_tail_116_ = lean_ctor_get(v_x_114_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_114_);
if (v_isSharedCheck_138_ == 0)
{
v___x_118_ = v_x_114_;
v_isShared_119_ = v_isSharedCheck_138_;
goto v_resetjp_117_;
}
else
{
lean_inc(v_tail_116_);
lean_inc(v_head_115_);
lean_dec(v_x_114_);
v___x_118_ = lean_box(0);
v_isShared_119_ = v_isSharedCheck_138_;
goto v_resetjp_117_;
}
v_resetjp_117_:
{
lean_object* v_before_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_136_; 
v_before_120_ = lean_ctor_get(v_head_115_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_head_115_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v_head_115_, 1);
lean_dec(v_unused_137_);
v___x_122_ = v_head_115_;
v_isShared_123_ = v_isSharedCheck_136_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_before_120_);
lean_dec(v_head_115_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_136_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
v___x_124_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0);
if (v_isShared_123_ == 0)
{
lean_ctor_set_tag(v___x_122_, 7);
lean_ctor_set(v___x_122_, 1, v___x_124_);
lean_ctor_set(v___x_122_, 0, v_x_113_);
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_x_113_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_124_);
v___x_126_ = v_reuseFailAlloc_135_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__3);
if (v_isShared_119_ == 0)
{
lean_ctor_set_tag(v___x_118_, 7);
lean_ctor_set(v___x_118_, 1, v___x_127_);
lean_ctor_set(v___x_118_, 0, v___x_126_);
v___x_129_ = v___x_118_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_134_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_130_ = l_Lean_MessageData_ofSyntax(v_before_120_);
v___x_131_ = l_Lean_indentD(v___x_130_);
v___x_132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_129_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
v_x_113_ = v___x_132_;
v_x_114_ = v_tail_116_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(lean_object* v_opts_139_, lean_object* v_opt_140_){
_start:
{
lean_object* v_name_141_; lean_object* v_defValue_142_; lean_object* v_map_143_; lean_object* v___x_144_; 
v_name_141_ = lean_ctor_get(v_opt_140_, 0);
v_defValue_142_ = lean_ctor_get(v_opt_140_, 1);
v_map_143_ = lean_ctor_get(v_opts_139_, 0);
v___x_144_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_143_, v_name_141_);
if (lean_obj_tag(v___x_144_) == 0)
{
uint8_t v___x_145_; 
v___x_145_ = lean_unbox(v_defValue_142_);
return v___x_145_;
}
else
{
lean_object* v_val_146_; 
v_val_146_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_val_146_);
lean_dec_ref_known(v___x_144_, 1);
if (lean_obj_tag(v_val_146_) == 1)
{
uint8_t v_v_147_; 
v_v_147_ = lean_ctor_get_uint8(v_val_146_, 0);
lean_dec_ref_known(v_val_146_, 0);
return v_v_147_;
}
else
{
uint8_t v___x_148_; 
lean_dec(v_val_146_);
v___x_148_ = lean_unbox(v_defValue_142_);
return v___x_148_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5___boxed(lean_object* v_opts_149_, lean_object* v_opt_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_opts_149_, v_opt_150_);
lean_dec_ref(v_opt_150_);
lean_dec_ref(v_opts_149_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__1));
v___x_157_ = l_Lean_MessageData_ofFormat(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg(lean_object* v_msgData_158_, lean_object* v_macroStack_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_options_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v_options_162_ = lean_ctor_get(v___y_160_, 2);
v___x_163_ = l_Lean_Elab_pp_macroStack;
v___x_164_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_options_162_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; 
lean_dec(v_macroStack_159_);
v___x_165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_165_, 0, v_msgData_158_);
return v___x_165_;
}
else
{
if (lean_obj_tag(v_macroStack_159_) == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v_msgData_158_);
return v___x_166_;
}
else
{
lean_object* v_head_167_; lean_object* v_after_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_183_; 
v_head_167_ = lean_ctor_get(v_macroStack_159_, 0);
lean_inc(v_head_167_);
v_after_168_ = lean_ctor_get(v_head_167_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v_head_167_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v_head_167_, 0);
lean_dec(v_unused_184_);
v___x_170_ = v_head_167_;
v_isShared_171_ = v_isSharedCheck_183_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_after_168_);
lean_dec(v_head_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_183_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6___closed__0);
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 7);
lean_ctor_set(v___x_170_, 1, v___x_172_);
lean_ctor_set(v___x_170_, 0, v_msgData_158_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_msgData_158_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_182_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_msgData_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_175_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___closed__2);
v___x_176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_174_);
lean_ctor_set(v___x_176_, 1, v___x_175_);
v___x_177_ = l_Lean_MessageData_ofSyntax(v_after_168_);
v___x_178_ = l_Lean_indentD(v___x_177_);
v_msgData_179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_179_, 0, v___x_176_);
lean_ctor_set(v_msgData_179_, 1, v___x_178_);
v___x_180_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__6(v_msgData_179_, v_macroStack_159_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_185_, lean_object* v_macroStack_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg(v_msgData_185_, v_macroStack_186_, v___y_187_);
lean_dec_ref(v___y_187_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(lean_object* v_msgData_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; lean_object* v_env_197_; lean_object* v___x_198_; lean_object* v_mctx_199_; lean_object* v_lctx_200_; lean_object* v_options_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_196_ = lean_st_ref_get(v___y_194_);
v_env_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc_ref(v_env_197_);
lean_dec(v___x_196_);
v___x_198_ = lean_st_ref_get(v___y_192_);
v_mctx_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc_ref(v_mctx_199_);
lean_dec(v___x_198_);
v_lctx_200_ = lean_ctor_get(v___y_191_, 2);
v_options_201_ = lean_ctor_get(v___y_193_, 2);
lean_inc_ref(v_options_201_);
lean_inc_ref(v_lctx_200_);
v___x_202_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_202_, 0, v_env_197_);
lean_ctor_set(v___x_202_, 1, v_mctx_199_);
lean_ctor_set(v___x_202_, 2, v_lctx_200_);
lean_ctor_set(v___x_202_, 3, v_options_201_);
v___x_203_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v_msgData_190_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1___boxed(lean_object* v_msgData_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v_msgData_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_ref_220_; lean_object* v___x_221_; lean_object* v_a_222_; lean_object* v_macroStack_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_234_; 
v_ref_220_ = lean_ctor_get(v___y_217_, 5);
v___x_221_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v_msg_212_, v___y_215_, v___y_216_, v___y_217_, v___y_218_);
v_a_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_a_222_);
lean_dec_ref(v___x_221_);
v_macroStack_223_ = lean_ctor_get(v___y_213_, 1);
v___x_224_ = l_Lean_Elab_getBetterRef(v_ref_220_, v_macroStack_223_);
lean_inc(v_macroStack_223_);
v___x_225_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg(v_a_222_, v_macroStack_223_, v___y_217_);
v_a_226_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_234_ == 0)
{
v___x_228_ = v___x_225_;
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_225_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_234_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_224_);
lean_ctor_set(v___x_230_, 1, v_a_226_);
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 1);
lean_ctor_set(v___x_228_, 0, v___x_230_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_230_);
v___x_232_ = v_reuseFailAlloc_233_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg___boxed(lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(v_msg_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(lean_object* v_ref_244_, lean_object* v_msg_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_fileName_253_; lean_object* v_fileMap_254_; lean_object* v_options_255_; lean_object* v_currRecDepth_256_; lean_object* v_maxRecDepth_257_; lean_object* v_ref_258_; lean_object* v_currNamespace_259_; lean_object* v_openDecls_260_; lean_object* v_initHeartbeats_261_; lean_object* v_maxHeartbeats_262_; lean_object* v_quotContext_263_; lean_object* v_currMacroScope_264_; uint8_t v_diag_265_; lean_object* v_cancelTk_x3f_266_; uint8_t v_suppressElabErrors_267_; lean_object* v_inheritedTraceOptions_268_; lean_object* v_ref_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_fileName_253_ = lean_ctor_get(v___y_250_, 0);
v_fileMap_254_ = lean_ctor_get(v___y_250_, 1);
v_options_255_ = lean_ctor_get(v___y_250_, 2);
v_currRecDepth_256_ = lean_ctor_get(v___y_250_, 3);
v_maxRecDepth_257_ = lean_ctor_get(v___y_250_, 4);
v_ref_258_ = lean_ctor_get(v___y_250_, 5);
v_currNamespace_259_ = lean_ctor_get(v___y_250_, 6);
v_openDecls_260_ = lean_ctor_get(v___y_250_, 7);
v_initHeartbeats_261_ = lean_ctor_get(v___y_250_, 8);
v_maxHeartbeats_262_ = lean_ctor_get(v___y_250_, 9);
v_quotContext_263_ = lean_ctor_get(v___y_250_, 10);
v_currMacroScope_264_ = lean_ctor_get(v___y_250_, 11);
v_diag_265_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*14);
v_cancelTk_x3f_266_ = lean_ctor_get(v___y_250_, 12);
v_suppressElabErrors_267_ = lean_ctor_get_uint8(v___y_250_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_268_ = lean_ctor_get(v___y_250_, 13);
v_ref_269_ = l_Lean_replaceRef(v_ref_244_, v_ref_258_);
lean_inc_ref(v_inheritedTraceOptions_268_);
lean_inc(v_cancelTk_x3f_266_);
lean_inc(v_currMacroScope_264_);
lean_inc(v_quotContext_263_);
lean_inc(v_maxHeartbeats_262_);
lean_inc(v_initHeartbeats_261_);
lean_inc(v_openDecls_260_);
lean_inc(v_currNamespace_259_);
lean_inc(v_maxRecDepth_257_);
lean_inc(v_currRecDepth_256_);
lean_inc_ref(v_options_255_);
lean_inc_ref(v_fileMap_254_);
lean_inc_ref(v_fileName_253_);
v___x_270_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_270_, 0, v_fileName_253_);
lean_ctor_set(v___x_270_, 1, v_fileMap_254_);
lean_ctor_set(v___x_270_, 2, v_options_255_);
lean_ctor_set(v___x_270_, 3, v_currRecDepth_256_);
lean_ctor_set(v___x_270_, 4, v_maxRecDepth_257_);
lean_ctor_set(v___x_270_, 5, v_ref_269_);
lean_ctor_set(v___x_270_, 6, v_currNamespace_259_);
lean_ctor_set(v___x_270_, 7, v_openDecls_260_);
lean_ctor_set(v___x_270_, 8, v_initHeartbeats_261_);
lean_ctor_set(v___x_270_, 9, v_maxHeartbeats_262_);
lean_ctor_set(v___x_270_, 10, v_quotContext_263_);
lean_ctor_set(v___x_270_, 11, v_currMacroScope_264_);
lean_ctor_set(v___x_270_, 12, v_cancelTk_x3f_266_);
lean_ctor_set(v___x_270_, 13, v_inheritedTraceOptions_268_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*14, v_diag_265_);
lean_ctor_set_uint8(v___x_270_, sizeof(void*)*14 + 1, v_suppressElabErrors_267_);
v___x_271_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(v_msg_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___x_270_, v___y_251_);
lean_dec_ref_known(v___x_270_, 14);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg___boxed(lean_object* v_ref_272_, lean_object* v_msg_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(v_ref_272_, v_msg_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v_ref_272_);
return v_res_281_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_282_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__0);
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__2(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__1);
v___x_286_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
lean_ctor_set(v___x_287_, 2, v___x_286_);
lean_ctor_set(v___x_287_, 3, v___x_286_);
lean_ctor_set(v___x_287_, 4, v___x_285_);
lean_ctor_set(v___x_287_, 5, v___x_285_);
lean_ctor_set(v___x_287_, 6, v___x_285_);
lean_ctor_set(v___x_287_, 7, v___x_285_);
lean_ctor_set(v___x_287_, 8, v___x_285_);
lean_ctor_set(v___x_287_, 9, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(32u);
v___x_289_ = lean_mk_empty_array_with_capacity(v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__4(void){
_start:
{
size_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_291_ = ((size_t)5ULL);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_unsigned_to_nat(32u);
v___x_294_ = lean_mk_empty_array_with_capacity(v___x_293_);
v___x_295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__3);
v___x_296_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_294_);
lean_ctor_set(v___x_296_, 2, v___x_292_);
lean_ctor_set(v___x_296_, 3, v___x_292_);
lean_ctor_set_usize(v___x_296_, 4, v___x_291_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__5(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_box(1);
v___x_298_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__4);
v___x_299_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__1);
v___x_300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
lean_ctor_set(v___x_300_, 2, v___x_297_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__7(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__6));
v___x_303_ = l_Lean_stringToMessageData(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__9(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__8));
v___x_306_ = l_Lean_stringToMessageData(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__11(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__10));
v___x_309_ = l_Lean_stringToMessageData(v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__13(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__12));
v___x_312_ = l_Lean_stringToMessageData(v___x_311_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__15(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__14));
v___x_315_ = l_Lean_stringToMessageData(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__17(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__16));
v___x_318_ = l_Lean_stringToMessageData(v___x_317_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__19(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__18));
v___x_321_ = l_Lean_stringToMessageData(v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg(lean_object* v_msg_322_, lean_object* v_declHint_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; lean_object* v_env_327_; uint8_t v___x_328_; 
v___x_326_ = lean_st_ref_get(v___y_324_);
v_env_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_env_327_);
lean_dec(v___x_326_);
v___x_328_ = l_Lean_Name_isAnonymous(v_declHint_323_);
if (v___x_328_ == 0)
{
uint8_t v_isExporting_329_; 
v_isExporting_329_ = lean_ctor_get_uint8(v_env_327_, sizeof(void*)*8);
if (v_isExporting_329_ == 0)
{
lean_object* v___x_330_; 
lean_dec_ref(v_env_327_);
lean_dec(v_declHint_323_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v_msg_322_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; uint8_t v___x_332_; 
lean_inc_ref(v_env_327_);
v___x_331_ = l_Lean_Environment_setExporting(v_env_327_, v___x_328_);
lean_inc(v_declHint_323_);
lean_inc_ref(v___x_331_);
v___x_332_ = l_Lean_Environment_contains(v___x_331_, v_declHint_323_, v_isExporting_329_);
if (v___x_332_ == 0)
{
lean_object* v___x_333_; 
lean_dec_ref(v___x_331_);
lean_dec_ref(v_env_327_);
lean_dec(v_declHint_323_);
v___x_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_333_, 0, v_msg_322_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_c_339_; lean_object* v___x_340_; 
v___x_334_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__2);
v___x_335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__5);
v___x_336_ = l_Lean_Options_empty;
v___x_337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_337_, 0, v___x_331_);
lean_ctor_set(v___x_337_, 1, v___x_334_);
lean_ctor_set(v___x_337_, 2, v___x_335_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
lean_inc(v_declHint_323_);
v___x_338_ = l_Lean_MessageData_ofConstName(v_declHint_323_, v___x_328_);
v_c_339_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_339_, 0, v___x_337_);
lean_ctor_set(v_c_339_, 1, v___x_338_);
v___x_340_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_327_, v_declHint_323_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec_ref(v_env_327_);
lean_dec(v_declHint_323_);
v___x_341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__7);
v___x_342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v_c_339_);
v___x_343_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__9);
v___x_344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = l_Lean_MessageData_note(v___x_344_);
v___x_346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_346_, 0, v_msg_322_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
return v___x_347_;
}
else
{
lean_object* v_val_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_383_; 
v_val_348_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_383_ == 0)
{
v___x_350_ = v___x_340_;
v_isShared_351_ = v_isSharedCheck_383_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_val_348_);
lean_dec(v___x_340_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_383_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v_mod_355_; uint8_t v___x_356_; 
v___x_352_ = lean_box(0);
v___x_353_ = l_Lean_Environment_header(v_env_327_);
lean_dec_ref(v_env_327_);
v___x_354_ = l_Lean_EnvironmentHeader_moduleNames(v___x_353_);
v_mod_355_ = lean_array_get(v___x_352_, v___x_354_, v_val_348_);
lean_dec(v_val_348_);
lean_dec_ref(v___x_354_);
v___x_356_ = l_Lean_isPrivateName(v_declHint_323_);
lean_dec(v_declHint_323_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_357_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__11);
v___x_358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_c_339_);
v___x_359_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__13);
v___x_360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = l_Lean_MessageData_ofName(v_mod_355_);
v___x_362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__15);
v___x_364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_362_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
v___x_365_ = l_Lean_MessageData_note(v___x_364_);
v___x_366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_366_, 0, v_msg_322_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 0);
lean_ctor_set(v___x_350_, 0, v___x_366_);
v___x_368_ = v___x_350_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
else
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__7);
v___x_371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v_c_339_);
v___x_372_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__17);
v___x_373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = l_Lean_MessageData_ofName(v_mod_355_);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__19);
v___x_377_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_375_);
lean_ctor_set(v___x_377_, 1, v___x_376_);
v___x_378_ = l_Lean_MessageData_note(v___x_377_);
v___x_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_379_, 0, v_msg_322_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 0);
lean_ctor_set(v___x_350_, 0, v___x_379_);
v___x_381_ = v___x_350_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_384_; 
lean_dec_ref(v_env_327_);
lean_dec(v_declHint_323_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v_msg_322_);
return v___x_384_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___boxed(lean_object* v_msg_385_, lean_object* v_declHint_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg(v_msg_385_, v_declHint_386_, v___y_387_);
lean_dec(v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13(lean_object* v_msg_390_, lean_object* v_declHint_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v___x_399_; lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_409_; 
v___x_399_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg(v_msg_390_, v_declHint_391_, v___y_397_);
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_409_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_409_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_407_; 
v___x_404_ = l_Lean_unknownIdentifierMessageTag;
v___x_405_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_a_400_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_405_);
v___x_407_ = v___x_402_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13___boxed(lean_object* v_msg_410_, lean_object* v_declHint_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13(v_msg_410_, v_declHint_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
lean_dec_ref(v___y_414_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10___redArg(lean_object* v_ref_420_, lean_object* v_msg_421_, lean_object* v_declHint_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___x_430_; lean_object* v_a_431_; lean_object* v___x_432_; 
v___x_430_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13(v_msg_421_, v_declHint_422_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
v_a_431_ = lean_ctor_get(v___x_430_, 0);
lean_inc(v_a_431_);
lean_dec_ref(v___x_430_);
v___x_432_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(v_ref_420_, v_a_431_, v___y_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10___redArg___boxed(lean_object* v_ref_433_, lean_object* v_msg_434_, lean_object* v_declHint_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10___redArg(v_ref_433_, v_msg_434_, v_declHint_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v_ref_433_);
return v_res_443_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__0));
v___x_446_ = l_Lean_stringToMessageData(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__2));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg(lean_object* v_ref_450_, lean_object* v_constName_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v___x_459_; uint8_t v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_459_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__1);
v___x_460_ = 0;
lean_inc(v_constName_451_);
v___x_461_ = l_Lean_MessageData_ofConstName(v_constName_451_, v___x_460_);
v___x_462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_459_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
v___x_463_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__3);
v___x_464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_462_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
v___x_465_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10___redArg(v_ref_450_, v___x_464_, v_constName_451_, v___y_452_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___boxed(lean_object* v_ref_466_, lean_object* v_constName_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg(v_ref_466_, v_constName_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v_ref_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___redArg(lean_object* v_constName_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_){
_start:
{
lean_object* v_ref_484_; lean_object* v___x_485_; 
v_ref_484_ = lean_ctor_get(v___y_481_, 5);
v___x_485_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg(v_ref_484_, v_constName_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___redArg___boxed(lean_object* v_constName_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___redArg(v_constName_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg(lean_object* v_as_495_, size_t v_sz_496_, size_t v_i_497_, lean_object* v_b_498_){
_start:
{
uint8_t v___x_500_; 
v___x_500_ = lean_usize_dec_lt(v_i_497_, v_sz_496_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v_b_498_);
return v___x_501_;
}
else
{
lean_object* v_fst_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_515_; 
v_fst_502_ = lean_ctor_get(v_b_498_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v_b_498_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_b_498_, 1);
lean_dec(v_unused_516_);
v___x_504_ = v_b_498_;
v_isShared_505_ = v_isSharedCheck_515_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_fst_502_);
lean_dec(v_b_498_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_515_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v_a_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_510_; 
v_a_506_ = lean_array_uget_borrowed(v_as_495_, v_i_497_);
lean_inc(v_a_506_);
v___x_507_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase(v_fst_502_, v_a_506_);
v___x_508_ = lean_box(v___x_500_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 1, v___x_508_);
lean_ctor_set(v___x_504_, 0, v___x_507_);
v___x_510_ = v___x_504_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_507_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_508_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
size_t v___x_511_; size_t v___x_512_; 
v___x_511_ = ((size_t)1ULL);
v___x_512_ = lean_usize_add(v_i_497_, v___x_511_);
v_i_497_ = v___x_512_;
v_b_498_ = v___x_510_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg___boxed(lean_object* v_as_517_, lean_object* v_sz_518_, lean_object* v_i_519_, lean_object* v_b_520_, lean_object* v___y_521_){
_start:
{
size_t v_sz_boxed_522_; size_t v_i_boxed_523_; lean_object* v_res_524_; 
v_sz_boxed_522_ = lean_unbox_usize(v_sz_518_);
lean_dec(v_sz_518_);
v_i_boxed_523_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg(v_as_517_, v_sz_boxed_522_, v_i_boxed_523_, v_b_520_);
lean_dec_ref(v_as_517_);
return v_res_524_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__10(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__9));
v___x_548_ = l_Lean_stringToMessageData(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__12(void){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__11));
v___x_551_ = l_Lean_stringToMessageData(v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4(lean_object* v_as_553_, size_t v_sz_554_, size_t v_i_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_a_565_; uint8_t v___x_569_; 
v___x_569_ = lean_usize_dec_lt(v_i_555_, v_sz_554_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v_b_556_);
return v___x_570_;
}
else
{
lean_object* v_snd_571_; lean_object* v_fst_572_; lean_object* v___x_574_; uint8_t v_isShared_575_; uint8_t v_isSharedCheck_825_; 
v_snd_571_ = lean_ctor_get(v_b_556_, 1);
v_fst_572_ = lean_ctor_get(v_b_556_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v_b_556_);
if (v_isSharedCheck_825_ == 0)
{
v___x_574_ = v_b_556_;
v_isShared_575_ = v_isSharedCheck_825_;
goto v_resetjp_573_;
}
else
{
lean_inc(v_snd_571_);
lean_inc(v_fst_572_);
lean_dec(v_b_556_);
v___x_574_ = lean_box(0);
v_isShared_575_ = v_isSharedCheck_825_;
goto v_resetjp_573_;
}
v_resetjp_573_:
{
lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_824_; 
v_fst_576_ = lean_ctor_get(v_snd_571_, 0);
v_snd_577_ = lean_ctor_get(v_snd_571_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_snd_571_);
if (v_isSharedCheck_824_ == 0)
{
v___x_579_ = v_snd_571_;
v_isShared_580_ = v_isSharedCheck_824_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snd_577_);
lean_inc(v_fst_576_);
lean_dec(v_snd_571_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_824_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v_fst_582_; lean_object* v_snd_583_; lean_object* v_fst_591_; lean_object* v_snd_592_; lean_object* v___x_595_; lean_object* v_a_596_; lean_object* v___y_598_; uint8_t v___y_599_; lean_object* v_a_603_; lean_object* v___y_607_; uint8_t v___y_608_; lean_object* v_a_612_; lean_object* v_fst_620_; lean_object* v_fst_625_; lean_object* v_snd_626_; lean_object* v___y_631_; uint8_t v___y_632_; lean_object* v_a_635_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_595_ = lean_unsigned_to_nat(1u);
v_a_596_ = lean_array_uget_borrowed(v_as_553_, v_i_555_);
lean_inc(v_a_596_);
v___x_638_ = l_Lean_Syntax_getKind(v_a_596_);
v___x_639_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__4));
v___x_640_ = lean_name_eq(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__6));
v___x_642_ = lean_name_eq(v___x_638_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; uint8_t v___x_644_; 
lean_del_object(v___x_579_);
lean_del_object(v___x_574_);
v___x_643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__8));
v___x_644_ = lean_name_eq(v___x_638_, v___x_643_);
lean_dec(v___x_638_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg();
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec_ref_known(v___x_645_, 1);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v_fst_576_);
lean_ctor_set(v___x_646_, 1, v_snd_577_);
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v_fst_572_);
lean_ctor_set(v___x_647_, 1, v___x_646_);
v_a_565_ = v___x_647_;
goto v___jp_564_;
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
lean_dec(v_fst_572_);
v_a_648_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_645_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_645_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v_snd_577_);
lean_inc(v_a_596_);
v___x_656_ = lean_array_push(v_fst_576_, v_a_596_);
v___x_657_ = lean_box(v___x_569_);
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v_fst_572_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v_a_565_ = v___x_659_;
goto v___jp_564_;
}
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
lean_dec(v___x_638_);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = l_Lean_Syntax_getArg(v_a_596_, v___x_660_);
v___x_662_ = l_Lean_Syntax_isNone(v___x_661_);
lean_dec(v___x_661_);
if (v___x_662_ == 0)
{
lean_del_object(v___x_579_);
lean_del_object(v___x_574_);
goto v___jp_615_;
}
else
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = l_Lean_Syntax_getArg(v_a_596_, v___x_595_);
v___x_664_ = l_Lean_Syntax_isNone(v___x_663_);
lean_dec(v___x_663_);
if (v___x_664_ == 0)
{
lean_del_object(v___x_579_);
lean_del_object(v___x_574_);
goto v___jp_615_;
}
else
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Meta_saveState___redArg(v___y_560_, v___y_562_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_711_; lean_object* v___x_742_; lean_object* v___x_743_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v___x_665_, 1);
v___x_667_ = lean_unsigned_to_nat(2u);
v___x_668_ = l_Lean_Syntax_getArg(v_a_596_, v___x_667_);
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__13));
lean_inc(v___x_668_);
v___x_743_ = l_Lean_Elab_Term_resolveId_x3f(v___x_668_, v___x_742_, v___x_569_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_dec(v_a_666_);
v___y_711_ = v___x_743_;
goto v___jp_710_;
}
else
{
lean_object* v_a_744_; uint8_t v___y_746_; uint8_t v___x_757_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
v___x_757_ = l_Lean_Exception_isInterrupt(v_a_744_);
if (v___x_757_ == 0)
{
uint8_t v___x_758_; 
v___x_758_ = l_Lean_Exception_isRuntime(v_a_744_);
v___y_746_ = v___x_758_;
goto v___jp_745_;
}
else
{
lean_dec(v_a_744_);
v___y_746_ = v___x_757_;
goto v___jp_745_;
}
v___jp_745_:
{
if (v___y_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec_ref_known(v___x_743_, 1);
v___x_747_ = l_Lean_Meta_SavedState_restore___redArg(v_a_666_, v___y_560_, v___y_562_);
lean_dec(v_a_666_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v___x_748_; 
lean_dec_ref_known(v___x_747_, 1);
lean_inc(v___x_668_);
v___x_748_ = l_Lean_Elab_Term_elabCDotFunctionAlias_x3f(v___x_668_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
v___y_711_ = v___x_748_;
goto v___jp_710_;
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v___x_668_);
lean_del_object(v___x_579_);
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
lean_del_object(v___x_574_);
lean_dec(v_fst_572_);
v_a_749_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_747_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_747_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
else
{
lean_dec(v_a_666_);
v___y_711_ = v___x_743_;
goto v___jp_710_;
}
}
}
v___jp_669_:
{
lean_object* v_fileName_676_; lean_object* v_fileMap_677_; lean_object* v_options_678_; lean_object* v_currRecDepth_679_; lean_object* v_maxRecDepth_680_; lean_object* v_ref_681_; lean_object* v_currNamespace_682_; lean_object* v_openDecls_683_; lean_object* v_initHeartbeats_684_; lean_object* v_maxHeartbeats_685_; lean_object* v_quotContext_686_; lean_object* v_currMacroScope_687_; uint8_t v_diag_688_; lean_object* v_cancelTk_x3f_689_; uint8_t v_suppressElabErrors_690_; lean_object* v_inheritedTraceOptions_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_ref_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v_fileName_676_ = lean_ctor_get(v___y_674_, 0);
v_fileMap_677_ = lean_ctor_get(v___y_674_, 1);
v_options_678_ = lean_ctor_get(v___y_674_, 2);
v_currRecDepth_679_ = lean_ctor_get(v___y_674_, 3);
v_maxRecDepth_680_ = lean_ctor_get(v___y_674_, 4);
v_ref_681_ = lean_ctor_get(v___y_674_, 5);
v_currNamespace_682_ = lean_ctor_get(v___y_674_, 6);
v_openDecls_683_ = lean_ctor_get(v___y_674_, 7);
v_initHeartbeats_684_ = lean_ctor_get(v___y_674_, 8);
v_maxHeartbeats_685_ = lean_ctor_get(v___y_674_, 9);
v_quotContext_686_ = lean_ctor_get(v___y_674_, 10);
v_currMacroScope_687_ = lean_ctor_get(v___y_674_, 11);
v_diag_688_ = lean_ctor_get_uint8(v___y_674_, sizeof(void*)*14);
v_cancelTk_x3f_689_ = lean_ctor_get(v___y_674_, 12);
v_suppressElabErrors_690_ = lean_ctor_get_uint8(v___y_674_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_691_ = lean_ctor_get(v___y_674_, 13);
v___x_692_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__10, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__10);
lean_inc(v___x_668_);
v___x_693_ = l_Lean_MessageData_ofSyntax(v___x_668_);
v___x_694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg___closed__3);
v___x_696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_694_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v_ref_697_ = l_Lean_replaceRef(v___x_668_, v_ref_681_);
lean_dec(v___x_668_);
lean_inc_ref(v_inheritedTraceOptions_691_);
lean_inc(v_cancelTk_x3f_689_);
lean_inc(v_currMacroScope_687_);
lean_inc(v_quotContext_686_);
lean_inc(v_maxHeartbeats_685_);
lean_inc(v_initHeartbeats_684_);
lean_inc(v_openDecls_683_);
lean_inc(v_currNamespace_682_);
lean_inc(v_maxRecDepth_680_);
lean_inc(v_currRecDepth_679_);
lean_inc_ref(v_options_678_);
lean_inc_ref(v_fileMap_677_);
lean_inc_ref(v_fileName_676_);
v___x_698_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_698_, 0, v_fileName_676_);
lean_ctor_set(v___x_698_, 1, v_fileMap_677_);
lean_ctor_set(v___x_698_, 2, v_options_678_);
lean_ctor_set(v___x_698_, 3, v_currRecDepth_679_);
lean_ctor_set(v___x_698_, 4, v_maxRecDepth_680_);
lean_ctor_set(v___x_698_, 5, v_ref_697_);
lean_ctor_set(v___x_698_, 6, v_currNamespace_682_);
lean_ctor_set(v___x_698_, 7, v_openDecls_683_);
lean_ctor_set(v___x_698_, 8, v_initHeartbeats_684_);
lean_ctor_set(v___x_698_, 9, v_maxHeartbeats_685_);
lean_ctor_set(v___x_698_, 10, v_quotContext_686_);
lean_ctor_set(v___x_698_, 11, v_currMacroScope_687_);
lean_ctor_set(v___x_698_, 12, v_cancelTk_x3f_689_);
lean_ctor_set(v___x_698_, 13, v_inheritedTraceOptions_691_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*14, v_diag_688_);
lean_ctor_set_uint8(v___x_698_, sizeof(void*)*14 + 1, v_suppressElabErrors_690_);
v___x_699_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(v___x_696_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___x_698_, v___y_675_);
lean_dec_ref_known(v___x_698_, 14);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; 
lean_dec_ref_known(v___x_699_, 1);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v_fst_576_);
lean_ctor_set(v___x_700_, 1, v_snd_577_);
v___x_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_701_, 0, v_fst_572_);
lean_ctor_set(v___x_701_, 1, v___x_700_);
v_a_565_ = v___x_701_;
goto v___jp_564_;
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
lean_dec(v_fst_572_);
v_a_702_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_699_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_699_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
v___jp_710_:
{
if (lean_obj_tag(v___y_711_) == 0)
{
lean_object* v_a_712_; 
v_a_712_ = lean_ctor_get(v___y_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___y_711_, 1);
if (lean_obj_tag(v_a_712_) == 1)
{
lean_object* v_val_713_; 
v_val_713_ = lean_ctor_get(v_a_712_, 0);
lean_inc(v_val_713_);
lean_dec_ref_known(v_a_712_, 1);
switch(lean_obj_tag(v_val_713_))
{
case 4:
{
lean_object* v_declName_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec(v___x_668_);
lean_del_object(v___x_579_);
lean_del_object(v___x_574_);
v_declName_714_ = lean_ctor_get(v_val_713_, 0);
lean_inc(v_declName_714_);
lean_dec_ref_known(v_val_713_, 2);
v___x_715_ = lean_unsigned_to_nat(1000u);
v___x_716_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromConst(v_declName_714_, v___x_715_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_a_717_; 
v_a_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_717_);
lean_dec_ref_known(v___x_716_, 1);
if (lean_obj_tag(v_a_717_) == 1)
{
lean_object* v_val_718_; lean_object* v___x_719_; 
v_val_718_ = lean_ctor_get(v_a_717_, 0);
lean_inc(v_val_718_);
lean_dec_ref_known(v_a_717_, 1);
v___x_719_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert(v_fst_572_, v_val_718_);
v_fst_591_ = v___x_719_;
v_snd_592_ = v_fst_576_;
goto v___jp_590_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v_a_717_);
v___x_720_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__12);
v___x_721_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(v___x_720_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_dec_ref_known(v___x_721_, 1);
v_fst_591_ = v_fst_572_;
v_snd_592_ = v_fst_576_;
goto v___jp_590_;
}
else
{
lean_object* v_a_722_; 
v_a_722_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_a_722_);
lean_dec_ref_known(v___x_721_, 1);
v_a_603_ = v_a_722_;
goto v___jp_602_;
}
}
}
else
{
lean_object* v_a_723_; 
v_a_723_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_a_723_);
lean_dec_ref_known(v___x_716_, 1);
v_a_603_ = v_a_723_;
goto v___jp_602_;
}
}
case 1:
{
lean_object* v_fvarId_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec(v___x_668_);
v_fvarId_724_ = lean_ctor_get(v_val_713_, 0);
lean_inc(v_fvarId_724_);
lean_dec_ref_known(v_val_713_, 1);
v___x_725_ = lean_unsigned_to_nat(1000u);
v___x_726_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(v_fvarId_724_, v___x_725_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
if (lean_obj_tag(v_a_727_) == 1)
{
lean_object* v_val_728_; lean_object* v___x_729_; 
v_val_728_ = lean_ctor_get(v_a_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref_known(v_a_727_, 1);
v___x_729_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert(v_fst_572_, v_val_728_);
v_fst_582_ = v___x_729_;
v_snd_583_ = v_fst_576_;
goto v___jp_581_;
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_dec(v_a_727_);
v___x_730_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__12, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__12_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__12);
v___x_731_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(v___x_730_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_dec_ref_known(v___x_731_, 1);
v_fst_582_ = v_fst_572_;
v_snd_583_ = v_fst_576_;
goto v___jp_581_;
}
else
{
lean_object* v_a_732_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v_a_612_ = v_a_732_;
goto v___jp_611_;
}
}
}
else
{
lean_object* v_a_733_; 
v_a_733_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_726_, 1);
v_a_612_ = v_a_733_;
goto v___jp_611_;
}
}
default: 
{
lean_dec(v_val_713_);
lean_del_object(v___x_579_);
lean_del_object(v___x_574_);
v___y_670_ = v___y_557_;
v___y_671_ = v___y_558_;
v___y_672_ = v___y_559_;
v___y_673_ = v___y_560_;
v___y_674_ = v___y_561_;
v___y_675_ = v___y_562_;
goto v___jp_669_;
}
}
}
else
{
lean_dec(v_a_712_);
lean_del_object(v___x_579_);
lean_del_object(v___x_574_);
v___y_670_ = v___y_557_;
v___y_671_ = v___y_558_;
v___y_672_ = v___y_559_;
v___y_673_ = v___y_560_;
v___y_674_ = v___y_561_;
v___y_675_ = v___y_562_;
goto v___jp_669_;
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v___x_668_);
lean_del_object(v___x_579_);
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
lean_del_object(v___x_574_);
lean_dec(v_fst_572_);
v_a_734_ = lean_ctor_get(v___y_711_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___y_711_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___y_711_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___y_711_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
else
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_766_; 
lean_del_object(v___x_579_);
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
lean_del_object(v___x_574_);
lean_dec(v_fst_572_);
v_a_759_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_766_ == 0)
{
v___x_761_ = v___x_665_;
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v___x_665_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_766_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v___x_638_);
lean_del_object(v___x_579_);
lean_del_object(v___x_574_);
v___x_767_ = l_Lean_Syntax_getArg(v_a_596_, v___x_595_);
lean_inc(v___x_767_);
v___x_768_ = l_Lean_Elab_Term_isLocalIdent_x3f(v___x_767_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
if (lean_obj_tag(v_a_769_) == 1)
{
lean_object* v_val_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec(v___x_767_);
v_val_770_ = lean_ctor_get(v_a_769_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v_a_769_, 1);
v___x_771_ = l_Lean_Expr_fvarId_x21(v_val_770_);
lean_dec(v_val_770_);
v___x_772_ = lean_unsigned_to_nat(1000u);
v___x_773_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(v___x_771_, v___x_772_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
if (lean_obj_tag(v_a_774_) == 1)
{
lean_object* v_val_775_; lean_object* v_proof_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v_val_775_ = lean_ctor_get(v_a_774_, 0);
lean_inc(v_val_775_);
lean_dec_ref_known(v_a_774_, 1);
v_proof_776_ = lean_ctor_get(v_val_775_, 1);
lean_inc_ref(v_proof_776_);
lean_dec(v_val_775_);
v___x_777_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_erase(v_fst_572_, v_proof_776_);
v___x_778_ = lean_box(v___x_569_);
v_fst_625_ = v___x_777_;
v_snd_626_ = v___x_778_;
goto v___jp_624_;
}
else
{
lean_dec(v_a_774_);
v_fst_620_ = v_fst_572_;
goto v___jp_619_;
}
}
else
{
lean_object* v_a_779_; 
v_a_779_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_773_, 1);
v_a_635_ = v_a_779_;
goto v___jp_634_;
}
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; 
lean_dec(v_a_769_);
v___x_780_ = lean_box(0);
lean_inc(v___x_767_);
v___x_781_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(v___x_767_, v___x_780_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_781_) == 0)
{
lean_object* v_a_782_; lean_object* v___x_783_; 
lean_dec(v___x_767_);
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref_known(v___x_781_, 1);
v___x_783_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_specEraseProofs(v_a_782_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_a_784_; uint8_t v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; size_t v_sz_788_; size_t v___x_789_; lean_object* v___x_790_; 
v_a_784_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_784_);
lean_dec_ref_known(v___x_783_, 1);
v___x_785_ = 0;
v___x_786_ = lean_box(v___x_785_);
lean_inc(v_fst_572_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_fst_572_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v_sz_788_ = lean_array_size(v_a_784_);
v___x_789_ = ((size_t)0ULL);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg(v_a_784_, v_sz_788_, v___x_789_, v___x_787_);
lean_dec(v_a_784_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v_fst_792_; lean_object* v_snd_793_; 
lean_dec(v_fst_572_);
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
v_fst_792_ = lean_ctor_get(v_a_791_, 0);
lean_inc(v_fst_792_);
v_snd_793_ = lean_ctor_get(v_a_791_, 1);
lean_inc(v_snd_793_);
lean_dec(v_a_791_);
v_fst_625_ = v_fst_792_;
v_snd_626_ = v_snd_793_;
goto v___jp_624_;
}
else
{
lean_object* v_a_794_; 
v_a_794_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_790_, 1);
v_a_635_ = v_a_794_;
goto v___jp_634_;
}
}
else
{
lean_object* v_a_795_; 
v_a_795_ = lean_ctor_get(v___x_783_, 0);
lean_inc(v_a_795_);
lean_dec_ref_known(v___x_783_, 1);
v_a_635_ = v_a_795_;
goto v___jp_634_;
}
}
else
{
lean_object* v_a_796_; uint8_t v___y_798_; uint8_t v___x_821_; 
v_a_796_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_781_, 1);
v___x_821_ = l_Lean_Exception_isInterrupt(v_a_796_);
if (v___x_821_ == 0)
{
uint8_t v___x_822_; 
lean_inc(v_a_796_);
v___x_822_ = l_Lean_Exception_isRuntime(v_a_796_);
v___y_798_ = v___x_822_;
goto v___jp_797_;
}
else
{
v___y_798_ = v___x_821_;
goto v___jp_797_;
}
v___jp_797_:
{
if (v___y_798_ == 0)
{
lean_object* v_fileName_799_; lean_object* v_fileMap_800_; lean_object* v_options_801_; lean_object* v_currRecDepth_802_; lean_object* v_maxRecDepth_803_; lean_object* v_ref_804_; lean_object* v_currNamespace_805_; lean_object* v_openDecls_806_; lean_object* v_initHeartbeats_807_; lean_object* v_maxHeartbeats_808_; lean_object* v_quotContext_809_; lean_object* v_currMacroScope_810_; uint8_t v_diag_811_; lean_object* v_cancelTk_x3f_812_; uint8_t v_suppressElabErrors_813_; lean_object* v_inheritedTraceOptions_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v_ref_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
lean_dec(v_a_796_);
v_fileName_799_ = lean_ctor_get(v___y_561_, 0);
v_fileMap_800_ = lean_ctor_get(v___y_561_, 1);
v_options_801_ = lean_ctor_get(v___y_561_, 2);
v_currRecDepth_802_ = lean_ctor_get(v___y_561_, 3);
v_maxRecDepth_803_ = lean_ctor_get(v___y_561_, 4);
v_ref_804_ = lean_ctor_get(v___y_561_, 5);
v_currNamespace_805_ = lean_ctor_get(v___y_561_, 6);
v_openDecls_806_ = lean_ctor_get(v___y_561_, 7);
v_initHeartbeats_807_ = lean_ctor_get(v___y_561_, 8);
v_maxHeartbeats_808_ = lean_ctor_get(v___y_561_, 9);
v_quotContext_809_ = lean_ctor_get(v___y_561_, 10);
v_currMacroScope_810_ = lean_ctor_get(v___y_561_, 11);
v_diag_811_ = lean_ctor_get_uint8(v___y_561_, sizeof(void*)*14);
v_cancelTk_x3f_812_ = lean_ctor_get(v___y_561_, 12);
v_suppressElabErrors_813_ = lean_ctor_get_uint8(v___y_561_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_814_ = lean_ctor_get(v___y_561_, 13);
v___x_815_ = l_Lean_Syntax_getId(v___x_767_);
v___x_816_ = lean_erase_macro_scopes(v___x_815_);
v_ref_817_ = l_Lean_replaceRef(v___x_767_, v_ref_804_);
lean_dec(v___x_767_);
lean_inc_ref(v_inheritedTraceOptions_814_);
lean_inc(v_cancelTk_x3f_812_);
lean_inc(v_currMacroScope_810_);
lean_inc(v_quotContext_809_);
lean_inc(v_maxHeartbeats_808_);
lean_inc(v_initHeartbeats_807_);
lean_inc(v_openDecls_806_);
lean_inc(v_currNamespace_805_);
lean_inc(v_maxRecDepth_803_);
lean_inc(v_currRecDepth_802_);
lean_inc_ref(v_options_801_);
lean_inc_ref(v_fileMap_800_);
lean_inc_ref(v_fileName_799_);
v___x_818_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_818_, 0, v_fileName_799_);
lean_ctor_set(v___x_818_, 1, v_fileMap_800_);
lean_ctor_set(v___x_818_, 2, v_options_801_);
lean_ctor_set(v___x_818_, 3, v_currRecDepth_802_);
lean_ctor_set(v___x_818_, 4, v_maxRecDepth_803_);
lean_ctor_set(v___x_818_, 5, v_ref_817_);
lean_ctor_set(v___x_818_, 6, v_currNamespace_805_);
lean_ctor_set(v___x_818_, 7, v_openDecls_806_);
lean_ctor_set(v___x_818_, 8, v_initHeartbeats_807_);
lean_ctor_set(v___x_818_, 9, v_maxHeartbeats_808_);
lean_ctor_set(v___x_818_, 10, v_quotContext_809_);
lean_ctor_set(v___x_818_, 11, v_currMacroScope_810_);
lean_ctor_set(v___x_818_, 12, v_cancelTk_x3f_812_);
lean_ctor_set(v___x_818_, 13, v_inheritedTraceOptions_814_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*14, v_diag_811_);
lean_ctor_set_uint8(v___x_818_, sizeof(void*)*14 + 1, v_suppressElabErrors_813_);
v___x_819_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___redArg(v___x_816_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___x_818_, v___y_562_);
lean_dec_ref_known(v___x_818_, 14);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_dec_ref_known(v___x_819_, 1);
v_fst_620_ = v_fst_572_;
goto v___jp_619_;
}
else
{
lean_object* v_a_820_; 
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref_known(v___x_819_, 1);
v_a_635_ = v_a_820_;
goto v___jp_634_;
}
}
else
{
lean_dec(v___x_767_);
v_a_635_ = v_a_796_;
goto v___jp_634_;
}
}
}
}
}
else
{
lean_object* v_a_823_; 
lean_dec(v___x_767_);
v_a_823_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_823_);
lean_dec_ref_known(v___x_768_, 1);
v_a_635_ = v_a_823_;
goto v___jp_634_;
}
}
v___jp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v_snd_583_);
v___x_585_ = v___x_579_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_snd_583_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_snd_577_);
v___x_585_ = v_reuseFailAlloc_589_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_587_; 
if (v_isShared_575_ == 0)
{
lean_ctor_set(v___x_574_, 1, v___x_585_);
lean_ctor_set(v___x_574_, 0, v_fst_582_);
v___x_587_ = v___x_574_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_fst_582_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
v_a_565_ = v___x_587_;
goto v___jp_564_;
}
}
}
v___jp_590_:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_snd_592_);
lean_ctor_set(v___x_593_, 1, v_snd_577_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_fst_591_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v_a_565_ = v___x_594_;
goto v___jp_564_;
}
v___jp_597_:
{
if (v___y_599_ == 0)
{
lean_object* v___x_600_; 
lean_dec_ref(v___y_598_);
lean_inc(v_a_596_);
v___x_600_ = lean_array_push(v_fst_576_, v_a_596_);
v_fst_591_ = v_fst_572_;
v_snd_592_ = v___x_600_;
goto v___jp_590_;
}
else
{
lean_object* v___x_601_; 
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
lean_dec(v_fst_572_);
v___x_601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_601_, 0, v___y_598_);
return v___x_601_;
}
}
v___jp_602_:
{
uint8_t v___x_604_; 
v___x_604_ = l_Lean_Exception_isInterrupt(v_a_603_);
if (v___x_604_ == 0)
{
uint8_t v___x_605_; 
lean_inc_ref(v_a_603_);
v___x_605_ = l_Lean_Exception_isRuntime(v_a_603_);
v___y_598_ = v_a_603_;
v___y_599_ = v___x_605_;
goto v___jp_597_;
}
else
{
v___y_598_ = v_a_603_;
v___y_599_ = v___x_604_;
goto v___jp_597_;
}
}
v___jp_606_:
{
if (v___y_608_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v___y_607_);
lean_inc(v_a_596_);
v___x_609_ = lean_array_push(v_fst_576_, v_a_596_);
v_fst_582_ = v_fst_572_;
v_snd_583_ = v___x_609_;
goto v___jp_581_;
}
else
{
lean_object* v___x_610_; 
lean_del_object(v___x_579_);
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
lean_del_object(v___x_574_);
lean_dec(v_fst_572_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___y_607_);
return v___x_610_;
}
}
v___jp_611_:
{
uint8_t v___x_613_; 
v___x_613_ = l_Lean_Exception_isInterrupt(v_a_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; 
lean_inc_ref(v_a_612_);
v___x_614_ = l_Lean_Exception_isRuntime(v_a_612_);
v___y_607_ = v_a_612_;
v___y_608_ = v___x_614_;
goto v___jp_606_;
}
else
{
v___y_607_ = v_a_612_;
v___y_608_ = v___x_613_;
goto v___jp_606_;
}
}
v___jp_615_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_inc(v_a_596_);
v___x_616_ = lean_array_push(v_fst_576_, v_a_596_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v_snd_577_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_fst_572_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
v_a_565_ = v___x_618_;
goto v___jp_564_;
}
v___jp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_inc(v_a_596_);
v___x_621_ = lean_array_push(v_fst_576_, v_a_596_);
v___x_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_snd_577_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v_fst_620_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
v_a_565_ = v___x_623_;
goto v___jp_564_;
}
v___jp_624_:
{
uint8_t v___x_627_; 
v___x_627_ = lean_unbox(v_snd_626_);
lean_dec(v_snd_626_);
if (v___x_627_ == 0)
{
v_fst_620_ = v_fst_625_;
goto v___jp_619_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v_fst_576_);
lean_ctor_set(v___x_628_, 1, v_snd_577_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_fst_625_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v_a_565_ = v___x_629_;
goto v___jp_564_;
}
}
v___jp_630_:
{
if (v___y_632_ == 0)
{
lean_dec_ref(v___y_631_);
v_fst_620_ = v_fst_572_;
goto v___jp_619_;
}
else
{
lean_object* v___x_633_; 
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
lean_dec(v_fst_572_);
v___x_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_633_, 0, v___y_631_);
return v___x_633_;
}
}
v___jp_634_:
{
uint8_t v___x_636_; 
v___x_636_ = l_Lean_Exception_isInterrupt(v_a_635_);
if (v___x_636_ == 0)
{
uint8_t v___x_637_; 
lean_inc_ref(v_a_635_);
v___x_637_ = l_Lean_Exception_isRuntime(v_a_635_);
v___y_631_ = v_a_635_;
v___y_632_ = v___x_637_;
goto v___jp_630_;
}
else
{
v___y_631_ = v_a_635_;
v___y_632_ = v___x_636_;
goto v___jp_630_;
}
}
}
}
}
v___jp_564_:
{
size_t v___x_566_; size_t v___x_567_; 
v___x_566_ = ((size_t)1ULL);
v___x_567_ = lean_usize_add(v_i_555_, v___x_566_);
v_i_555_ = v___x_567_;
v_b_556_ = v_a_565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___boxed(lean_object* v_as_826_, lean_object* v_sz_827_, lean_object* v_i_828_, lean_object* v_b_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_){
_start:
{
size_t v_sz_boxed_837_; size_t v_i_boxed_838_; lean_object* v_res_839_; 
v_sz_boxed_837_ = lean_unbox_usize(v_sz_827_);
lean_dec(v_sz_827_);
v_i_boxed_838_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_res_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4(v_as_826_, v_sz_boxed_837_, v_i_boxed_838_, v_b_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec_ref(v_as_826_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7___redArg(lean_object* v_as_840_, size_t v_sz_841_, size_t v_i_842_, lean_object* v_b_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v_a_850_; uint8_t v___x_854_; 
v___x_854_ = lean_usize_dec_lt(v_i_842_, v_sz_841_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v_b_843_);
return v___x_855_;
}
else
{
lean_object* v_a_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v_a_856_ = lean_array_uget_borrowed(v_as_840_, v_i_842_);
lean_inc(v_a_856_);
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v_a_856_);
lean_inc_ref(v_b_843_);
v___x_858_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_isErased(v_b_843_, v___x_857_);
if (v___x_858_ == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_unsigned_to_nat(1000u);
lean_inc(v_a_856_);
v___x_860_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(v_a_856_, v___x_859_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
if (lean_obj_tag(v_a_861_) == 1)
{
lean_object* v_val_862_; lean_object* v___x_863_; 
v_val_862_ = lean_ctor_get(v_a_861_, 0);
lean_inc(v_val_862_);
lean_dec_ref_known(v_a_861_, 1);
v___x_863_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert(v_b_843_, v_val_862_);
v_a_850_ = v___x_863_;
goto v___jp_849_;
}
else
{
lean_dec(v_a_861_);
v_a_850_ = v_b_843_;
goto v___jp_849_;
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_875_; 
v_a_864_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_875_ == 0)
{
v___x_866_ = v___x_860_;
v_isShared_867_ = v_isSharedCheck_875_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_860_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_875_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
uint8_t v___y_869_; uint8_t v___x_873_; 
v___x_873_ = l_Lean_Exception_isInterrupt(v_a_864_);
if (v___x_873_ == 0)
{
uint8_t v___x_874_; 
lean_inc(v_a_864_);
v___x_874_ = l_Lean_Exception_isRuntime(v_a_864_);
v___y_869_ = v___x_874_;
goto v___jp_868_;
}
else
{
v___y_869_ = v___x_873_;
goto v___jp_868_;
}
v___jp_868_:
{
if (v___y_869_ == 0)
{
lean_del_object(v___x_866_);
lean_dec(v_a_864_);
v_a_850_ = v_b_843_;
goto v___jp_849_;
}
else
{
lean_object* v___x_871_; 
lean_dec_ref(v_b_843_);
if (v_isShared_867_ == 0)
{
v___x_871_ = v___x_866_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_864_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
}
else
{
v_a_850_ = v_b_843_;
goto v___jp_849_;
}
}
v___jp_849_:
{
size_t v___x_851_; size_t v___x_852_; 
v___x_851_ = ((size_t)1ULL);
v___x_852_ = lean_usize_add(v_i_842_, v___x_851_);
v_i_842_ = v___x_852_;
v_b_843_ = v_a_850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7___redArg___boxed(lean_object* v_as_876_, lean_object* v_sz_877_, lean_object* v_i_878_, lean_object* v_b_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
size_t v_sz_boxed_885_; size_t v_i_boxed_886_; lean_object* v_res_887_; 
v_sz_boxed_885_ = lean_unbox_usize(v_sz_877_);
lean_dec(v_sz_877_);
v_i_boxed_886_ = lean_unbox_usize(v_i_878_);
lean_dec(v_i_878_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7___redArg(v_as_876_, v_sz_boxed_885_, v_i_boxed_886_, v_b_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec_ref(v_as_876_);
return v_res_887_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_box(0);
v___x_891_ = lean_unsigned_to_nat(16u);
v___x_892_ = lean_mk_array(v___x_891_, v___x_890_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__1);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
lean_ctor_set(v___x_895_, 1, v___x_893_);
return v___x_895_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__16(void){
_start:
{
lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_929_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__15));
v___x_930_ = l_String_toRawSubstring_x27(v___x_929_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22(void){
_start:
{
lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_941_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__21));
v___x_942_ = l_String_toRawSubstring_x27(v___x_941_);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24(void){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l_Array_mkArray0(lean_box(0));
return v___x_945_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__28(void){
_start:
{
lean_object* v___x_949_; 
v___x_949_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_949_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29(void){
_start:
{
lean_object* v___x_950_; 
v___x_950_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__5(lean_box(0));
return v___x_950_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__30(void){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__6(lean_box(0));
return v___x_951_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31(void){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_952_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__32(void){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__31);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_955_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__32, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__32_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__32);
v___x_956_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__30, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__30_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__30);
v___x_957_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__29);
v___x_958_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__28, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__28_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__28);
v___x_959_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
lean_ctor_set(v___x_959_, 2, v___x_957_);
lean_ctor_set(v___x_959_, 3, v___x_956_);
lean_ctor_set(v___x_959_, 4, v___x_957_);
lean_ctor_set(v___x_959_, 5, v___x_955_);
return v___x_959_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__34(void){
_start:
{
lean_object* v___x_960_; lean_object* v___f_961_; 
v___x_960_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33);
v___f_961_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___lam__0___boxed), 4, 1);
lean_closure_set(v___f_961_, 0, v___x_960_);
return v___f_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext(lean_object* v_lemmas_962_, lean_object* v_goal_963_, uint8_t v_ignoreStarArg_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_getSpecTheorems___redArg(v_a_970_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_974_; uint8_t v___x_975_; lean_object* v___y_977_; lean_object* v_specThms_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; size_t v_sz_1022_; size_t v___x_1023_; lean_object* v___x_1024_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref_known(v___x_972_, 1);
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = 0;
v___x_1017_ = lean_unsigned_to_nat(1u);
v___x_1018_ = l_Lean_Syntax_getArg(v_lemmas_962_, v___x_1017_);
v___x_1019_ = l_Lean_Syntax_getSepArgs(v___x_1018_);
lean_dec(v___x_1018_);
v___x_1020_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__3));
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v_a_973_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v_sz_1022_ = lean_array_size(v___x_1019_);
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4(v___x_1019_, v_sz_1022_, v___x_1023_, v___x_1021_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
lean_dec_ref(v___x_1019_);
if (lean_obj_tag(v___x_1024_) == 0)
{
lean_object* v_a_1025_; lean_object* v_snd_1026_; lean_object* v_fst_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1131_; 
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_a_1025_);
lean_dec_ref_known(v___x_1024_, 1);
v_snd_1026_ = lean_ctor_get(v_a_1025_, 1);
v_fst_1027_ = lean_ctor_get(v_a_1025_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_a_1025_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1029_ = v_a_1025_;
v_isShared_1030_ = v_isSharedCheck_1131_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_snd_1026_);
lean_inc(v_fst_1027_);
lean_dec(v_a_1025_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1131_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1130_; 
v_fst_1031_ = lean_ctor_get(v_snd_1026_, 0);
v_snd_1032_ = lean_ctor_get(v_snd_1026_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_snd_1026_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1034_ = v_snd_1026_;
v_isShared_1035_ = v_isSharedCheck_1130_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_snd_1032_);
lean_inc(v_fst_1031_);
lean_dec(v_snd_1026_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1130_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v_ref_1036_; lean_object* v_quotContext_1037_; lean_object* v_currMacroScope_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1043_; 
v_ref_1036_ = lean_ctor_get(v_a_969_, 5);
v_quotContext_1037_ = lean_ctor_get(v_a_969_, 10);
v_currMacroScope_1038_ = lean_ctor_get(v_a_969_, 11);
v___x_1039_ = l_Lean_SourceInfo_fromRef(v_ref_1036_, v___x_975_);
v___x_1040_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__4));
v___x_1041_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__5));
lean_inc(v___x_1039_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set_tag(v___x_1034_, 2);
lean_ctor_set(v___x_1034_, 1, v___x_1040_);
lean_ctor_set(v___x_1034_, 0, v___x_1039_);
v___x_1043_ = v___x_1034_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v___x_1040_);
v___x_1043_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
v___x_1044_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__7));
v___x_1045_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9));
v___x_1046_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__11));
v___x_1047_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__13));
v___x_1048_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__14));
lean_inc(v___x_1039_);
if (v_isShared_1030_ == 0)
{
lean_ctor_set_tag(v___x_1029_, 2);
lean_ctor_set(v___x_1029_, 1, v___x_1048_);
lean_ctor_set(v___x_1029_, 0, v___x_1039_);
v___x_1050_ = v___x_1029_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v___x_1048_);
v___x_1050_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___f_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1051_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__16, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__16_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__16);
v___x_1052_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__17));
lean_inc_n(v_currMacroScope_1038_, 2);
lean_inc_n(v_quotContext_1037_, 2);
v___x_1053_ = l_Lean_addMacroScope(v_quotContext_1037_, v___x_1052_, v_currMacroScope_1038_);
v___x_1054_ = lean_box(0);
lean_inc_n(v___x_1039_, 14);
v___x_1055_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1039_);
lean_ctor_set(v___x_1055_, 1, v___x_1051_);
lean_ctor_set(v___x_1055_, 2, v___x_1053_);
lean_ctor_set(v___x_1055_, 3, v___x_1054_);
v___x_1056_ = l_Lean_Syntax_node2(v___x_1039_, v___x_1047_, v___x_1050_, v___x_1055_);
v___x_1057_ = l_Lean_Syntax_node1(v___x_1039_, v___x_1046_, v___x_1056_);
v___x_1058_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__19));
v___x_1059_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__20));
v___x_1060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1039_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__22);
v___x_1062_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__23));
v___x_1063_ = l_Lean_addMacroScope(v_quotContext_1037_, v___x_1062_, v_currMacroScope_1038_);
v___x_1064_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1039_);
lean_ctor_set(v___x_1064_, 1, v___x_1061_);
lean_ctor_set(v___x_1064_, 2, v___x_1063_);
lean_ctor_set(v___x_1064_, 3, v___x_1054_);
v___x_1065_ = l_Lean_Syntax_node2(v___x_1039_, v___x_1058_, v___x_1060_, v___x_1064_);
v___x_1066_ = l_Lean_Syntax_node1(v___x_1039_, v___x_1046_, v___x_1065_);
v___x_1067_ = l_Lean_Syntax_node2(v___x_1039_, v___x_1045_, v___x_1057_, v___x_1066_);
v___x_1068_ = l_Lean_Syntax_node1(v___x_1039_, v___x_1044_, v___x_1067_);
v___x_1069_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24);
v___x_1070_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1039_);
lean_ctor_set(v___x_1070_, 1, v___x_1045_);
lean_ctor_set(v___x_1070_, 2, v___x_1069_);
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25));
v___x_1072_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1039_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__26));
v___x_1074_ = l_Lean_Syntax_SepArray_ofElems(v___x_1073_, v_fst_1031_);
lean_dec(v_fst_1031_);
v___x_1075_ = l_Array_append___redArg(v___x_1069_, v___x_1074_);
lean_dec_ref(v___x_1074_);
v___x_1076_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1039_);
lean_ctor_set(v___x_1076_, 1, v___x_1045_);
lean_ctor_set(v___x_1076_, 2, v___x_1075_);
v___x_1077_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27));
v___x_1078_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1039_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = l_Lean_Syntax_node3(v___x_1039_, v___x_1045_, v___x_1072_, v___x_1076_, v___x_1078_);
lean_inc_ref_n(v___x_1070_, 2);
v___x_1080_ = l_Lean_Syntax_node6(v___x_1039_, v___x_1041_, v___x_1043_, v___x_1068_, v___x_1070_, v___x_1070_, v___x_1079_, v___x_1070_);
v___x_1081_ = 0;
v___x_1082_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__33);
v___f_1083_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__34, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__34_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__34);
v___x_1084_ = lean_box(v___x_975_);
v___x_1085_ = lean_box(v___x_1081_);
v___x_1086_ = lean_box(v_ignoreStarArg_964_);
v___x_1087_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_1087_, 0, v___x_1080_);
lean_closure_set(v___x_1087_, 1, v___x_1084_);
lean_closure_set(v___x_1087_, 2, v___x_1085_);
lean_closure_set(v___x_1087_, 3, v___x_1086_);
lean_closure_set(v___x_1087_, 4, v___f_1083_);
v___x_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1088_, 0, v_goal_963_);
lean_ctor_set(v___x_1088_, 1, v___x_1054_);
v___x_1089_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg(v___x_1087_, v___x_1088_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___y_1092_; lean_object* v_ctx_1115_; lean_object* v_simpTheorems_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v_ctx_1115_ = lean_ctor_get(v_a_1090_, 0);
lean_inc_ref(v_ctx_1115_);
lean_dec(v_a_1090_);
v_simpTheorems_1116_ = lean_ctor_get(v_ctx_1115_, 6);
lean_inc_ref(v_simpTheorems_1116_);
lean_dec_ref(v_ctx_1115_);
v___x_1117_ = lean_array_get_size(v_simpTheorems_1116_);
v___x_1118_ = lean_nat_dec_lt(v___x_974_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_dec_ref(v_simpTheorems_1116_);
v___y_1092_ = v___x_1082_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_array_fget(v_simpTheorems_1116_, v___x_974_);
lean_dec_ref(v_simpTheorems_1116_);
v___y_1092_ = v___x_1119_;
goto v___jp_1091_;
}
v___jp_1091_:
{
uint8_t v___x_1093_; 
v___x_1093_ = lean_unbox(v_snd_1032_);
lean_dec(v_snd_1032_);
if (v___x_1093_ == 0)
{
v___y_977_ = v___y_1092_;
v_specThms_978_ = v_fst_1027_;
v___y_979_ = v_a_967_;
v___y_980_ = v_a_968_;
v___y_981_ = v_a_969_;
v___y_982_ = v_a_970_;
goto v___jp_976_;
}
else
{
if (v_ignoreStarArg_964_ == 0)
{
lean_object* v___x_1094_; 
v___x_1094_ = l_Lean_Meta_getPropHyps(v_a_967_, v_a_968_, v_a_969_, v_a_970_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; size_t v_sz_1096_; lean_object* v___x_1097_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
lean_inc(v_a_1095_);
lean_dec_ref_known(v___x_1094_, 1);
v_sz_1096_ = lean_array_size(v_a_1095_);
v___x_1097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7___redArg(v_a_1095_, v_sz_1096_, v___x_1023_, v_fst_1027_, v_a_967_, v_a_968_, v_a_969_, v_a_970_);
lean_dec(v_a_1095_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___y_977_ = v___y_1092_;
v_specThms_978_ = v_a_1098_;
v___y_979_ = v_a_967_;
v___y_980_ = v_a_968_;
v___y_981_ = v_a_969_;
v___y_982_ = v_a_970_;
goto v___jp_976_;
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v___y_1092_);
v_a_1099_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1097_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v___y_1092_);
lean_dec(v_fst_1027_);
v_a_1107_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1094_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1094_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
v___y_977_ = v___y_1092_;
v_specThms_978_ = v_fst_1027_;
v___y_979_ = v_a_967_;
v___y_980_ = v_a_968_;
v___y_981_ = v_a_969_;
v___y_982_ = v_a_970_;
goto v___jp_976_;
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_snd_1032_);
lean_dec(v_fst_1027_);
v_a_1120_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1089_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1089_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
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
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec(v_goal_963_);
v_a_1132_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1024_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1024_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
v___jp_976_:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules(v___y_979_, v___y_980_, v___y_981_, v___y_982_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v___x_985_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v___x_985_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_extendWithSimpSpecs(v_specThms_978_, v___y_977_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
lean_dec_ref(v___y_977_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v_a_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1000_; 
v_a_986_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_988_ = v___x_985_;
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_a_986_);
lean_dec(v___x_985_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1000_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___x_990_; uint8_t v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_990_ = lean_box(0);
v___x_991_ = 1;
v___x_992_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2);
v___x_993_ = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(v___x_993_, 0, v_a_984_);
lean_ctor_set(v___x_993_, 1, v___x_990_);
lean_ctor_set(v___x_993_, 2, v___x_992_);
lean_ctor_set(v___x_993_, 3, v___x_990_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*4, v___x_991_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*4 + 1, v___x_975_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*4 + 2, v___x_991_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*4 + 3, v___x_975_);
lean_ctor_set_uint8(v___x_993_, sizeof(void*)*4 + 4, v___x_991_);
v___x_994_ = lean_box(1);
v___x_995_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_995_, 0, v_a_986_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
lean_ctor_set(v___x_995_, 2, v___x_990_);
lean_ctor_set(v___x_995_, 3, v___x_974_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_993_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 0, v___x_996_);
v___x_998_ = v___x_988_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec(v_a_984_);
v_a_1001_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_985_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_985_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
lean_dec_ref(v_specThms_978_);
lean_dec_ref(v___y_977_);
v_a_1009_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_983_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_983_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec(v_goal_963_);
v_a_1140_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_972_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_972_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___boxed(lean_object* v_lemmas_1148_, lean_object* v_goal_1149_, lean_object* v_ignoreStarArg_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
uint8_t v_ignoreStarArg_boxed_1158_; lean_object* v_res_1159_; 
v_ignoreStarArg_boxed_1158_ = lean_unbox(v_ignoreStarArg_1150_);
v_res_1159_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext(v_lemmas_1148_, v_goal_1149_, v_ignoreStarArg_boxed_1158_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_lemmas_1148_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1(lean_object* v_00_u03b1_1160_, lean_object* v_msg_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___redArg(v_msg_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1___boxed(lean_object* v_00_u03b1_1170_, lean_object* v_msg_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1(v_00_u03b1_1170_, v_msg_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v___y_1175_);
lean_dec_ref(v___y_1174_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2(lean_object* v_as_1180_, size_t v_sz_1181_, size_t v_i_1182_, lean_object* v_b_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___redArg(v_as_1180_, v_sz_1181_, v_i_1182_, v_b_1183_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2___boxed(lean_object* v_as_1192_, lean_object* v_sz_1193_, lean_object* v_i_1194_, lean_object* v_b_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
size_t v_sz_boxed_1203_; size_t v_i_boxed_1204_; lean_object* v_res_1205_; 
v_sz_boxed_1203_ = lean_unbox_usize(v_sz_1193_);
lean_dec(v_sz_1193_);
v_i_boxed_1204_ = lean_unbox_usize(v_i_1194_);
lean_dec(v_i_1194_);
v_res_1205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__2(v_as_1192_, v_sz_boxed_1203_, v_i_boxed_1204_, v_b_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec_ref(v_as_1192_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3(lean_object* v_00_u03b1_1206_, lean_object* v_constName_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___redArg(v_constName_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3___boxed(lean_object* v_00_u03b1_1216_, lean_object* v_constName_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3(v_00_u03b1_1216_, v_constName_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7(lean_object* v_as_1226_, size_t v_sz_1227_, size_t v_i_1228_, lean_object* v_b_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7___redArg(v_as_1226_, v_sz_1227_, v_i_1228_, v_b_1229_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7___boxed(lean_object* v_as_1238_, lean_object* v_sz_1239_, lean_object* v_i_1240_, lean_object* v_b_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
size_t v_sz_boxed_1249_; size_t v_i_boxed_1250_; lean_object* v_res_1251_; 
v_sz_boxed_1249_ = lean_unbox_usize(v_sz_1239_);
lean_dec(v_sz_1239_);
v_i_boxed_1250_ = lean_unbox_usize(v_i_1240_);
lean_dec(v_i_1240_);
v_res_1251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__7(v_as_1238_, v_sz_boxed_1249_, v_i_boxed_1250_, v_b_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec_ref(v_as_1238_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2(lean_object* v_msgData_1252_, lean_object* v_macroStack_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___redArg(v_msgData_1252_, v_macroStack_1253_, v___y_1258_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2___boxed(lean_object* v_msgData_1262_, lean_object* v_macroStack_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2(v_msgData_1262_, v_macroStack_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_);
lean_dec(v___y_1269_);
lean_dec_ref(v___y_1268_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5(lean_object* v_00_u03b1_1272_, lean_object* v_ref_1273_, lean_object* v_constName_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v___x_1282_; 
v___x_1282_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___redArg(v_ref_1273_, v_constName_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1283_, lean_object* v_ref_1284_, lean_object* v_constName_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5(v_00_u03b1_1283_, v_ref_1284_, v_constName_1285_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v_ref_1284_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10(lean_object* v_00_u03b1_1294_, lean_object* v_ref_1295_, lean_object* v_msg_1296_, lean_object* v_declHint_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10___redArg(v_ref_1295_, v_msg_1296_, v_declHint_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_ref_1307_, lean_object* v_msg_1308_, lean_object* v_declHint_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10(v_00_u03b1_1306_, v_ref_1307_, v_msg_1308_, v_declHint_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v_ref_1307_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14(lean_object* v_msg_1318_, lean_object* v_declHint_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg(v_msg_1318_, v_declHint_1319_, v___y_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___boxed(lean_object* v_msg_1328_, lean_object* v_declHint_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14(v_msg_1328_, v_declHint_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14(lean_object* v_00_u03b1_1338_, lean_object* v_ref_1339_, lean_object* v_msg_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(v_ref_1339_, v_msg_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___boxed(lean_object* v_00_u03b1_1349_, lean_object* v_ref_1350_, lean_object* v_msg_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14(v_00_u03b1_1349_, v_ref_1350_, v_msg_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v_ref_1350_);
return v_res_1359_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0(uint8_t v___y_1367_, uint8_t v_suppressElabErrors_1368_, lean_object* v_x_1369_){
_start:
{
if (lean_obj_tag(v_x_1369_) == 1)
{
lean_object* v_pre_1370_; 
v_pre_1370_ = lean_ctor_get(v_x_1369_, 0);
switch(lean_obj_tag(v_pre_1370_))
{
case 1:
{
lean_object* v_pre_1371_; 
v_pre_1371_ = lean_ctor_get(v_pre_1370_, 0);
switch(lean_obj_tag(v_pre_1371_))
{
case 0:
{
lean_object* v_str_1372_; lean_object* v_str_1373_; lean_object* v___x_1374_; uint8_t v___x_1375_; 
v_str_1372_ = lean_ctor_get(v_x_1369_, 1);
v_str_1373_ = lean_ctor_get(v_pre_1370_, 1);
v___x_1374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__0));
v___x_1375_ = lean_string_dec_eq(v_str_1373_, v___x_1374_);
if (v___x_1375_ == 0)
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2));
v___x_1377_ = lean_string_dec_eq(v_str_1373_, v___x_1376_);
if (v___x_1377_ == 0)
{
return v___y_1367_;
}
else
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__1));
v___x_1379_ = lean_string_dec_eq(v_str_1372_, v___x_1378_);
if (v___x_1379_ == 0)
{
return v___y_1367_;
}
else
{
return v_suppressElabErrors_1368_;
}
}
}
else
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__2));
v___x_1381_ = lean_string_dec_eq(v_str_1372_, v___x_1380_);
if (v___x_1381_ == 0)
{
return v___y_1367_;
}
else
{
return v_suppressElabErrors_1368_;
}
}
}
case 1:
{
lean_object* v_pre_1382_; 
v_pre_1382_ = lean_ctor_get(v_pre_1371_, 0);
if (lean_obj_tag(v_pre_1382_) == 0)
{
lean_object* v_str_1383_; lean_object* v_str_1384_; lean_object* v_str_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v_str_1383_ = lean_ctor_get(v_x_1369_, 1);
v_str_1384_ = lean_ctor_get(v_pre_1370_, 1);
v_str_1385_ = lean_ctor_get(v_pre_1371_, 1);
v___x_1386_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__3));
v___x_1387_ = lean_string_dec_eq(v_str_1385_, v___x_1386_);
if (v___x_1387_ == 0)
{
return v___y_1367_;
}
else
{
lean_object* v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__4));
v___x_1389_ = lean_string_dec_eq(v_str_1384_, v___x_1388_);
if (v___x_1389_ == 0)
{
return v___y_1367_;
}
else
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__5));
v___x_1391_ = lean_string_dec_eq(v_str_1383_, v___x_1390_);
if (v___x_1391_ == 0)
{
return v___y_1367_;
}
else
{
return v_suppressElabErrors_1368_;
}
}
}
}
else
{
return v___y_1367_;
}
}
default: 
{
return v___y_1367_;
}
}
}
case 0:
{
lean_object* v_str_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_str_1392_ = lean_ctor_get(v_x_1369_, 1);
v___x_1393_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___closed__6));
v___x_1394_ = lean_string_dec_eq(v_str_1392_, v___x_1393_);
if (v___x_1394_ == 0)
{
return v___y_1367_;
}
else
{
return v_suppressElabErrors_1368_;
}
}
default: 
{
return v___y_1367_;
}
}
}
else
{
return v___y_1367_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v___y_1395_, lean_object* v_suppressElabErrors_1396_, lean_object* v_x_1397_){
_start:
{
uint8_t v___y_2865__boxed_1398_; uint8_t v_suppressElabErrors_boxed_1399_; uint8_t v_res_1400_; lean_object* v_r_1401_; 
v___y_2865__boxed_1398_ = lean_unbox(v___y_1395_);
v_suppressElabErrors_boxed_1399_ = lean_unbox(v_suppressElabErrors_1396_);
v_res_1400_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0(v___y_2865__boxed_1398_, v_suppressElabErrors_boxed_1399_, v_x_1397_);
lean_dec(v_x_1397_);
v_r_1401_ = lean_box(v_res_1400_);
return v_r_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1(lean_object* v_ref_1403_, lean_object* v_msgData_1404_, uint8_t v_severity_1405_, uint8_t v_isSilent_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; uint8_t v___y_1416_; uint8_t v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1449_; lean_object* v___y_1450_; uint8_t v___y_1451_; lean_object* v___y_1452_; uint8_t v___y_1453_; uint8_t v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; uint8_t v___y_1477_; uint8_t v___y_1478_; uint8_t v___y_1479_; lean_object* v___y_1480_; lean_object* v___y_1481_; lean_object* v___y_1485_; lean_object* v___y_1486_; uint8_t v___y_1487_; uint8_t v___y_1488_; lean_object* v___y_1489_; lean_object* v___y_1490_; uint8_t v___y_1491_; uint8_t v___x_1496_; lean_object* v___y_1498_; lean_object* v___y_1499_; lean_object* v___y_1500_; uint8_t v___y_1501_; lean_object* v___y_1502_; uint8_t v___y_1503_; uint8_t v___y_1504_; uint8_t v___y_1506_; uint8_t v___x_1521_; 
v___x_1496_ = 2;
v___x_1521_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1405_, v___x_1496_);
if (v___x_1521_ == 0)
{
v___y_1506_ = v___x_1521_;
goto v___jp_1505_;
}
else
{
uint8_t v___x_1522_; 
lean_inc_ref(v_msgData_1404_);
v___x_1522_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1404_);
v___y_1506_ = v___x_1522_;
goto v___jp_1505_;
}
v___jp_1412_:
{
lean_object* v___x_1422_; lean_object* v_currNamespace_1423_; lean_object* v_openDecls_1424_; lean_object* v_env_1425_; lean_object* v_nextMacroScope_1426_; lean_object* v_ngen_1427_; lean_object* v_auxDeclNGen_1428_; lean_object* v_traceState_1429_; lean_object* v_cache_1430_; lean_object* v_messages_1431_; lean_object* v_infoState_1432_; lean_object* v_snapshotTasks_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1447_; 
v___x_1422_ = lean_st_ref_take(v___y_1421_);
v_currNamespace_1423_ = lean_ctor_get(v___y_1420_, 6);
v_openDecls_1424_ = lean_ctor_get(v___y_1420_, 7);
v_env_1425_ = lean_ctor_get(v___x_1422_, 0);
v_nextMacroScope_1426_ = lean_ctor_get(v___x_1422_, 1);
v_ngen_1427_ = lean_ctor_get(v___x_1422_, 2);
v_auxDeclNGen_1428_ = lean_ctor_get(v___x_1422_, 3);
v_traceState_1429_ = lean_ctor_get(v___x_1422_, 4);
v_cache_1430_ = lean_ctor_get(v___x_1422_, 5);
v_messages_1431_ = lean_ctor_get(v___x_1422_, 6);
v_infoState_1432_ = lean_ctor_get(v___x_1422_, 7);
v_snapshotTasks_1433_ = lean_ctor_get(v___x_1422_, 8);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1435_ = v___x_1422_;
v_isShared_1436_ = v_isSharedCheck_1447_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_snapshotTasks_1433_);
lean_inc(v_infoState_1432_);
lean_inc(v_messages_1431_);
lean_inc(v_cache_1430_);
lean_inc(v_traceState_1429_);
lean_inc(v_auxDeclNGen_1428_);
lean_inc(v_ngen_1427_);
lean_inc(v_nextMacroScope_1426_);
lean_inc(v_env_1425_);
lean_dec(v___x_1422_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1447_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
lean_inc(v_openDecls_1424_);
lean_inc(v_currNamespace_1423_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_currNamespace_1423_);
lean_ctor_set(v___x_1437_, 1, v_openDecls_1424_);
v___x_1438_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v___y_1419_);
lean_inc_ref(v___y_1413_);
lean_inc_ref(v___y_1415_);
v___x_1439_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1439_, 0, v___y_1415_);
lean_ctor_set(v___x_1439_, 1, v___y_1414_);
lean_ctor_set(v___x_1439_, 2, v___y_1418_);
lean_ctor_set(v___x_1439_, 3, v___y_1413_);
lean_ctor_set(v___x_1439_, 4, v___x_1438_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*5, v___y_1416_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*5 + 1, v___y_1417_);
lean_ctor_set_uint8(v___x_1439_, sizeof(void*)*5 + 2, v_isSilent_1406_);
v___x_1440_ = l_Lean_MessageLog_add(v___x_1439_, v_messages_1431_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 6, v___x_1440_);
v___x_1442_ = v___x_1435_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_env_1425_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_nextMacroScope_1426_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_ngen_1427_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v_auxDeclNGen_1428_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_traceState_1429_);
lean_ctor_set(v_reuseFailAlloc_1446_, 5, v_cache_1430_);
lean_ctor_set(v_reuseFailAlloc_1446_, 6, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1446_, 7, v_infoState_1432_);
lean_ctor_set(v_reuseFailAlloc_1446_, 8, v_snapshotTasks_1433_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_st_ref_set(v___y_1421_, v___x_1442_);
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
return v___x_1445_;
}
}
}
v___jp_1448_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1472_; 
v___x_1457_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1404_);
v___x_1458_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v___x_1457_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1472_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1472_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
lean_inc_ref_n(v___y_1455_, 2);
v___x_1463_ = l_Lean_FileMap_toPosition(v___y_1455_, v___y_1452_);
lean_dec(v___y_1452_);
v___x_1464_ = l_Lean_FileMap_toPosition(v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
v___x_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1465_, 0, v___x_1464_);
v___x_1466_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___closed__0));
if (v___y_1453_ == 0)
{
lean_del_object(v___x_1461_);
lean_dec_ref(v___y_1449_);
v___y_1413_ = v___x_1466_;
v___y_1414_ = v___x_1463_;
v___y_1415_ = v___y_1450_;
v___y_1416_ = v___y_1451_;
v___y_1417_ = v___y_1454_;
v___y_1418_ = v___x_1465_;
v___y_1419_ = v_a_1459_;
v___y_1420_ = v___y_1409_;
v___y_1421_ = v___y_1410_;
goto v___jp_1412_;
}
else
{
uint8_t v___x_1467_; 
lean_inc(v_a_1459_);
v___x_1467_ = l_Lean_MessageData_hasTag(v___y_1449_, v_a_1459_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
lean_dec_ref_known(v___x_1465_, 1);
lean_dec_ref(v___x_1463_);
lean_dec(v_a_1459_);
v___x_1468_ = lean_box(0);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1468_);
v___x_1470_ = v___x_1461_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
else
{
lean_del_object(v___x_1461_);
v___y_1413_ = v___x_1466_;
v___y_1414_ = v___x_1463_;
v___y_1415_ = v___y_1450_;
v___y_1416_ = v___y_1451_;
v___y_1417_ = v___y_1454_;
v___y_1418_ = v___x_1465_;
v___y_1419_ = v_a_1459_;
v___y_1420_ = v___y_1409_;
v___y_1421_ = v___y_1410_;
goto v___jp_1412_;
}
}
}
}
v___jp_1473_:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Lean_Syntax_getTailPos_x3f(v___y_1476_, v___y_1477_);
lean_dec(v___y_1476_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_inc(v___y_1481_);
v___y_1449_ = v___y_1474_;
v___y_1450_ = v___y_1475_;
v___y_1451_ = v___y_1477_;
v___y_1452_ = v___y_1481_;
v___y_1453_ = v___y_1478_;
v___y_1454_ = v___y_1479_;
v___y_1455_ = v___y_1480_;
v___y_1456_ = v___y_1481_;
goto v___jp_1448_;
}
else
{
lean_object* v_val_1483_; 
v_val_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_val_1483_);
lean_dec_ref_known(v___x_1482_, 1);
v___y_1449_ = v___y_1474_;
v___y_1450_ = v___y_1475_;
v___y_1451_ = v___y_1477_;
v___y_1452_ = v___y_1481_;
v___y_1453_ = v___y_1478_;
v___y_1454_ = v___y_1479_;
v___y_1455_ = v___y_1480_;
v___y_1456_ = v_val_1483_;
goto v___jp_1448_;
}
}
v___jp_1484_:
{
lean_object* v_ref_1492_; lean_object* v___x_1493_; 
v_ref_1492_ = l_Lean_replaceRef(v_ref_1403_, v___y_1489_);
v___x_1493_ = l_Lean_Syntax_getPos_x3f(v_ref_1492_, v___y_1487_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v___x_1494_; 
v___x_1494_ = lean_unsigned_to_nat(0u);
v___y_1474_ = v___y_1485_;
v___y_1475_ = v___y_1486_;
v___y_1476_ = v_ref_1492_;
v___y_1477_ = v___y_1487_;
v___y_1478_ = v___y_1488_;
v___y_1479_ = v___y_1491_;
v___y_1480_ = v___y_1490_;
v___y_1481_ = v___x_1494_;
goto v___jp_1473_;
}
else
{
lean_object* v_val_1495_; 
v_val_1495_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_val_1495_);
lean_dec_ref_known(v___x_1493_, 1);
v___y_1474_ = v___y_1485_;
v___y_1475_ = v___y_1486_;
v___y_1476_ = v_ref_1492_;
v___y_1477_ = v___y_1487_;
v___y_1478_ = v___y_1488_;
v___y_1479_ = v___y_1491_;
v___y_1480_ = v___y_1490_;
v___y_1481_ = v_val_1495_;
goto v___jp_1473_;
}
}
v___jp_1497_:
{
if (v___y_1504_ == 0)
{
v___y_1485_ = v___y_1499_;
v___y_1486_ = v___y_1498_;
v___y_1487_ = v___y_1503_;
v___y_1488_ = v___y_1501_;
v___y_1489_ = v___y_1500_;
v___y_1490_ = v___y_1502_;
v___y_1491_ = v_severity_1405_;
goto v___jp_1484_;
}
else
{
v___y_1485_ = v___y_1499_;
v___y_1486_ = v___y_1498_;
v___y_1487_ = v___y_1503_;
v___y_1488_ = v___y_1501_;
v___y_1489_ = v___y_1500_;
v___y_1490_ = v___y_1502_;
v___y_1491_ = v___x_1496_;
goto v___jp_1484_;
}
}
v___jp_1505_:
{
if (v___y_1506_ == 0)
{
lean_object* v_fileName_1507_; lean_object* v_fileMap_1508_; lean_object* v_options_1509_; lean_object* v_ref_1510_; uint8_t v_suppressElabErrors_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___f_1514_; uint8_t v___x_1515_; uint8_t v___x_1516_; 
v_fileName_1507_ = lean_ctor_get(v___y_1409_, 0);
v_fileMap_1508_ = lean_ctor_get(v___y_1409_, 1);
v_options_1509_ = lean_ctor_get(v___y_1409_, 2);
v_ref_1510_ = lean_ctor_get(v___y_1409_, 5);
v_suppressElabErrors_1511_ = lean_ctor_get_uint8(v___y_1409_, sizeof(void*)*14 + 1);
v___x_1512_ = lean_box(v___y_1506_);
v___x_1513_ = lean_box(v_suppressElabErrors_1511_);
v___f_1514_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1514_, 0, v___x_1512_);
lean_closure_set(v___f_1514_, 1, v___x_1513_);
v___x_1515_ = 1;
v___x_1516_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1405_, v___x_1515_);
if (v___x_1516_ == 0)
{
v___y_1498_ = v_fileName_1507_;
v___y_1499_ = v___f_1514_;
v___y_1500_ = v_ref_1510_;
v___y_1501_ = v_suppressElabErrors_1511_;
v___y_1502_ = v_fileMap_1508_;
v___y_1503_ = v___y_1506_;
v___y_1504_ = v___x_1516_;
goto v___jp_1497_;
}
else
{
lean_object* v___x_1517_; uint8_t v___x_1518_; 
v___x_1517_ = l_Lean_warningAsError;
v___x_1518_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_options_1509_, v___x_1517_);
v___y_1498_ = v_fileName_1507_;
v___y_1499_ = v___f_1514_;
v___y_1500_ = v_ref_1510_;
v___y_1501_ = v_suppressElabErrors_1511_;
v___y_1502_ = v_fileMap_1508_;
v___y_1503_ = v___y_1506_;
v___y_1504_ = v___x_1518_;
goto v___jp_1497_;
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec_ref(v_msgData_1404_);
v___x_1519_ = lean_box(0);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_ref_1523_, lean_object* v_msgData_1524_, lean_object* v_severity_1525_, lean_object* v_isSilent_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
uint8_t v_severity_boxed_1532_; uint8_t v_isSilent_boxed_1533_; lean_object* v_res_1534_; 
v_severity_boxed_1532_ = lean_unbox(v_severity_1525_);
v_isSilent_boxed_1533_ = lean_unbox(v_isSilent_1526_);
v_res_1534_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1(v_ref_1523_, v_msgData_1524_, v_severity_boxed_1532_, v_isSilent_boxed_1533_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v_ref_1523_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0(lean_object* v_msgData_1535_, uint8_t v_severity_1536_, uint8_t v_isSilent_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v_ref_1543_; lean_object* v___x_1544_; 
v_ref_1543_ = lean_ctor_get(v___y_1540_, 5);
v___x_1544_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1(v_ref_1543_, v_msgData_1535_, v_severity_1536_, v_isSilent_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0___boxed(lean_object* v_msgData_1545_, lean_object* v_severity_1546_, lean_object* v_isSilent_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
uint8_t v_severity_boxed_1553_; uint8_t v_isSilent_boxed_1554_; lean_object* v_res_1555_; 
v_severity_boxed_1553_ = lean_unbox(v_severity_1546_);
v_isSilent_boxed_1554_ = lean_unbox(v_isSilent_1547_);
v_res_1555_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0(v_msgData_1545_, v_severity_boxed_1553_, v_isSilent_boxed_1554_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0(lean_object* v_msgData_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v___x_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; 
v___x_1562_ = 1;
v___x_1563_ = 0;
v___x_1564_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0(v_msgData_1556_, v___x_1562_, v___x_1563_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
return v___x_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0___boxed(lean_object* v_msgData_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0(v_msgData_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
return v_res_1571_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__1));
v___x_1576_ = l_Lean_MessageData_ofFormat(v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig(lean_object* v_config_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_){
_start:
{
uint8_t v_leave_1583_; 
v_leave_1583_ = lean_ctor_get_uint8(v_config_1577_, sizeof(void*)*1 + 1);
if (v_leave_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1584_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___closed__2);
v___x_1585_ = l_Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0(v___x_1584_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig___boxed(lean_object* v_config_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig(v_config_1588_, v_a_1589_, v_a_1590_, v_a_1591_, v_a_1592_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
lean_dec(v_a_1590_);
lean_dec_ref(v_a_1589_);
lean_dec_ref(v_config_1588_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0(lean_object* v_x_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0___closed__0));
v___x_1609_ = l_Lean_Meta_Sym_Simp_simpArrowTelescope(v___x_1608_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0___boxed(lean_object* v_x_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__0(v_x_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec(v___y_1612_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__1(lean_object* v___f_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v___x_1635_; 
lean_inc_ref(v___y_1624_);
v___x_1635_ = l_Lean_Meta_Sym_Simp_simpControl(v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1637_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
lean_inc(v_a_1636_);
v___x_1637_ = lean_box(0);
if (lean_obj_tag(v_a_1636_) == 0)
{
uint8_t v_done_1638_; 
v_done_1638_ = lean_ctor_get_uint8(v_a_1636_, 0);
if (v_done_1638_ == 0)
{
uint8_t v_contextDependent_1639_; lean_object* v___x_1640_; 
lean_dec_ref_known(v___x_1635_, 1);
v_contextDependent_1639_ = lean_ctor_get_uint8(v_a_1636_, 1);
lean_dec_ref_known(v_a_1636_, 0);
v___x_1640_ = lean_apply_12(v___f_1623_, v___x_1637_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, lean_box(0));
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_object* v_a_1641_; uint8_t v___y_1643_; 
v_a_1641_ = lean_ctor_get(v___x_1640_, 0);
lean_inc(v_a_1641_);
if (v_contextDependent_1639_ == 0)
{
lean_dec(v_a_1641_);
return v___x_1640_;
}
else
{
if (lean_obj_tag(v_a_1641_) == 0)
{
uint8_t v_contextDependent_1653_; 
v_contextDependent_1653_ = lean_ctor_get_uint8(v_a_1641_, 1);
v___y_1643_ = v_contextDependent_1653_;
goto v___jp_1642_;
}
else
{
uint8_t v_contextDependent_1654_; 
v_contextDependent_1654_ = lean_ctor_get_uint8(v_a_1641_, sizeof(void*)*2 + 1);
v___y_1643_ = v_contextDependent_1654_;
goto v___jp_1642_;
}
}
v___jp_1642_:
{
if (v___y_1643_ == 0)
{
lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1651_; 
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; 
v_unused_1652_ = lean_ctor_get(v___x_1640_, 0);
lean_dec(v_unused_1652_);
v___x_1645_ = v___x_1640_;
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
else
{
lean_dec(v___x_1640_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1651_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v___x_1649_; 
v___x_1647_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1641_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1647_);
v___x_1649_ = v___x_1645_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
lean_dec(v_a_1641_);
return v___x_1640_;
}
}
}
else
{
return v___x_1640_;
}
}
else
{
lean_dec_ref_known(v_a_1636_, 0);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___f_1623_);
return v___x_1635_;
}
}
else
{
uint8_t v_done_1655_; 
v_done_1655_ = lean_ctor_get_uint8(v_a_1636_, sizeof(void*)*2);
if (v_done_1655_ == 0)
{
lean_object* v_e_x27_1656_; lean_object* v_proof_1657_; uint8_t v_contextDependent_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1708_; 
lean_dec_ref_known(v___x_1635_, 1);
v_e_x27_1656_ = lean_ctor_get(v_a_1636_, 0);
v_proof_1657_ = lean_ctor_get(v_a_1636_, 1);
v_contextDependent_1658_ = lean_ctor_get_uint8(v_a_1636_, sizeof(void*)*2 + 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_a_1636_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1660_ = v_a_1636_;
v_isShared_1661_ = v_isSharedCheck_1708_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_proof_1657_);
lean_inc(v_e_x27_1656_);
lean_dec(v_a_1636_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1708_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; 
lean_inc(v___y_1633_);
lean_inc_ref(v___y_1632_);
lean_inc(v___y_1631_);
lean_inc_ref(v___y_1630_);
lean_inc(v___y_1629_);
lean_inc_ref(v_e_x27_1656_);
v___x_1662_ = lean_apply_12(v___f_1623_, v___x_1637_, v_e_x27_1656_, v___y_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_, lean_box(0));
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1707_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1707_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1707_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1707_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
if (lean_obj_tag(v_a_1663_) == 0)
{
uint8_t v_done_1667_; uint8_t v_contextDependent_1668_; uint8_t v___y_1670_; 
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1624_);
v_done_1667_ = lean_ctor_get_uint8(v_a_1663_, 0);
v_contextDependent_1668_ = lean_ctor_get_uint8(v_a_1663_, 1);
lean_dec_ref_known(v_a_1663_, 0);
if (v_contextDependent_1658_ == 0)
{
v___y_1670_ = v_contextDependent_1668_;
goto v___jp_1669_;
}
else
{
v___y_1670_ = v_contextDependent_1658_;
goto v___jp_1669_;
}
v___jp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1661_ == 0)
{
v___x_1672_ = v___x_1660_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_e_x27_1656_);
lean_ctor_set(v_reuseFailAlloc_1676_, 1, v_proof_1657_);
v___x_1672_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
lean_object* v___x_1674_; 
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*2, v_done_1667_);
lean_ctor_set_uint8(v___x_1672_, sizeof(void*)*2 + 1, v___y_1670_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1672_);
v___x_1674_ = v___x_1665_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_object* v_e_x27_1677_; lean_object* v_proof_1678_; uint8_t v_done_1679_; uint8_t v_contextDependent_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1706_; 
lean_del_object(v___x_1665_);
lean_del_object(v___x_1660_);
v_e_x27_1677_ = lean_ctor_get(v_a_1663_, 0);
v_proof_1678_ = lean_ctor_get(v_a_1663_, 1);
v_done_1679_ = lean_ctor_get_uint8(v_a_1663_, sizeof(void*)*2);
v_contextDependent_1680_ = lean_ctor_get_uint8(v_a_1663_, sizeof(void*)*2 + 1);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_a_1663_);
if (v_isSharedCheck_1706_ == 0)
{
v___x_1682_ = v_a_1663_;
v_isShared_1683_ = v_isSharedCheck_1706_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_proof_1678_);
lean_inc(v_e_x27_1677_);
lean_dec(v_a_1663_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1706_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; 
lean_inc_ref(v_e_x27_1677_);
v___x_1684_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_1624_, v_e_x27_1656_, v_proof_1657_, v_e_x27_1677_, v_proof_1678_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1697_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1687_ = v___x_1684_;
v_isShared_1688_ = v_isSharedCheck_1697_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1684_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1697_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
uint8_t v___y_1690_; 
if (v_contextDependent_1658_ == 0)
{
v___y_1690_ = v_contextDependent_1680_;
goto v___jp_1689_;
}
else
{
v___y_1690_ = v_contextDependent_1658_;
goto v___jp_1689_;
}
v___jp_1689_:
{
lean_object* v___x_1692_; 
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 1, v_a_1685_);
v___x_1692_ = v___x_1682_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_e_x27_1677_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_a_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1696_, sizeof(void*)*2, v_done_1679_);
v___x_1692_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1694_; 
lean_ctor_set_uint8(v___x_1692_, sizeof(void*)*2 + 1, v___y_1690_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 0, v___x_1692_);
v___x_1694_ = v___x_1687_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v___x_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_del_object(v___x_1682_);
lean_dec_ref(v_e_x27_1677_);
v_a_1698_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1684_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1684_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1660_);
lean_dec_ref(v_proof_1657_);
lean_dec_ref(v_e_x27_1656_);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1624_);
return v___x_1662_;
}
}
}
else
{
lean_dec_ref_known(v_a_1636_, 2);
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___f_1623_);
return v___x_1635_;
}
}
}
else
{
lean_dec(v___y_1633_);
lean_dec_ref(v___y_1632_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___f_1623_);
return v___x_1635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__1___boxed(lean_object* v___f_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__1(v___f_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2(lean_object* v_a_1723_, lean_object* v_x_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___closed__0));
v___x_1737_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_1723_, v___x_1736_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___boxed(lean_object* v_a_1738_, lean_object* v_x_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2(v_a_1738_, v_x_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_, v___y_1749_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec(v___y_1747_);
lean_dec_ref(v___y_1746_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v_a_1738_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__4(lean_object* v___f_1752_, lean_object* v___x_1753_, lean_object* v___f_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
uint8_t v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; uint8_t v___y_1770_; uint8_t v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; uint8_t v___y_1777_; lean_object* v___y_1781_; lean_object* v_e_x27_1782_; lean_object* v_proof_1783_; uint8_t v_done_1784_; uint8_t v_contextDependent_1785_; lean_object* v___y_1808_; lean_object* v___y_1809_; uint8_t v___y_1810_; lean_object* v___y_1814_; lean_object* v_a_1815_; lean_object* v___y_1828_; lean_object* v___x_1830_; 
lean_inc_ref(v___y_1755_);
v___x_1830_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_1753_, v___y_1755_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v___x_1832_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
v___x_1832_ = lean_box(0);
if (lean_obj_tag(v_a_1831_) == 0)
{
uint8_t v_done_1833_; 
v_done_1833_ = lean_ctor_get_uint8(v_a_1831_, 0);
if (v_done_1833_ == 0)
{
uint8_t v_contextDependent_1834_; lean_object* v___x_1835_; 
lean_dec_ref_known(v___x_1830_, 1);
v_contextDependent_1834_ = lean_ctor_get_uint8(v_a_1831_, 1);
lean_dec_ref_known(v_a_1831_, 0);
lean_inc(v___y_1764_);
lean_inc_ref(v___y_1763_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1761_);
lean_inc(v___y_1760_);
lean_inc_ref(v___y_1759_);
lean_inc(v___y_1758_);
lean_inc_ref(v___y_1757_);
lean_inc(v___y_1756_);
lean_inc_ref(v___y_1755_);
v___x_1835_ = lean_apply_12(v___f_1754_, v___x_1832_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, lean_box(0));
if (lean_obj_tag(v___x_1835_) == 0)
{
lean_object* v_a_1836_; uint8_t v___y_1838_; 
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
lean_inc(v_a_1836_);
if (v_contextDependent_1834_ == 0)
{
v___y_1814_ = v___x_1835_;
v_a_1815_ = v_a_1836_;
goto v___jp_1813_;
}
else
{
if (lean_obj_tag(v_a_1836_) == 0)
{
uint8_t v_contextDependent_1848_; 
v_contextDependent_1848_ = lean_ctor_get_uint8(v_a_1836_, 1);
v___y_1838_ = v_contextDependent_1848_;
goto v___jp_1837_;
}
else
{
uint8_t v_contextDependent_1849_; 
v_contextDependent_1849_ = lean_ctor_get_uint8(v_a_1836_, sizeof(void*)*2 + 1);
v___y_1838_ = v_contextDependent_1849_;
goto v___jp_1837_;
}
}
v___jp_1837_:
{
if (v___y_1838_ == 0)
{
lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1846_; 
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1846_ == 0)
{
lean_object* v_unused_1847_; 
v_unused_1847_ = lean_ctor_get(v___x_1835_, 0);
lean_dec(v_unused_1847_);
v___x_1840_ = v___x_1835_;
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
else
{
lean_dec(v___x_1835_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1846_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1836_);
lean_inc_ref(v___x_1842_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 0, v___x_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
v___y_1814_ = v___x_1844_;
v_a_1815_ = v___x_1842_;
goto v___jp_1813_;
}
}
}
else
{
v___y_1814_ = v___x_1835_;
v_a_1815_ = v_a_1836_;
goto v___jp_1813_;
}
}
}
else
{
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v___f_1752_);
return v___x_1835_;
}
}
else
{
lean_dec_ref_known(v_a_1831_, 0);
lean_dec_ref(v___f_1754_);
v___y_1828_ = v___x_1830_;
goto v___jp_1827_;
}
}
else
{
uint8_t v_done_1850_; 
v_done_1850_ = lean_ctor_get_uint8(v_a_1831_, sizeof(void*)*2);
if (v_done_1850_ == 0)
{
lean_object* v_e_x27_1851_; lean_object* v_proof_1852_; uint8_t v_contextDependent_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1903_; 
lean_dec_ref_known(v___x_1830_, 1);
v_e_x27_1851_ = lean_ctor_get(v_a_1831_, 0);
v_proof_1852_ = lean_ctor_get(v_a_1831_, 1);
v_contextDependent_1853_ = lean_ctor_get_uint8(v_a_1831_, sizeof(void*)*2 + 1);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_a_1831_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1855_ = v_a_1831_;
v_isShared_1856_ = v_isSharedCheck_1903_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_proof_1852_);
lean_inc(v_e_x27_1851_);
lean_dec(v_a_1831_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1903_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1857_; 
lean_inc(v___y_1764_);
lean_inc_ref(v___y_1763_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1761_);
lean_inc(v___y_1760_);
lean_inc_ref(v___y_1759_);
lean_inc(v___y_1758_);
lean_inc_ref(v___y_1757_);
lean_inc(v___y_1756_);
lean_inc_ref(v_e_x27_1851_);
v___x_1857_ = lean_apply_12(v___f_1754_, v___x_1832_, v_e_x27_1851_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, lean_box(0));
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1902_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1902_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1902_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
if (lean_obj_tag(v_a_1858_) == 0)
{
uint8_t v_done_1862_; uint8_t v_contextDependent_1863_; uint8_t v___y_1865_; 
v_done_1862_ = lean_ctor_get_uint8(v_a_1858_, 0);
v_contextDependent_1863_ = lean_ctor_get_uint8(v_a_1858_, 1);
lean_dec_ref_known(v_a_1858_, 0);
if (v_contextDependent_1853_ == 0)
{
v___y_1865_ = v_contextDependent_1863_;
goto v___jp_1864_;
}
else
{
v___y_1865_ = v_contextDependent_1853_;
goto v___jp_1864_;
}
v___jp_1864_:
{
lean_object* v___x_1867_; 
lean_inc_ref(v_proof_1852_);
lean_inc_ref(v_e_x27_1851_);
if (v_isShared_1856_ == 0)
{
v___x_1867_ = v___x_1855_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_e_x27_1851_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v_proof_1852_);
v___x_1867_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
lean_object* v___x_1869_; 
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*2, v_done_1862_);
lean_ctor_set_uint8(v___x_1867_, sizeof(void*)*2 + 1, v___y_1865_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1867_);
v___x_1869_ = v___x_1860_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
v___y_1781_ = v___x_1869_;
v_e_x27_1782_ = v_e_x27_1851_;
v_proof_1783_ = v_proof_1852_;
v_done_1784_ = v_done_1862_;
v_contextDependent_1785_ = v___y_1865_;
goto v___jp_1780_;
}
}
}
}
else
{
lean_object* v_e_x27_1872_; lean_object* v_proof_1873_; uint8_t v_done_1874_; uint8_t v_contextDependent_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1901_; 
lean_del_object(v___x_1860_);
lean_del_object(v___x_1855_);
v_e_x27_1872_ = lean_ctor_get(v_a_1858_, 0);
v_proof_1873_ = lean_ctor_get(v_a_1858_, 1);
v_done_1874_ = lean_ctor_get_uint8(v_a_1858_, sizeof(void*)*2);
v_contextDependent_1875_ = lean_ctor_get_uint8(v_a_1858_, sizeof(void*)*2 + 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_a_1858_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1877_ = v_a_1858_;
v_isShared_1878_ = v_isSharedCheck_1901_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_proof_1873_);
lean_inc(v_e_x27_1872_);
lean_dec(v_a_1858_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1901_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; 
lean_inc_ref(v_e_x27_1872_);
lean_inc_ref(v___y_1755_);
v___x_1879_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_1755_, v_e_x27_1851_, v_proof_1852_, v_e_x27_1872_, v_proof_1873_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1892_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1882_ = v___x_1879_;
v_isShared_1883_ = v_isSharedCheck_1892_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1879_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1892_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
uint8_t v___y_1885_; 
if (v_contextDependent_1853_ == 0)
{
v___y_1885_ = v_contextDependent_1875_;
goto v___jp_1884_;
}
else
{
v___y_1885_ = v_contextDependent_1853_;
goto v___jp_1884_;
}
v___jp_1884_:
{
lean_object* v___x_1887_; 
lean_inc(v_a_1880_);
lean_inc_ref(v_e_x27_1872_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 1, v_a_1880_);
v___x_1887_ = v___x_1877_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_e_x27_1872_);
lean_ctor_set(v_reuseFailAlloc_1891_, 1, v_a_1880_);
lean_ctor_set_uint8(v_reuseFailAlloc_1891_, sizeof(void*)*2, v_done_1874_);
v___x_1887_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
lean_object* v___x_1889_; 
lean_ctor_set_uint8(v___x_1887_, sizeof(void*)*2 + 1, v___y_1885_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 0, v___x_1887_);
v___x_1889_ = v___x_1882_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v___x_1887_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
v___y_1781_ = v___x_1889_;
v_e_x27_1782_ = v_e_x27_1872_;
v_proof_1783_ = v_a_1880_;
v_done_1784_ = v_done_1874_;
v_contextDependent_1785_ = v___y_1885_;
goto v___jp_1780_;
}
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_del_object(v___x_1877_);
lean_dec_ref(v_e_x27_1872_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v___f_1752_);
v_a_1893_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1879_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1879_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1855_);
lean_dec_ref(v_proof_1852_);
lean_dec_ref(v_e_x27_1851_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v___f_1752_);
return v___x_1857_;
}
}
}
else
{
lean_dec_ref_known(v_a_1831_, 2);
lean_dec_ref(v___f_1754_);
v___y_1828_ = v___x_1830_;
goto v___jp_1827_;
}
}
}
else
{
lean_dec_ref(v___f_1754_);
v___y_1828_ = v___x_1830_;
goto v___jp_1827_;
}
v___jp_1766_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1771_, 0, v___y_1768_);
lean_ctor_set(v___x_1771_, 1, v___y_1769_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*2, v___y_1767_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*2 + 1, v___y_1770_);
v___x_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1771_);
return v___x_1772_;
}
v___jp_1773_:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1778_, 0, v___y_1776_);
lean_ctor_set(v___x_1778_, 1, v___y_1775_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*2, v___y_1774_);
lean_ctor_set_uint8(v___x_1778_, sizeof(void*)*2 + 1, v___y_1777_);
v___x_1779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1778_);
return v___x_1779_;
}
v___jp_1780_:
{
if (v_done_1784_ == 0)
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_dec_ref(v___y_1781_);
v___x_1786_ = lean_box(0);
lean_inc(v___y_1764_);
lean_inc_ref(v___y_1763_);
lean_inc(v___y_1762_);
lean_inc_ref(v___y_1761_);
lean_inc(v___y_1760_);
lean_inc_ref(v_e_x27_1782_);
v___x_1787_ = lean_apply_12(v___f_1752_, v___x_1786_, v_e_x27_1782_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, lean_box(0));
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_a_1788_);
lean_dec_ref_known(v___x_1787_, 1);
if (lean_obj_tag(v_a_1788_) == 0)
{
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1755_);
if (v_contextDependent_1785_ == 0)
{
uint8_t v_done_1789_; uint8_t v_contextDependent_1790_; 
v_done_1789_ = lean_ctor_get_uint8(v_a_1788_, 0);
v_contextDependent_1790_ = lean_ctor_get_uint8(v_a_1788_, 1);
lean_dec_ref_known(v_a_1788_, 0);
v___y_1767_ = v_done_1789_;
v___y_1768_ = v_e_x27_1782_;
v___y_1769_ = v_proof_1783_;
v___y_1770_ = v_contextDependent_1790_;
goto v___jp_1766_;
}
else
{
uint8_t v_done_1791_; 
v_done_1791_ = lean_ctor_get_uint8(v_a_1788_, 0);
lean_dec_ref_known(v_a_1788_, 0);
v___y_1767_ = v_done_1791_;
v___y_1768_ = v_e_x27_1782_;
v___y_1769_ = v_proof_1783_;
v___y_1770_ = v_contextDependent_1785_;
goto v___jp_1766_;
}
}
else
{
lean_object* v_e_x27_1792_; lean_object* v_proof_1793_; uint8_t v_done_1794_; uint8_t v_contextDependent_1795_; lean_object* v___x_1796_; 
v_e_x27_1792_ = lean_ctor_get(v_a_1788_, 0);
lean_inc_ref_n(v_e_x27_1792_, 2);
v_proof_1793_ = lean_ctor_get(v_a_1788_, 1);
lean_inc_ref(v_proof_1793_);
v_done_1794_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*2);
v_contextDependent_1795_ = lean_ctor_get_uint8(v_a_1788_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1788_, 2);
v___x_1796_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_1755_, v_e_x27_1782_, v_proof_1783_, v_e_x27_1792_, v_proof_1793_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
if (lean_obj_tag(v___x_1796_) == 0)
{
if (v_contextDependent_1785_ == 0)
{
lean_object* v_a_1797_; 
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1797_);
lean_dec_ref_known(v___x_1796_, 1);
v___y_1774_ = v_done_1794_;
v___y_1775_ = v_a_1797_;
v___y_1776_ = v_e_x27_1792_;
v___y_1777_ = v_contextDependent_1795_;
goto v___jp_1773_;
}
else
{
lean_object* v_a_1798_; 
v_a_1798_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_a_1798_);
lean_dec_ref_known(v___x_1796_, 1);
v___y_1774_ = v_done_1794_;
v___y_1775_ = v_a_1798_;
v___y_1776_ = v_e_x27_1792_;
v___y_1777_ = v_contextDependent_1785_;
goto v___jp_1773_;
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec_ref(v_e_x27_1792_);
v_a_1799_ = lean_ctor_get(v___x_1796_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1796_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1796_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1796_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
else
{
lean_dec_ref(v_proof_1783_);
lean_dec_ref(v_e_x27_1782_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1755_);
return v___x_1787_;
}
}
else
{
lean_dec_ref(v_proof_1783_);
lean_dec_ref(v_e_x27_1782_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v___f_1752_);
return v___y_1781_;
}
}
v___jp_1807_:
{
if (v___y_1810_ == 0)
{
lean_object* v___x_1811_; lean_object* v___x_1812_; 
lean_dec_ref(v___y_1809_);
v___x_1811_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1808_);
v___x_1812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1812_, 0, v___x_1811_);
return v___x_1812_;
}
else
{
lean_dec_ref(v___y_1808_);
return v___y_1809_;
}
}
v___jp_1813_:
{
if (lean_obj_tag(v_a_1815_) == 0)
{
uint8_t v_done_1816_; 
v_done_1816_ = lean_ctor_get_uint8(v_a_1815_, 0);
if (v_done_1816_ == 0)
{
uint8_t v_contextDependent_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec_ref(v___y_1814_);
v_contextDependent_1817_ = lean_ctor_get_uint8(v_a_1815_, 1);
lean_dec_ref_known(v_a_1815_, 0);
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_apply_12(v___f_1752_, v___x_1818_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, lean_box(0));
if (lean_obj_tag(v___x_1819_) == 0)
{
if (v_contextDependent_1817_ == 0)
{
return v___x_1819_;
}
else
{
lean_object* v_a_1820_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
if (lean_obj_tag(v_a_1820_) == 0)
{
uint8_t v_contextDependent_1821_; 
v_contextDependent_1821_ = lean_ctor_get_uint8(v_a_1820_, 1);
v___y_1808_ = v_a_1820_;
v___y_1809_ = v___x_1819_;
v___y_1810_ = v_contextDependent_1821_;
goto v___jp_1807_;
}
else
{
uint8_t v_contextDependent_1822_; 
v_contextDependent_1822_ = lean_ctor_get_uint8(v_a_1820_, sizeof(void*)*2 + 1);
v___y_1808_ = v_a_1820_;
v___y_1809_ = v___x_1819_;
v___y_1810_ = v_contextDependent_1822_;
goto v___jp_1807_;
}
}
}
else
{
return v___x_1819_;
}
}
else
{
lean_dec_ref_known(v_a_1815_, 0);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v___f_1752_);
return v___y_1814_;
}
}
else
{
lean_object* v_e_x27_1823_; lean_object* v_proof_1824_; uint8_t v_done_1825_; uint8_t v_contextDependent_1826_; 
v_e_x27_1823_ = lean_ctor_get(v_a_1815_, 0);
lean_inc_ref(v_e_x27_1823_);
v_proof_1824_ = lean_ctor_get(v_a_1815_, 1);
lean_inc_ref(v_proof_1824_);
v_done_1825_ = lean_ctor_get_uint8(v_a_1815_, sizeof(void*)*2);
v_contextDependent_1826_ = lean_ctor_get_uint8(v_a_1815_, sizeof(void*)*2 + 1);
lean_dec_ref_known(v_a_1815_, 2);
v___y_1781_ = v___y_1814_;
v_e_x27_1782_ = v_e_x27_1823_;
v_proof_1783_ = v_proof_1824_;
v_done_1784_ = v_done_1825_;
v_contextDependent_1785_ = v_contextDependent_1826_;
goto v___jp_1780_;
}
}
v___jp_1827_:
{
if (lean_obj_tag(v___y_1828_) == 0)
{
lean_object* v_a_1829_; 
v_a_1829_ = lean_ctor_get(v___y_1828_, 0);
lean_inc(v_a_1829_);
v___y_1814_ = v___y_1828_;
v_a_1815_ = v_a_1829_;
goto v___jp_1813_;
}
else
{
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec_ref(v___f_1752_);
return v___y_1828_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__4___boxed(lean_object* v___f_1904_, lean_object* v___x_1905_, lean_object* v___f_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__4(v___f_1904_, v___x_1905_, v___f_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_);
lean_dec(v___x_1905_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__3(lean_object* v___x_1919_, lean_object* v___f_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___x_1932_; 
lean_inc_ref(v___y_1921_);
v___x_1932_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_1919_, v___y_1921_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
v___x_1934_ = lean_box(0);
if (lean_obj_tag(v_a_1933_) == 0)
{
uint8_t v_done_1935_; 
v_done_1935_ = lean_ctor_get_uint8(v_a_1933_, 0);
if (v_done_1935_ == 0)
{
uint8_t v_contextDependent_1936_; lean_object* v___x_1937_; 
lean_dec_ref_known(v___x_1932_, 1);
v_contextDependent_1936_ = lean_ctor_get_uint8(v_a_1933_, 1);
lean_dec_ref_known(v_a_1933_, 0);
v___x_1937_ = lean_apply_12(v___f_1920_, v___x_1934_, v___y_1921_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, lean_box(0));
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; uint8_t v___y_1940_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
if (v_contextDependent_1936_ == 0)
{
lean_dec(v_a_1938_);
return v___x_1937_;
}
else
{
if (lean_obj_tag(v_a_1938_) == 0)
{
uint8_t v_contextDependent_1950_; 
v_contextDependent_1950_ = lean_ctor_get_uint8(v_a_1938_, 1);
v___y_1940_ = v_contextDependent_1950_;
goto v___jp_1939_;
}
else
{
uint8_t v_contextDependent_1951_; 
v_contextDependent_1951_ = lean_ctor_get_uint8(v_a_1938_, sizeof(void*)*2 + 1);
v___y_1940_ = v_contextDependent_1951_;
goto v___jp_1939_;
}
}
v___jp_1939_:
{
if (v___y_1940_ == 0)
{
lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1948_; 
v_isSharedCheck_1948_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1948_ == 0)
{
lean_object* v_unused_1949_; 
v_unused_1949_ = lean_ctor_get(v___x_1937_, 0);
lean_dec(v_unused_1949_);
v___x_1942_ = v___x_1937_;
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
else
{
lean_dec(v___x_1937_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1948_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1944_; lean_object* v___x_1946_; 
v___x_1944_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1938_);
if (v_isShared_1943_ == 0)
{
lean_ctor_set(v___x_1942_, 0, v___x_1944_);
v___x_1946_ = v___x_1942_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
else
{
lean_dec(v_a_1938_);
return v___x_1937_;
}
}
}
else
{
return v___x_1937_;
}
}
else
{
lean_dec_ref_known(v_a_1933_, 0);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec_ref(v___f_1920_);
return v___x_1932_;
}
}
else
{
uint8_t v_done_1952_; 
v_done_1952_ = lean_ctor_get_uint8(v_a_1933_, sizeof(void*)*2);
if (v_done_1952_ == 0)
{
lean_object* v_e_x27_1953_; lean_object* v_proof_1954_; uint8_t v_contextDependent_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2005_; 
lean_dec_ref_known(v___x_1932_, 1);
v_e_x27_1953_ = lean_ctor_get(v_a_1933_, 0);
v_proof_1954_ = lean_ctor_get(v_a_1933_, 1);
v_contextDependent_1955_ = lean_ctor_get_uint8(v_a_1933_, sizeof(void*)*2 + 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_a_1933_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1957_ = v_a_1933_;
v_isShared_1958_ = v_isSharedCheck_2005_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_proof_1954_);
lean_inc(v_e_x27_1953_);
lean_dec(v_a_1933_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2005_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; 
lean_inc(v___y_1930_);
lean_inc_ref(v___y_1929_);
lean_inc(v___y_1928_);
lean_inc_ref(v___y_1927_);
lean_inc(v___y_1926_);
lean_inc_ref(v_e_x27_1953_);
v___x_1959_ = lean_apply_12(v___f_1920_, v___x_1934_, v_e_x27_1953_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_, lean_box(0));
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2004_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1962_ = v___x_1959_;
v_isShared_1963_ = v_isSharedCheck_2004_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1959_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2004_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
if (lean_obj_tag(v_a_1960_) == 0)
{
uint8_t v_done_1964_; uint8_t v_contextDependent_1965_; uint8_t v___y_1967_; 
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1921_);
v_done_1964_ = lean_ctor_get_uint8(v_a_1960_, 0);
v_contextDependent_1965_ = lean_ctor_get_uint8(v_a_1960_, 1);
lean_dec_ref_known(v_a_1960_, 0);
if (v_contextDependent_1955_ == 0)
{
v___y_1967_ = v_contextDependent_1965_;
goto v___jp_1966_;
}
else
{
v___y_1967_ = v_contextDependent_1955_;
goto v___jp_1966_;
}
v___jp_1966_:
{
lean_object* v___x_1969_; 
if (v_isShared_1958_ == 0)
{
v___x_1969_ = v___x_1957_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_e_x27_1953_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_proof_1954_);
v___x_1969_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*2, v_done_1964_);
lean_ctor_set_uint8(v___x_1969_, sizeof(void*)*2 + 1, v___y_1967_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1969_);
v___x_1971_ = v___x_1962_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
}
else
{
lean_object* v_e_x27_1974_; lean_object* v_proof_1975_; uint8_t v_done_1976_; uint8_t v_contextDependent_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2003_; 
lean_del_object(v___x_1962_);
lean_del_object(v___x_1957_);
v_e_x27_1974_ = lean_ctor_get(v_a_1960_, 0);
v_proof_1975_ = lean_ctor_get(v_a_1960_, 1);
v_done_1976_ = lean_ctor_get_uint8(v_a_1960_, sizeof(void*)*2);
v_contextDependent_1977_ = lean_ctor_get_uint8(v_a_1960_, sizeof(void*)*2 + 1);
v_isSharedCheck_2003_ = !lean_is_exclusive(v_a_1960_);
if (v_isSharedCheck_2003_ == 0)
{
v___x_1979_ = v_a_1960_;
v_isShared_1980_ = v_isSharedCheck_2003_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_proof_1975_);
lean_inc(v_e_x27_1974_);
lean_dec(v_a_1960_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2003_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; 
lean_inc_ref(v_e_x27_1974_);
v___x_1981_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v___y_1921_, v_e_x27_1953_, v_proof_1954_, v_e_x27_1974_, v_proof_1975_, v___y_1926_, v___y_1927_, v___y_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1994_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1994_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1994_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
uint8_t v___y_1987_; 
if (v_contextDependent_1955_ == 0)
{
v___y_1987_ = v_contextDependent_1977_;
goto v___jp_1986_;
}
else
{
v___y_1987_ = v_contextDependent_1955_;
goto v___jp_1986_;
}
v___jp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v_a_1982_);
v___x_1989_ = v___x_1979_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_e_x27_1974_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_a_1982_);
lean_ctor_set_uint8(v_reuseFailAlloc_1993_, sizeof(void*)*2, v_done_1976_);
v___x_1989_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
lean_ctor_set_uint8(v___x_1989_, sizeof(void*)*2 + 1, v___y_1987_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1989_);
v___x_1991_ = v___x_1984_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_del_object(v___x_1979_);
lean_dec_ref(v_e_x27_1974_);
v_a_1995_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1981_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1981_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_1957_);
lean_dec_ref(v_proof_1954_);
lean_dec_ref(v_e_x27_1953_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1921_);
return v___x_1959_;
}
}
}
else
{
lean_dec_ref_known(v_a_1933_, 2);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec_ref(v___f_1920_);
return v___x_1932_;
}
}
}
else
{
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
lean_dec(v___y_1928_);
lean_dec_ref(v___y_1927_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v___y_1924_);
lean_dec_ref(v___y_1923_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec_ref(v___f_1920_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__3___boxed(lean_object* v___x_2006_, lean_object* v___f_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__3(v___x_2006_, v___f_2007_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
lean_dec(v___x_2006_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg(lean_object* v_msg_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_){
_start:
{
lean_object* v_ref_2026_; lean_object* v___x_2027_; lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2036_; 
v_ref_2026_ = lean_ctor_get(v___y_2023_, 5);
v___x_2027_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v_msg_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2030_ = v___x_2027_;
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2027_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2034_; 
lean_inc(v_ref_2026_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_ref_2026_);
lean_ctor_set(v___x_2032_, 1, v_a_2028_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set_tag(v___x_2030_, 1);
lean_ctor_set(v___x_2030_, 0, v___x_2032_);
v___x_2034_ = v___x_2030_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg___boxed(lean_object* v_msg_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg(v_msg_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg(lean_object* v_as_2044_, size_t v_sz_2045_, size_t v_i_2046_, lean_object* v_b_2047_){
_start:
{
uint8_t v___x_2049_; 
v___x_2049_ = lean_usize_dec_lt(v_i_2046_, v_sz_2045_);
if (v___x_2049_ == 0)
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2050_, 0, v_b_2047_);
return v___x_2050_;
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; 
v_a_2051_ = lean_array_uget_borrowed(v_as_2044_, v_i_2046_);
lean_inc(v_a_2051_);
v___x_2052_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_2047_, v_a_2051_);
v___x_2053_ = ((size_t)1ULL);
v___x_2054_ = lean_usize_add(v_i_2046_, v___x_2053_);
v_i_2046_ = v___x_2054_;
v_b_2047_ = v___x_2052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg___boxed(lean_object* v_as_2056_, lean_object* v_sz_2057_, lean_object* v_i_2058_, lean_object* v_b_2059_, lean_object* v___y_2060_){
_start:
{
size_t v_sz_boxed_2061_; size_t v_i_boxed_2062_; lean_object* v_res_2063_; 
v_sz_boxed_2061_ = lean_unbox_usize(v_sz_2057_);
lean_dec(v_sz_2057_);
v_i_boxed_2062_ = lean_unbox_usize(v_i_2058_);
lean_dec(v_i_2058_);
v_res_2063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg(v_as_2056_, v_sz_boxed_2061_, v_i_boxed_2062_, v_b_2059_);
lean_dec_ref(v_as_2056_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__1(lean_object* v___x_2064_, lean_object* v_as_2065_, size_t v_sz_2066_, size_t v_i_2067_, lean_object* v_b_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_a_2075_; uint8_t v___x_2079_; 
v___x_2079_ = lean_usize_dec_lt(v_i_2067_, v_sz_2066_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; 
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v_b_2068_);
return v___x_2080_;
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v_a_2081_ = lean_array_uget_borrowed(v_as_2065_, v_i_2067_);
v___x_2082_ = l_Lean_TSyntax_getId(v_a_2081_);
v___x_2083_ = l_Lean_LocalContext_findFromUserName_x3f(v___x_2064_, v___x_2082_);
lean_dec(v___x_2082_);
if (lean_obj_tag(v___x_2083_) == 1)
{
lean_object* v_val_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; 
v_val_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_val_2084_);
lean_dec_ref_known(v___x_2083_, 1);
v___x_2085_ = l_Lean_LocalDecl_toExpr(v_val_2084_);
v___x_2086_ = l_Lean_Meta_Sym_Simp_mkTheoremFromExpr(v___x_2085_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2086_) == 0)
{
lean_object* v_a_2087_; lean_object* v___x_2088_; 
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v___x_2088_ = lean_array_push(v_b_2068_, v_a_2087_);
v_a_2075_ = v___x_2088_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec_ref(v_b_2068_);
v_a_2089_ = lean_ctor_get(v___x_2086_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2086_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2086_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2086_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v___x_2097_; 
lean_dec(v___x_2083_);
lean_inc(v_a_2081_);
v___x_2097_ = l_Lean_realizeGlobalConstNoOverload(v_a_2081_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2099_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc(v_a_2098_);
lean_dec_ref_known(v___x_2097_, 1);
v___x_2099_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(v_a_2098_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; lean_object* v___x_2101_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = lean_array_push(v_b_2068_, v_a_2100_);
v_a_2075_ = v___x_2101_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec_ref(v_b_2068_);
v_a_2102_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2099_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2099_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v_b_2068_);
v_a_2110_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2097_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2097_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
}
v___jp_2074_:
{
size_t v___x_2076_; size_t v___x_2077_; 
v___x_2076_ = ((size_t)1ULL);
v___x_2077_ = lean_usize_add(v_i_2067_, v___x_2076_);
v_i_2067_ = v___x_2077_;
v_b_2068_ = v_a_2075_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__1___boxed(lean_object* v___x_2118_, lean_object* v_as_2119_, lean_object* v_sz_2120_, lean_object* v_i_2121_, lean_object* v_b_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
size_t v_sz_boxed_2128_; size_t v_i_boxed_2129_; lean_object* v_res_2130_; 
v_sz_boxed_2128_ = lean_unbox_usize(v_sz_2120_);
lean_dec(v_sz_2120_);
v_i_boxed_2129_ = lean_unbox_usize(v_i_2121_);
lean_dec(v_i_2121_);
v_res_2130_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__1(v___x_2118_, v_as_2119_, v_sz_boxed_2128_, v_i_boxed_2129_, v_b_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec_ref(v_as_2119_);
lean_dec_ref(v___x_2118_);
return v_res_2130_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__2(void){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2134_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__3(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__2);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
return v___x_2136_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__6(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__5));
v___x_2141_ = l_Lean_stringToMessageData(v___x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts(lean_object* v_variantId_x3f_2142_, lean_object* v_extraIds_x3f_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_, lean_object* v_a_2147_){
_start:
{
lean_object* v___f_2149_; lean_object* v_post_2151_; lean_object* v_extraThms_2155_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v___y_2192_; lean_object* v___y_2193_; lean_object* v___y_2194_; lean_object* v___y_2195_; lean_object* v___y_2212_; 
v___f_2149_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__1));
if (lean_obj_tag(v_variantId_x3f_2142_) == 0)
{
lean_object* v___x_2224_; 
v___x_2224_ = lean_box(0);
v___y_2212_ = v___x_2224_;
goto v___jp_2211_;
}
else
{
lean_object* v_val_2225_; lean_object* v___x_2226_; 
v_val_2225_ = lean_ctor_get(v_variantId_x3f_2142_, 0);
v___x_2226_ = l_Lean_TSyntax_getId(v_val_2225_);
v___y_2212_ = v___x_2226_;
goto v___jp_2211_;
}
v___jp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___f_2149_);
lean_ctor_set(v___x_2152_, 1, v_post_2151_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
v___jp_2154_:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_Meta_Sym_Simp_getSymSimpTheorems___redArg(v___y_2159_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___f_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref_known(v___x_2160_, 1);
v___f_2162_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___boxed), 13, 1);
lean_closure_set(v___f_2162_, 0, v_a_2161_);
v___x_2163_ = lean_unsigned_to_nat(255u);
v___x_2164_ = lean_array_get_size(v_extraThms_2155_);
v___x_2165_ = lean_unsigned_to_nat(0u);
v___x_2166_ = lean_nat_dec_eq(v___x_2164_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_object* v___x_2167_; size_t v_sz_2168_; size_t v___x_2169_; lean_object* v___x_2170_; 
v___x_2167_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__3);
v_sz_2168_ = lean_array_size(v_extraThms_2155_);
v___x_2169_ = ((size_t)0ULL);
v___x_2170_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg(v_extraThms_2155_, v_sz_2168_, v___x_2169_, v___x_2167_);
lean_dec_ref(v_extraThms_2155_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___f_2172_; lean_object* v___f_2173_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref_known(v___x_2170_, 1);
v___f_2172_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__2___boxed), 13, 1);
lean_closure_set(v___f_2172_, 0, v_a_2171_);
v___f_2173_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__4___boxed), 14, 3);
lean_closure_set(v___f_2173_, 0, v___f_2172_);
lean_closure_set(v___f_2173_, 1, v___x_2163_);
lean_closure_set(v___f_2173_, 2, v___f_2162_);
v_post_2151_ = v___f_2173_;
goto v___jp_2150_;
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec_ref(v___f_2162_);
v_a_2174_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2170_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2170_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v___f_2182_; 
lean_dec_ref(v_extraThms_2155_);
v___f_2182_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___lam__3___boxed), 13, 2);
lean_closure_set(v___f_2182_, 0, v___x_2163_);
lean_closure_set(v___f_2182_, 1, v___f_2162_);
v_post_2151_ = v___f_2182_;
goto v___jp_2150_;
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_dec_ref(v_extraThms_2155_);
v_a_2183_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2160_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2160_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
v___jp_2191_:
{
lean_object* v_extraThms_2196_; 
v_extraThms_2196_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__4));
if (lean_obj_tag(v_extraIds_x3f_2143_) == 1)
{
lean_object* v_val_2197_; lean_object* v_lctx_2198_; size_t v_sz_2199_; size_t v___x_2200_; lean_object* v___x_2201_; 
v_val_2197_ = lean_ctor_get(v_extraIds_x3f_2143_, 0);
v_lctx_2198_ = lean_ctor_get(v___y_2192_, 2);
v_sz_2199_ = lean_array_size(v_val_2197_);
v___x_2200_ = ((size_t)0ULL);
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__1(v_lctx_2198_, v_val_2197_, v_sz_2199_, v___x_2200_, v_extraThms_2196_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
v_extraThms_2155_ = v_a_2202_;
v___y_2156_ = v___y_2192_;
v___y_2157_ = v___y_2193_;
v___y_2158_ = v___y_2194_;
v___y_2159_ = v___y_2195_;
goto v___jp_2154_;
}
else
{
lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2210_; 
v_a_2203_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2205_ = v___x_2201_;
v_isShared_2206_ = v_isSharedCheck_2210_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2201_);
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
else
{
v_extraThms_2155_ = v_extraThms_2196_;
v___y_2156_ = v___y_2192_;
v___y_2157_ = v___y_2193_;
v___y_2158_ = v___y_2194_;
v___y_2159_ = v___y_2195_;
goto v___jp_2154_;
}
}
v___jp_2211_:
{
uint8_t v___x_2213_; 
v___x_2213_ = l_Lean_Name_isAnonymous(v___y_2212_);
lean_dec(v___y_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
v___x_2214_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__6, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___closed__6);
v___x_2215_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg(v___x_2214_, v_a_2144_, v_a_2145_, v_a_2146_, v_a_2147_);
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
else
{
v___y_2192_ = v_a_2144_;
v___y_2193_ = v_a_2145_;
v___y_2194_ = v_a_2146_;
v___y_2195_ = v_a_2147_;
goto v___jp_2191_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts___boxed(lean_object* v_variantId_x3f_2227_, lean_object* v_extraIds_x3f_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v_res_2234_; 
v_res_2234_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts(v_variantId_x3f_2227_, v_extraIds_x3f_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2232_);
lean_dec(v_a_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_extraIds_x3f_2228_);
lean_dec(v_variantId_x3f_2227_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0(lean_object* v_as_2235_, size_t v_sz_2236_, size_t v_i_2237_, lean_object* v_b_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___redArg(v_as_2235_, v_sz_2236_, v_i_2237_, v_b_2238_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0___boxed(lean_object* v_as_2245_, lean_object* v_sz_2246_, lean_object* v_i_2247_, lean_object* v_b_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
size_t v_sz_boxed_2254_; size_t v_i_boxed_2255_; lean_object* v_res_2256_; 
v_sz_boxed_2254_ = lean_unbox_usize(v_sz_2246_);
lean_dec(v_sz_2246_);
v_i_boxed_2255_ = lean_unbox_usize(v_i_2247_);
lean_dec(v_i_2247_);
v_res_2256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__0(v_as_2245_, v_sz_boxed_2254_, v_i_boxed_2255_, v_b_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec_ref(v_as_2245_);
return v_res_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2(lean_object* v_00_u03b1_2257_, lean_object* v_msg_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___redArg(v_msg_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2___boxed(lean_object* v_00_u03b1_2265_, lean_object* v_msg_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts_spec__2(v_00_u03b1_2265_, v_msg_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions_spec__0(size_t v_sz_2273_, size_t v_i_2274_, lean_object* v_bs_2275_){
_start:
{
uint8_t v___x_2276_; 
v___x_2276_ = lean_usize_dec_lt(v_i_2274_, v_sz_2273_);
if (v___x_2276_ == 0)
{
return v_bs_2275_;
}
else
{
lean_object* v_v_2277_; lean_object* v___x_2278_; lean_object* v_bs_x27_2279_; size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
v_v_2277_ = lean_array_uget(v_bs_2275_, v_i_2274_);
v___x_2278_ = lean_unsigned_to_nat(0u);
v_bs_x27_2279_ = lean_array_uset(v_bs_2275_, v_i_2274_, v___x_2278_);
v___x_2280_ = ((size_t)1ULL);
v___x_2281_ = lean_usize_add(v_i_2274_, v___x_2280_);
v___x_2282_ = lean_array_uset(v_bs_x27_2279_, v_i_2274_, v_v_2277_);
v_i_2274_ = v___x_2281_;
v_bs_2275_ = v___x_2282_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions_spec__0___boxed(lean_object* v_sz_2284_, lean_object* v_i_2285_, lean_object* v_bs_2286_){
_start:
{
size_t v_sz_boxed_2287_; size_t v_i_boxed_2288_; lean_object* v_res_2289_; 
v_sz_boxed_2287_ = lean_unbox_usize(v_sz_2284_);
lean_dec(v_sz_2284_);
v_i_boxed_2288_ = lean_unbox_usize(v_i_2285_);
lean_dec(v_i_2285_);
v_res_2289_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions_spec__0(v_sz_boxed_2287_, v_i_boxed_2288_, v_bs_2286_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions(lean_object* v_simpClause_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_){
_start:
{
lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2317_ = l_Lean_Syntax_getNumArgs(v_simpClause_2290_);
v___x_2318_ = lean_unsigned_to_nat(0u);
v___x_2319_ = lean_nat_dec_eq(v___x_2317_, v___x_2318_);
lean_dec(v___x_2317_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; lean_object* v___y_2322_; lean_object* v___y_2323_; lean_object* v___y_2331_; lean_object* v___x_2337_; lean_object* v___x_2341_; uint8_t v___x_2342_; 
v___x_2320_ = lean_unsigned_to_nat(1u);
v___x_2337_ = l_Lean_Syntax_getArg(v_simpClause_2290_, v___x_2320_);
v___x_2341_ = l_Lean_Syntax_getNumArgs(v___x_2337_);
v___x_2342_ = lean_nat_dec_eq(v___x_2341_, v___x_2318_);
lean_dec(v___x_2341_);
if (v___x_2342_ == 0)
{
goto v___jp_2338_;
}
else
{
if (v___x_2319_ == 0)
{
lean_object* v___x_2343_; 
lean_dec(v___x_2337_);
v___x_2343_ = lean_box(0);
v___y_2331_ = v___x_2343_;
goto v___jp_2330_;
}
else
{
goto v___jp_2338_;
}
}
v___jp_2321_:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; size_t v_sz_2326_; size_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2324_ = l_Lean_Syntax_getArg(v___y_2322_, v___x_2320_);
lean_dec(v___y_2322_);
v___x_2325_ = l_Lean_Syntax_getSepArgs(v___x_2324_);
lean_dec(v___x_2324_);
v_sz_2326_ = lean_array_size(v___x_2325_);
v___x_2327_ = ((size_t)0ULL);
v___x_2328_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions_spec__0(v_sz_2326_, v___x_2327_, v___x_2325_);
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
v___y_2297_ = v___y_2323_;
v___y_2298_ = v___x_2329_;
goto v___jp_2296_;
}
v___jp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; uint8_t v___x_2335_; 
v___x_2332_ = lean_unsigned_to_nat(2u);
v___x_2333_ = l_Lean_Syntax_getArg(v_simpClause_2290_, v___x_2332_);
v___x_2334_ = l_Lean_Syntax_getNumArgs(v___x_2333_);
v___x_2335_ = lean_nat_dec_eq(v___x_2334_, v___x_2318_);
lean_dec(v___x_2334_);
if (v___x_2335_ == 0)
{
v___y_2322_ = v___x_2333_;
v___y_2323_ = v___y_2331_;
goto v___jp_2321_;
}
else
{
if (v___x_2319_ == 0)
{
lean_object* v___x_2336_; 
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v___y_2297_ = v___y_2331_;
v___y_2298_ = v___x_2336_;
goto v___jp_2296_;
}
else
{
v___y_2322_ = v___x_2333_;
v___y_2323_ = v___y_2331_;
goto v___jp_2321_;
}
}
}
v___jp_2338_:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = l_Lean_Syntax_getArg(v___x_2337_, v___x_2318_);
lean_dec(v___x_2337_);
v___x_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
v___y_2331_ = v___x_2340_;
goto v___jp_2330_;
}
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
return v___x_2345_;
}
v___jp_2296_:
{
lean_object* v___x_2299_; 
v___x_2299_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSymSimpParts(v___y_2297_, v___y_2298_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_);
lean_dec(v___y_2298_);
lean_dec(v___y_2297_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2308_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2308_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v___x_2306_; 
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_a_2300_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2304_);
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
v_a_2309_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2299_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2299_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions___boxed(lean_object* v_simpClause_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions(v_simpClause_2346_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
lean_dec(v_simpClause_2346_);
return v_res_2352_;
}
}
static lean_object* _init_l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__0));
v___x_2355_ = lean_string_utf8_byte_size(v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg(lean_object* v_s_2356_){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; uint8_t v___x_2360_; 
v___x_2357_ = ((lean_object*)(l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__0));
v___x_2358_ = lean_string_utf8_byte_size(v_s_2356_);
v___x_2359_ = lean_obj_once(&l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__1, &l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__1_once, _init_l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg___closed__1);
v___x_2360_ = lean_nat_dec_le(v___x_2359_, v___x_2358_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; 
lean_dec_ref(v_s_2356_);
v___x_2361_ = lean_box(0);
return v___x_2361_;
}
else
{
lean_object* v___x_2362_; uint8_t v___x_2363_; 
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = lean_string_memcmp(v_s_2356_, v___x_2357_, v___x_2362_, v___x_2362_, v___x_2359_);
if (v___x_2363_ == 0)
{
lean_object* v___x_2364_; 
lean_dec_ref(v_s_2356_);
v___x_2364_ = lean_box(0);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
lean_inc_ref(v_s_2356_);
v___x_2365_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2365_, 0, v_s_2356_);
lean_ctor_set(v___x_2365_, 1, v___x_2362_);
lean_ctor_set(v___x_2365_, 2, v___x_2358_);
v___x_2366_ = l_String_Slice_pos_x21(v___x_2365_, v___x_2359_);
lean_dec_ref_known(v___x_2365_, 3);
v___x_2367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2367_, 0, v_s_2356_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
lean_ctor_set(v___x_2367_, 2, v___x_2358_);
v___x_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2367_);
return v___x_2368_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2(lean_object* v_s_2369_, lean_object* v_pat_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg(v_s_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___boxed(lean_object* v_s_2372_, lean_object* v_pat_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2(v_s_2372_, v_pat_2373_);
lean_dec_ref(v_pat_2373_);
return v_res_2374_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(lean_object* v_a_2375_, lean_object* v_x_2376_){
_start:
{
if (lean_obj_tag(v_x_2376_) == 0)
{
uint8_t v___x_2377_; 
v___x_2377_ = 0;
return v___x_2377_;
}
else
{
lean_object* v_key_2378_; lean_object* v_tail_2379_; uint8_t v___x_2380_; 
v_key_2378_ = lean_ctor_get(v_x_2376_, 0);
v_tail_2379_ = lean_ctor_get(v_x_2376_, 2);
v___x_2380_ = lean_nat_dec_eq(v_key_2378_, v_a_2375_);
if (v___x_2380_ == 0)
{
v_x_2376_ = v_tail_2379_;
goto _start;
}
else
{
return v___x_2380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg___boxed(lean_object* v_a_2382_, lean_object* v_x_2383_){
_start:
{
uint8_t v_res_2384_; lean_object* v_r_2385_; 
v_res_2384_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(v_a_2382_, v_x_2383_);
lean_dec(v_x_2383_);
lean_dec(v_a_2382_);
v_r_2385_ = lean_box(v_res_2384_);
return v_r_2385_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(lean_object* v_m_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_buckets_2388_; lean_object* v___x_2389_; uint64_t v___x_2390_; uint64_t v___x_2391_; uint64_t v___x_2392_; uint64_t v_fold_2393_; uint64_t v___x_2394_; uint64_t v___x_2395_; uint64_t v___x_2396_; size_t v___x_2397_; size_t v___x_2398_; size_t v___x_2399_; size_t v___x_2400_; size_t v___x_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; 
v_buckets_2388_ = lean_ctor_get(v_m_2386_, 1);
v___x_2389_ = lean_array_get_size(v_buckets_2388_);
v___x_2390_ = lean_uint64_of_nat(v_a_2387_);
v___x_2391_ = 32ULL;
v___x_2392_ = lean_uint64_shift_right(v___x_2390_, v___x_2391_);
v_fold_2393_ = lean_uint64_xor(v___x_2390_, v___x_2392_);
v___x_2394_ = 16ULL;
v___x_2395_ = lean_uint64_shift_right(v_fold_2393_, v___x_2394_);
v___x_2396_ = lean_uint64_xor(v_fold_2393_, v___x_2395_);
v___x_2397_ = lean_uint64_to_usize(v___x_2396_);
v___x_2398_ = lean_usize_of_nat(v___x_2389_);
v___x_2399_ = ((size_t)1ULL);
v___x_2400_ = lean_usize_sub(v___x_2398_, v___x_2399_);
v___x_2401_ = lean_usize_land(v___x_2397_, v___x_2400_);
v___x_2402_ = lean_array_uget_borrowed(v_buckets_2388_, v___x_2401_);
v___x_2403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(v_a_2387_, v___x_2402_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg___boxed(lean_object* v_m_2404_, lean_object* v_a_2405_){
_start:
{
uint8_t v_res_2406_; lean_object* v_r_2407_; 
v_res_2406_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(v_m_2404_, v_a_2405_);
lean_dec(v_a_2405_);
lean_dec_ref(v_m_2404_);
v_r_2407_ = lean_box(v_res_2406_);
return v_r_2407_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2___redArg(lean_object* v_a_2408_, lean_object* v_b_2409_, lean_object* v_x_2410_){
_start:
{
if (lean_obj_tag(v_x_2410_) == 0)
{
lean_dec(v_b_2409_);
lean_dec(v_a_2408_);
return v_x_2410_;
}
else
{
lean_object* v_key_2411_; lean_object* v_value_2412_; lean_object* v_tail_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2425_; 
v_key_2411_ = lean_ctor_get(v_x_2410_, 0);
v_value_2412_ = lean_ctor_get(v_x_2410_, 1);
v_tail_2413_ = lean_ctor_get(v_x_2410_, 2);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_x_2410_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2415_ = v_x_2410_;
v_isShared_2416_ = v_isSharedCheck_2425_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_tail_2413_);
lean_inc(v_value_2412_);
lean_inc(v_key_2411_);
lean_dec(v_x_2410_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2425_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
uint8_t v___x_2417_; 
v___x_2417_ = lean_nat_dec_eq(v_key_2411_, v_a_2408_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2418_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2___redArg(v_a_2408_, v_b_2409_, v_tail_2413_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 2, v___x_2418_);
v___x_2420_ = v___x_2415_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_key_2411_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_value_2412_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
return v___x_2420_;
}
}
else
{
lean_object* v___x_2423_; 
lean_dec(v_value_2412_);
lean_dec(v_key_2411_);
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 1, v_b_2409_);
lean_ctor_set(v___x_2415_, 0, v_a_2408_);
v___x_2423_ = v___x_2415_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_a_2408_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_b_2409_);
lean_ctor_set(v_reuseFailAlloc_2424_, 2, v_tail_2413_);
v___x_2423_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
return v___x_2423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3_spec__6___redArg(lean_object* v_x_2426_, lean_object* v_x_2427_){
_start:
{
if (lean_obj_tag(v_x_2427_) == 0)
{
return v_x_2426_;
}
else
{
lean_object* v_key_2428_; lean_object* v_value_2429_; lean_object* v_tail_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2453_; 
v_key_2428_ = lean_ctor_get(v_x_2427_, 0);
v_value_2429_ = lean_ctor_get(v_x_2427_, 1);
v_tail_2430_ = lean_ctor_get(v_x_2427_, 2);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_x_2427_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2432_ = v_x_2427_;
v_isShared_2433_ = v_isSharedCheck_2453_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_tail_2430_);
lean_inc(v_value_2429_);
lean_inc(v_key_2428_);
lean_dec(v_x_2427_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2453_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; uint64_t v___x_2435_; uint64_t v___x_2436_; uint64_t v___x_2437_; uint64_t v_fold_2438_; uint64_t v___x_2439_; uint64_t v___x_2440_; uint64_t v___x_2441_; size_t v___x_2442_; size_t v___x_2443_; size_t v___x_2444_; size_t v___x_2445_; size_t v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2434_ = lean_array_get_size(v_x_2426_);
v___x_2435_ = lean_uint64_of_nat(v_key_2428_);
v___x_2436_ = 32ULL;
v___x_2437_ = lean_uint64_shift_right(v___x_2435_, v___x_2436_);
v_fold_2438_ = lean_uint64_xor(v___x_2435_, v___x_2437_);
v___x_2439_ = 16ULL;
v___x_2440_ = lean_uint64_shift_right(v_fold_2438_, v___x_2439_);
v___x_2441_ = lean_uint64_xor(v_fold_2438_, v___x_2440_);
v___x_2442_ = lean_uint64_to_usize(v___x_2441_);
v___x_2443_ = lean_usize_of_nat(v___x_2434_);
v___x_2444_ = ((size_t)1ULL);
v___x_2445_ = lean_usize_sub(v___x_2443_, v___x_2444_);
v___x_2446_ = lean_usize_land(v___x_2442_, v___x_2445_);
v___x_2447_ = lean_array_uget_borrowed(v_x_2426_, v___x_2446_);
lean_inc(v___x_2447_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 2, v___x_2447_);
v___x_2449_ = v___x_2432_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_key_2428_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_value_2429_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_array_uset(v_x_2426_, v___x_2446_, v___x_2449_);
v_x_2426_ = v___x_2450_;
v_x_2427_ = v_tail_2430_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3___redArg(lean_object* v_i_2454_, lean_object* v_source_2455_, lean_object* v_target_2456_){
_start:
{
lean_object* v___x_2457_; uint8_t v___x_2458_; 
v___x_2457_ = lean_array_get_size(v_source_2455_);
v___x_2458_ = lean_nat_dec_lt(v_i_2454_, v___x_2457_);
if (v___x_2458_ == 0)
{
lean_dec_ref(v_source_2455_);
lean_dec(v_i_2454_);
return v_target_2456_;
}
else
{
lean_object* v_es_2459_; lean_object* v___x_2460_; lean_object* v_source_2461_; lean_object* v_target_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_es_2459_ = lean_array_fget(v_source_2455_, v_i_2454_);
v___x_2460_ = lean_box(0);
v_source_2461_ = lean_array_fset(v_source_2455_, v_i_2454_, v___x_2460_);
v_target_2462_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3_spec__6___redArg(v_target_2456_, v_es_2459_);
v___x_2463_ = lean_unsigned_to_nat(1u);
v___x_2464_ = lean_nat_add(v_i_2454_, v___x_2463_);
lean_dec(v_i_2454_);
v_i_2454_ = v___x_2464_;
v_source_2455_ = v_source_2461_;
v_target_2456_ = v_target_2462_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1___redArg(lean_object* v_data_2466_){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v_nbuckets_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2467_ = lean_array_get_size(v_data_2466_);
v___x_2468_ = lean_unsigned_to_nat(2u);
v_nbuckets_2469_ = lean_nat_mul(v___x_2467_, v___x_2468_);
v___x_2470_ = lean_unsigned_to_nat(0u);
v___x_2471_ = lean_box(0);
v___x_2472_ = lean_mk_array(v_nbuckets_2469_, v___x_2471_);
v___x_2473_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3___redArg(v___x_2470_, v_data_2466_, v___x_2472_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0___redArg(lean_object* v_m_2474_, lean_object* v_a_2475_, lean_object* v_b_2476_){
_start:
{
lean_object* v_size_2477_; lean_object* v_buckets_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2521_; 
v_size_2477_ = lean_ctor_get(v_m_2474_, 0);
v_buckets_2478_ = lean_ctor_get(v_m_2474_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_m_2474_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2480_ = v_m_2474_;
v_isShared_2481_ = v_isSharedCheck_2521_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_buckets_2478_);
lean_inc(v_size_2477_);
lean_dec(v_m_2474_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2521_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2482_; uint64_t v___x_2483_; uint64_t v___x_2484_; uint64_t v___x_2485_; uint64_t v_fold_2486_; uint64_t v___x_2487_; uint64_t v___x_2488_; uint64_t v___x_2489_; size_t v___x_2490_; size_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; lean_object* v_bkt_2495_; uint8_t v___x_2496_; 
v___x_2482_ = lean_array_get_size(v_buckets_2478_);
v___x_2483_ = lean_uint64_of_nat(v_a_2475_);
v___x_2484_ = 32ULL;
v___x_2485_ = lean_uint64_shift_right(v___x_2483_, v___x_2484_);
v_fold_2486_ = lean_uint64_xor(v___x_2483_, v___x_2485_);
v___x_2487_ = 16ULL;
v___x_2488_ = lean_uint64_shift_right(v_fold_2486_, v___x_2487_);
v___x_2489_ = lean_uint64_xor(v_fold_2486_, v___x_2488_);
v___x_2490_ = lean_uint64_to_usize(v___x_2489_);
v___x_2491_ = lean_usize_of_nat(v___x_2482_);
v___x_2492_ = ((size_t)1ULL);
v___x_2493_ = lean_usize_sub(v___x_2491_, v___x_2492_);
v___x_2494_ = lean_usize_land(v___x_2490_, v___x_2493_);
v_bkt_2495_ = lean_array_uget_borrowed(v_buckets_2478_, v___x_2494_);
v___x_2496_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(v_a_2475_, v_bkt_2495_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v_size_x27_2498_; lean_object* v___x_2499_; lean_object* v_buckets_x27_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v___x_2497_ = lean_unsigned_to_nat(1u);
v_size_x27_2498_ = lean_nat_add(v_size_2477_, v___x_2497_);
lean_dec(v_size_2477_);
lean_inc(v_bkt_2495_);
v___x_2499_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2499_, 0, v_a_2475_);
lean_ctor_set(v___x_2499_, 1, v_b_2476_);
lean_ctor_set(v___x_2499_, 2, v_bkt_2495_);
v_buckets_x27_2500_ = lean_array_uset(v_buckets_2478_, v___x_2494_, v___x_2499_);
v___x_2501_ = lean_unsigned_to_nat(4u);
v___x_2502_ = lean_nat_mul(v_size_x27_2498_, v___x_2501_);
v___x_2503_ = lean_unsigned_to_nat(3u);
v___x_2504_ = lean_nat_div(v___x_2502_, v___x_2503_);
lean_dec(v___x_2502_);
v___x_2505_ = lean_array_get_size(v_buckets_x27_2500_);
v___x_2506_ = lean_nat_dec_le(v___x_2504_, v___x_2505_);
lean_dec(v___x_2504_);
if (v___x_2506_ == 0)
{
lean_object* v_val_2507_; lean_object* v___x_2509_; 
v_val_2507_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1___redArg(v_buckets_x27_2500_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v_val_2507_);
lean_ctor_set(v___x_2480_, 0, v_size_x27_2498_);
v___x_2509_ = v___x_2480_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_size_x27_2498_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v_val_2507_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
else
{
lean_object* v___x_2512_; 
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v_buckets_x27_2500_);
lean_ctor_set(v___x_2480_, 0, v_size_x27_2498_);
v___x_2512_ = v___x_2480_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_size_x27_2498_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_buckets_x27_2500_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
else
{
lean_object* v___x_2514_; lean_object* v_buckets_x27_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2519_; 
lean_inc(v_bkt_2495_);
v___x_2514_ = lean_box(0);
v_buckets_x27_2515_ = lean_array_uset(v_buckets_2478_, v___x_2494_, v___x_2514_);
v___x_2516_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2___redArg(v_a_2475_, v_b_2476_, v_bkt_2495_);
v___x_2517_ = lean_array_uset(v_buckets_x27_2515_, v___x_2494_, v___x_2516_);
if (v_isShared_2481_ == 0)
{
lean_ctor_set(v___x_2480_, 1, v___x_2517_);
v___x_2519_ = v___x_2480_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_size_2477_);
lean_ctor_set(v_reuseFailAlloc_2520_, 1, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__1));
v___x_2526_ = l_Lean_MessageData_ofFormat(v___x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0(lean_object* v_fst_2531_, lean_object* v___x_2532_, lean_object* v___x_2533_, lean_object* v___x_2534_, lean_object* v_a_2535_, lean_object* v___x_2536_, lean_object* v___x_2537_, lean_object* v_____r_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
uint8_t v___x_2546_; lean_object* v___y_2570_; lean_object* v_val_2577_; uint8_t v___x_2595_; 
v___x_2546_ = 0;
lean_inc(v___x_2533_);
v___x_2595_ = l_Lean_Syntax_isOfKind(v___x_2533_, v___x_2534_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; 
v___x_2596_ = lean_nat_add(v_a_2535_, v___x_2536_);
v_val_2577_ = v___x_2596_;
goto v___jp_2576_;
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2597_ = l_Lean_Syntax_getArg(v___x_2533_, v___x_2537_);
v___x_2598_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__5));
lean_inc(v___x_2597_);
v___x_2599_ = l_Lean_Syntax_isOfKind(v___x_2597_, v___x_2598_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; 
lean_dec(v___x_2597_);
v___x_2600_ = lean_nat_add(v_a_2535_, v___x_2536_);
v_val_2577_ = v___x_2600_;
goto v___jp_2576_;
}
else
{
lean_object* v___x_2601_; 
v___x_2601_ = l_Lean_TSyntax_getId(v___x_2597_);
lean_dec(v___x_2597_);
if (lean_obj_tag(v___x_2601_) == 1)
{
lean_object* v_pre_2602_; 
v_pre_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_pre_2602_);
if (lean_obj_tag(v_pre_2602_) == 0)
{
lean_object* v_str_2603_; lean_object* v___x_2604_; 
v_str_2603_ = lean_ctor_get(v___x_2601_, 1);
lean_inc_ref(v_str_2603_);
lean_dec_ref_known(v___x_2601_, 2);
v___x_2604_ = l_String_dropPrefix_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__2___redArg(v_str_2603_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_dec(v___x_2532_);
goto v___jp_2547_;
}
else
{
lean_object* v_val_2605_; lean_object* v___x_2606_; 
v_val_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_val_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = l_String_Slice_toNat_x3f(v_val_2605_);
lean_dec(v_val_2605_);
if (lean_obj_tag(v___x_2606_) == 1)
{
lean_object* v_val_2607_; 
v_val_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_val_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v_val_2577_ = v_val_2607_;
goto v___jp_2576_;
}
else
{
lean_dec(v___x_2606_);
lean_dec(v___x_2532_);
goto v___jp_2547_;
}
}
}
else
{
lean_dec(v_pre_2602_);
lean_dec_ref_known(v___x_2601_, 2);
lean_dec(v___x_2532_);
goto v___jp_2547_;
}
}
else
{
lean_dec(v___x_2601_);
lean_dec(v___x_2532_);
goto v___jp_2547_;
}
}
}
v___jp_2547_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__2, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__2_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__2);
v___x_2549_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(v___x_2533_, v___x_2548_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___x_2533_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2559_; 
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v___x_2549_, 0);
lean_dec(v_unused_2560_);
v___x_2551_ = v___x_2549_;
v_isShared_2552_ = v_isSharedCheck_2559_;
goto v_resetjp_2550_;
}
else
{
lean_dec(v___x_2549_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2559_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2553_ = lean_box(v___x_2546_);
v___x_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2554_, 0, v_fst_2531_);
lean_ctor_set(v___x_2554_, 1, v___x_2553_);
v___x_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2555_);
v___x_2557_ = v___x_2551_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v___x_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_dec(v_fst_2531_);
v_a_2561_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2549_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2549_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
v___jp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2571_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0___redArg(v_fst_2531_, v___y_2570_, v___x_2532_);
v___x_2572_ = lean_box(v___x_2546_);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2571_);
lean_ctor_set(v___x_2573_, 1, v___x_2572_);
v___x_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
return v___x_2575_;
}
v___jp_2576_:
{
uint8_t v___x_2578_; 
v___x_2578_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(v_fst_2531_, v_val_2577_);
if (v___x_2578_ == 0)
{
lean_dec(v___x_2533_);
v___y_2570_ = v_val_2577_;
goto v___jp_2569_;
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2579_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___closed__3));
lean_inc(v_val_2577_);
v___x_2580_ = l_Nat_reprFast(v_val_2577_);
v___x_2581_ = lean_string_append(v___x_2579_, v___x_2580_);
lean_dec_ref(v___x_2580_);
v___x_2582_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__13_spec__14___redArg___closed__14));
v___x_2583_ = lean_string_append(v___x_2581_, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
v___x_2585_ = l_Lean_MessageData_ofFormat(v___x_2584_);
v___x_2586_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(v___x_2533_, v___x_2585_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
lean_dec(v___x_2533_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_dec_ref_known(v___x_2586_, 1);
v___y_2570_ = v_val_2577_;
goto v___jp_2569_;
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec(v_val_2577_);
lean_dec(v___x_2532_);
lean_dec(v_fst_2531_);
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2586_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0___boxed(lean_object* v_fst_2608_, lean_object* v___x_2609_, lean_object* v___x_2610_, lean_object* v___x_2611_, lean_object* v_a_2612_, lean_object* v___x_2613_, lean_object* v___x_2614_, lean_object* v_____r_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_, lean_object* v___y_2620_, lean_object* v___y_2621_, lean_object* v___y_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0(v_fst_2608_, v___x_2609_, v___x_2610_, v___x_2611_, v_a_2612_, v___x_2613_, v___x_2614_, v_____r_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_);
lean_dec(v___y_2621_);
lean_dec_ref(v___y_2620_);
lean_dec(v___y_2619_);
lean_dec_ref(v___y_2618_);
lean_dec(v___y_2617_);
lean_dec_ref(v___y_2616_);
lean_dec(v___x_2614_);
lean_dec(v___x_2613_);
lean_dec(v_a_2612_);
lean_dec(v___x_2611_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1(lean_object* v_a_2624_, lean_object* v___x_2625_, lean_object* v_fst_2626_, lean_object* v___x_2627_, lean_object* v_____r_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_){
_start:
{
uint8_t v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2636_ = 1;
v___x_2637_ = lean_nat_add(v_a_2624_, v___x_2625_);
v___x_2638_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0___redArg(v_fst_2626_, v___x_2637_, v___x_2627_);
v___x_2639_ = lean_box(v___x_2636_);
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2638_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
v___x_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2640_);
v___x_2642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1___boxed(lean_object* v_a_2643_, lean_object* v___x_2644_, lean_object* v_fst_2645_, lean_object* v___x_2646_, lean_object* v_____r_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1(v_a_2643_, v___x_2644_, v_fst_2645_, v___x_2646_, v_____r_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
lean_dec(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v___x_2644_);
lean_dec(v_a_2643_);
return v_res_2655_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; 
v___x_2669_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__4));
v___x_2670_ = l_Lean_stringToMessageData(v___x_2669_);
return v___x_2670_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__10));
v___x_2683_ = l_Lean_stringToMessageData(v___x_2682_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(lean_object* v_upperBound_2688_, lean_object* v_alts_2689_, lean_object* v___x_2690_, lean_object* v_a_2691_, lean_object* v_b_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
uint8_t v___x_2700_; 
v___x_2700_ = lean_nat_dec_lt(v_a_2691_, v_upperBound_2688_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
lean_dec(v_a_2691_);
v___x_2701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_b_2692_);
return v___x_2701_;
}
else
{
lean_object* v_fst_2702_; lean_object* v_snd_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2818_; 
v_fst_2702_ = lean_ctor_get(v_b_2692_, 0);
v_snd_2703_ = lean_ctor_get(v_b_2692_, 1);
v_isSharedCheck_2818_ = !lean_is_exclusive(v_b_2692_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2705_ = v_b_2692_;
v_isShared_2706_ = v_isSharedCheck_2818_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_snd_2703_);
lean_inc(v_fst_2702_);
lean_dec(v_b_2692_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2818_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v_a_2710_; lean_object* v___y_2714_; lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2707_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__1));
v___x_2708_ = lean_unsigned_to_nat(1u);
v___x_2733_ = lean_unsigned_to_nat(0u);
v___x_2734_ = lean_array_fget_borrowed(v_alts_2689_, v_a_2691_);
lean_inc(v___x_2734_);
v___x_2735_ = l_Lean_Syntax_isOfKind(v___x_2734_, v___x_2707_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2736_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__3));
lean_inc(v___x_2734_);
v___x_2737_ = l_Lean_Syntax_isOfKind(v___x_2734_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5);
v___x_2739_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(v___x_2734_, v___x_2738_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v___x_2741_; 
lean_dec_ref_known(v___x_2739_, 1);
if (v_isShared_2706_ == 0)
{
v___x_2741_ = v___x_2705_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_fst_2702_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v_snd_2703_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
v_a_2710_ = v___x_2741_;
goto v___jp_2709_;
}
}
else
{
lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2750_; 
lean_del_object(v___x_2705_);
lean_dec(v_snd_2703_);
lean_dec(v_fst_2702_);
lean_dec(v_a_2691_);
v_a_2743_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2745_ = v___x_2739_;
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_dec(v___x_2739_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2750_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2748_; 
if (v_isShared_2746_ == 0)
{
v___x_2748_ = v___x_2745_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_a_2743_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2751_ = l_Lean_Syntax_getArg(v___x_2734_, v___x_2708_);
v___x_2752_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__7));
lean_inc(v___x_2751_);
v___x_2753_ = l_Lean_Syntax_isOfKind(v___x_2751_, v___x_2752_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_dec(v___x_2751_);
v___x_2754_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5);
v___x_2755_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(v___x_2734_, v___x_2754_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v___x_2757_; 
lean_dec_ref_known(v___x_2755_, 1);
if (v_isShared_2706_ == 0)
{
v___x_2757_ = v___x_2705_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v_fst_2702_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v_snd_2703_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
v_a_2710_ = v___x_2757_;
goto v___jp_2709_;
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_del_object(v___x_2705_);
lean_dec(v_snd_2703_);
lean_dec(v_fst_2702_);
lean_dec(v_a_2691_);
v_a_2759_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2755_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2755_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
else
{
lean_object* v___x_2767_; lean_object* v___x_2768_; uint8_t v___x_2782_; 
lean_del_object(v___x_2705_);
v___x_2767_ = l_Lean_Syntax_getArg(v___x_2751_, v___x_2733_);
lean_dec(v___x_2751_);
v___x_2768_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__9));
v___x_2782_ = lean_unbox(v_snd_2703_);
lean_dec(v_snd_2703_);
if (v___x_2782_ == 1)
{
goto v___jp_2769_;
}
else
{
if (v___x_2735_ == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_box(0);
lean_inc(v___x_2734_);
v___x_2784_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0(v_fst_2702_, v___x_2734_, v___x_2767_, v___x_2768_, v_a_2691_, v___x_2708_, v___x_2733_, v___x_2783_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
v___y_2714_ = v___x_2784_;
goto v___jp_2713_;
}
else
{
goto v___jp_2769_;
}
}
v___jp_2769_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11);
v___x_2771_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(v___x_2734_, v___x_2770_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; lean_object* v___x_2773_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
lean_inc(v___x_2734_);
v___x_2773_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__0(v_fst_2702_, v___x_2734_, v___x_2767_, v___x_2768_, v_a_2691_, v___x_2708_, v___x_2733_, v_a_2772_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
v___y_2714_ = v___x_2773_;
goto v___jp_2713_;
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_dec(v___x_2767_);
lean_dec(v_fst_2702_);
lean_dec(v_a_2691_);
v_a_2774_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2771_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2771_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2785_ = l_Lean_Syntax_getArg(v___x_2734_, v___x_2733_);
v___x_2786_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__13));
v___x_2787_ = l_Lean_Syntax_isOfKind(v___x_2785_, v___x_2786_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__5);
v___x_2789_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(v___x_2734_, v___x_2788_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v___x_2791_; 
lean_dec_ref_known(v___x_2789_, 1);
if (v_isShared_2706_ == 0)
{
v___x_2791_ = v___x_2705_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_fst_2702_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_snd_2703_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
v_a_2710_ = v___x_2791_;
goto v___jp_2709_;
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_del_object(v___x_2705_);
lean_dec(v_snd_2703_);
lean_dec(v_fst_2702_);
lean_dec(v_a_2691_);
v_a_2793_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2789_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2789_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
else
{
uint8_t v___x_2814_; 
lean_del_object(v___x_2705_);
v___x_2814_ = lean_unbox(v_snd_2703_);
lean_dec(v_snd_2703_);
if (v___x_2814_ == 0)
{
goto v___jp_2801_;
}
else
{
uint8_t v___x_2815_; 
v___x_2815_ = lean_nat_dec_eq(v___x_2690_, v___x_2733_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = lean_box(0);
lean_inc(v___x_2734_);
v___x_2817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1(v_a_2691_, v___x_2708_, v_fst_2702_, v___x_2734_, v___x_2816_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
v___y_2714_ = v___x_2817_;
goto v___jp_2713_;
}
else
{
goto v___jp_2801_;
}
}
v___jp_2801_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11, &l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11_once, _init_l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___closed__11);
v___x_2803_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__3_spec__5_spec__10_spec__14___redArg(v___x_2734_, v___x_2802_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2805_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
lean_inc(v___x_2734_);
v___x_2805_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___lam__1(v_a_2691_, v___x_2708_, v_fst_2702_, v___x_2734_, v_a_2804_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
v___y_2714_ = v___x_2805_;
goto v___jp_2713_;
}
else
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2813_; 
lean_dec(v_fst_2702_);
lean_dec(v_a_2691_);
v_a_2806_ = lean_ctor_get(v___x_2803_, 0);
v_isSharedCheck_2813_ = !lean_is_exclusive(v___x_2803_);
if (v_isSharedCheck_2813_ == 0)
{
v___x_2808_ = v___x_2803_;
v_isShared_2809_ = v_isSharedCheck_2813_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v___x_2803_);
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
v___jp_2709_:
{
lean_object* v___x_2711_; 
v___x_2711_ = lean_nat_add(v_a_2691_, v___x_2708_);
lean_dec(v_a_2691_);
v_a_2691_ = v___x_2711_;
v_b_2692_ = v_a_2710_;
goto _start;
}
v___jp_2713_:
{
if (lean_obj_tag(v___y_2714_) == 0)
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2724_; 
v_a_2715_ = lean_ctor_get(v___y_2714_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___y_2714_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2717_ = v___y_2714_;
v_isShared_2718_ = v_isSharedCheck_2724_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___y_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2724_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
if (lean_obj_tag(v_a_2715_) == 0)
{
lean_object* v_a_2719_; lean_object* v___x_2721_; 
lean_dec(v_a_2691_);
v_a_2719_ = lean_ctor_get(v_a_2715_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v_a_2715_, 1);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 0, v_a_2719_);
v___x_2721_ = v___x_2717_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
else
{
lean_object* v_a_2723_; 
lean_del_object(v___x_2717_);
v_a_2723_ = lean_ctor_get(v_a_2715_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v_a_2715_, 1);
v_a_2710_ = v_a_2723_;
goto v___jp_2709_;
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec(v_a_2691_);
v_a_2725_ = lean_ctor_get(v___y_2714_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___y_2714_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___y_2714_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___y_2714_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg___boxed(lean_object* v_upperBound_2819_, lean_object* v_alts_2820_, lean_object* v___x_2821_, lean_object* v_a_2822_, lean_object* v_b_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(v_upperBound_2819_, v_alts_2820_, v___x_2821_, v_a_2822_, v_b_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v___x_2821_);
lean_dec_ref(v_alts_2820_);
lean_dec(v_upperBound_2819_);
return v_res_2831_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2(void){
_start:
{
uint8_t v_dotOrCase_2838_; lean_object* v_map_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; 
v_dotOrCase_2838_ = 2;
v_map_2839_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2);
v___x_2840_ = lean_box(v_dotOrCase_2838_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v_map_2839_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
return v___x_2841_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3(void){
_start:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2);
v___x_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
return v___x_2843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap(lean_object* v_stx_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l_Lean_Syntax_getOptional_x3f(v_stx_2855_);
if (lean_obj_tag(v___x_2863_) == 1)
{
lean_object* v_val_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2973_; 
v_val_2864_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2866_ = v___x_2863_;
v_isShared_2867_ = v_isSharedCheck_2973_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_val_2864_);
lean_dec(v___x_2863_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2973_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; uint8_t v___x_2869_; 
v___x_2868_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__1));
lean_inc(v_val_2864_);
v___x_2869_ = l_Lean_Syntax_isOfKind(v_val_2864_, v___x_2868_);
if (v___x_2869_ == 0)
{
if (v___x_2869_ == 0)
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_del_object(v___x_2866_);
lean_dec(v_val_2864_);
v___x_2870_ = lean_box(0);
v___x_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2870_);
return v___x_2871_;
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v_alts_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v___x_2872_ = lean_unsigned_to_nat(1u);
v___x_2873_ = l_Lean_Syntax_getArg(v_val_2864_, v___x_2872_);
lean_dec(v_val_2864_);
v_alts_2874_ = l_Lean_Syntax_getArgs(v___x_2873_);
lean_dec(v___x_2873_);
v___x_2875_ = lean_array_get_size(v_alts_2874_);
v___x_2876_ = lean_unsigned_to_nat(0u);
v___x_2877_ = lean_nat_dec_eq(v___x_2875_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; lean_object* v___x_2879_; 
v___x_2878_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2);
v___x_2879_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(v___x_2875_, v_alts_2874_, v___x_2875_, v___x_2876_, v___x_2878_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
lean_dec_ref(v_alts_2874_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2891_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2882_ = v___x_2879_;
v_isShared_2883_ = v_isSharedCheck_2891_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2879_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2891_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v_fst_2884_; lean_object* v___x_2886_; 
v_fst_2884_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_fst_2884_);
lean_dec(v_a_2880_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v_fst_2884_);
v___x_2886_ = v___x_2866_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_fst_2884_);
v___x_2886_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
lean_object* v___x_2888_; 
if (v_isShared_2883_ == 0)
{
lean_ctor_set(v___x_2882_, 0, v___x_2886_);
v___x_2888_ = v___x_2882_;
goto v_reusejp_2887_;
}
else
{
lean_object* v_reuseFailAlloc_2889_; 
v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2886_);
v___x_2888_ = v_reuseFailAlloc_2889_;
goto v_reusejp_2887_;
}
v_reusejp_2887_:
{
return v___x_2888_;
}
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_del_object(v___x_2866_);
v_a_2892_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2879_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2879_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
else
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
lean_dec_ref(v_alts_2874_);
lean_del_object(v___x_2866_);
v___x_2900_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3);
v___x_2901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2900_);
return v___x_2901_;
}
}
}
else
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2902_ = lean_unsigned_to_nat(0u);
v___x_2903_ = l_Lean_Syntax_getArg(v_val_2864_, v___x_2902_);
v___x_2904_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__5));
lean_inc(v___x_2903_);
v___x_2905_ = l_Lean_Syntax_isOfKind(v___x_2903_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_dec(v___x_2903_);
if (v___x_2869_ == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
lean_del_object(v___x_2866_);
lean_dec(v_val_2864_);
v___x_2906_ = lean_box(0);
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
return v___x_2907_;
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v_alts_2910_; lean_object* v___x_2911_; uint8_t v___x_2912_; 
v___x_2908_ = lean_unsigned_to_nat(1u);
v___x_2909_ = l_Lean_Syntax_getArg(v_val_2864_, v___x_2908_);
lean_dec(v_val_2864_);
v_alts_2910_ = l_Lean_Syntax_getArgs(v___x_2909_);
lean_dec(v___x_2909_);
v___x_2911_ = lean_array_get_size(v_alts_2910_);
v___x_2912_ = lean_nat_dec_eq(v___x_2911_, v___x_2902_);
if (v___x_2912_ == 0)
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2);
v___x_2914_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(v___x_2911_, v_alts_2910_, v___x_2911_, v___x_2902_, v___x_2913_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
lean_dec_ref(v_alts_2910_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2926_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2926_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2926_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v_fst_2919_; lean_object* v___x_2921_; 
v_fst_2919_ = lean_ctor_get(v_a_2915_, 0);
lean_inc(v_fst_2919_);
lean_dec(v_a_2915_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v_fst_2919_);
v___x_2921_ = v___x_2866_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_fst_2919_);
v___x_2921_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2923_; 
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 0, v___x_2921_);
v___x_2923_ = v___x_2917_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2921_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_del_object(v___x_2866_);
v_a_2927_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2914_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2914_);
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
lean_object* v___x_2935_; lean_object* v___x_2936_; 
lean_dec_ref(v_alts_2910_);
lean_del_object(v___x_2866_);
v___x_2935_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3);
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2935_);
return v___x_2936_;
}
}
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v___x_2937_ = l_Lean_Syntax_getArg(v___x_2903_, v___x_2902_);
lean_dec(v___x_2903_);
v___x_2938_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__8));
v___x_2939_ = l_Lean_Syntax_isOfKind(v___x_2937_, v___x_2938_);
if (v___x_2939_ == 0)
{
if (v___x_2869_ == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
lean_del_object(v___x_2866_);
lean_dec(v_val_2864_);
v___x_2940_ = lean_box(0);
v___x_2941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
return v___x_2941_;
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v_alts_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2942_ = lean_unsigned_to_nat(1u);
v___x_2943_ = l_Lean_Syntax_getArg(v_val_2864_, v___x_2942_);
lean_dec(v_val_2864_);
v_alts_2944_ = l_Lean_Syntax_getArgs(v___x_2943_);
lean_dec(v___x_2943_);
v___x_2945_ = lean_array_get_size(v_alts_2944_);
v___x_2946_ = lean_nat_dec_eq(v___x_2945_, v___x_2902_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__2);
v___x_2948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(v___x_2945_, v_alts_2944_, v___x_2945_, v___x_2902_, v___x_2947_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
lean_dec_ref(v_alts_2944_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2960_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2960_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2960_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v_fst_2953_; lean_object* v___x_2955_; 
v_fst_2953_ = lean_ctor_get(v_a_2949_, 0);
lean_inc(v_fst_2953_);
lean_dec(v_a_2949_);
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 0, v_fst_2953_);
v___x_2955_ = v___x_2866_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_fst_2953_);
v___x_2955_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2957_; 
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2955_);
v___x_2957_ = v___x_2951_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_del_object(v___x_2866_);
v_a_2961_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2948_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2948_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec_ref(v_alts_2944_);
lean_del_object(v___x_2866_);
v___x_2969_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___closed__3);
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
return v___x_2970_;
}
}
}
else
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_del_object(v___x_2866_);
lean_dec(v_val_2864_);
v___x_2971_ = lean_box(0);
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
return v___x_2972_;
}
}
}
}
}
else
{
lean_object* v___x_2974_; lean_object* v___x_2975_; 
lean_dec(v___x_2863_);
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
return v___x_2975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap___boxed(lean_object* v_stx_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap(v_stx_2976_, v_a_2977_, v_a_2978_, v_a_2979_, v_a_2980_, v_a_2981_, v_a_2982_);
lean_dec(v_a_2982_);
lean_dec_ref(v_a_2981_);
lean_dec(v_a_2980_);
lean_dec_ref(v_a_2979_);
lean_dec(v_a_2978_);
lean_dec_ref(v_a_2977_);
lean_dec(v_stx_2976_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0(lean_object* v_00_u03b2_2985_, lean_object* v_m_2986_, lean_object* v_a_2987_, lean_object* v_b_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0___redArg(v_m_2986_, v_a_2987_, v_b_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1(lean_object* v_00_u03b2_2990_, lean_object* v_m_2991_, lean_object* v_a_2992_){
_start:
{
uint8_t v___x_2993_; 
v___x_2993_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(v_m_2991_, v_a_2992_);
return v___x_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___boxed(lean_object* v_00_u03b2_2994_, lean_object* v_m_2995_, lean_object* v_a_2996_){
_start:
{
uint8_t v_res_2997_; lean_object* v_r_2998_; 
v_res_2997_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1(v_00_u03b2_2994_, v_m_2995_, v_a_2996_);
lean_dec(v_a_2996_);
lean_dec_ref(v_m_2995_);
v_r_2998_ = lean_box(v_res_2997_);
return v_r_2998_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3(lean_object* v_upperBound_2999_, lean_object* v_alts_3000_, lean_object* v___x_3001_, lean_object* v_inst_3002_, lean_object* v_R_3003_, lean_object* v_a_3004_, lean_object* v_b_3005_, lean_object* v_c_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___redArg(v_upperBound_2999_, v_alts_3000_, v___x_3001_, v_a_3004_, v_b_3005_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3___boxed(lean_object* v_upperBound_3015_, lean_object* v_alts_3016_, lean_object* v___x_3017_, lean_object* v_inst_3018_, lean_object* v_R_3019_, lean_object* v_a_3020_, lean_object* v_b_3021_, lean_object* v_c_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__3(v_upperBound_3015_, v_alts_3016_, v___x_3017_, v_inst_3018_, v_R_3019_, v_a_3020_, v_b_3021_, v_c_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___x_3017_);
lean_dec_ref(v_alts_3016_);
lean_dec(v_upperBound_3015_);
return v_res_3030_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0(lean_object* v_00_u03b2_3031_, lean_object* v_a_3032_, lean_object* v_x_3033_){
_start:
{
uint8_t v___x_3034_; 
v___x_3034_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(v_a_3032_, v_x_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3035_, lean_object* v_a_3036_, lean_object* v_x_3037_){
_start:
{
uint8_t v_res_3038_; lean_object* v_r_3039_; 
v_res_3038_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0(v_00_u03b2_3035_, v_a_3036_, v_x_3037_);
lean_dec(v_x_3037_);
lean_dec(v_a_3036_);
v_r_3039_ = lean_box(v_res_3038_);
return v_r_3039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1(lean_object* v_00_u03b2_3040_, lean_object* v_data_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1___redArg(v_data_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2(lean_object* v_00_u03b2_3043_, lean_object* v_a_3044_, lean_object* v_b_3045_, lean_object* v_x_3046_){
_start:
{
lean_object* v___x_3047_; 
v___x_3047_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__2___redArg(v_a_3044_, v_b_3045_, v_x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3048_, lean_object* v_i_3049_, lean_object* v_source_3050_, lean_object* v_target_3051_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3___redArg(v_i_3049_, v_source_3050_, v_target_3051_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_3053_, lean_object* v_x_3054_, lean_object* v_x_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1_spec__3_spec__6___redArg(v_x_3054_, v_x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg(lean_object* v_a_3057_, lean_object* v_x_3058_){
_start:
{
if (lean_obj_tag(v_x_3058_) == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_box(0);
return v___x_3059_;
}
else
{
lean_object* v_key_3060_; lean_object* v_value_3061_; lean_object* v_tail_3062_; uint8_t v___x_3063_; 
v_key_3060_ = lean_ctor_get(v_x_3058_, 0);
v_value_3061_ = lean_ctor_get(v_x_3058_, 1);
v_tail_3062_ = lean_ctor_get(v_x_3058_, 2);
v___x_3063_ = lean_nat_dec_eq(v_key_3060_, v_a_3057_);
if (v___x_3063_ == 0)
{
v_x_3058_ = v_tail_3062_;
goto _start;
}
else
{
lean_object* v___x_3065_; 
lean_inc(v_value_3061_);
v___x_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3065_, 0, v_value_3061_);
return v___x_3065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg___boxed(lean_object* v_a_3066_, lean_object* v_x_3067_){
_start:
{
lean_object* v_res_3068_; 
v_res_3068_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg(v_a_3066_, v_x_3067_);
lean_dec(v_x_3067_);
lean_dec(v_a_3066_);
return v_res_3068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg(lean_object* v_m_3069_, lean_object* v_a_3070_){
_start:
{
lean_object* v_buckets_3071_; lean_object* v___x_3072_; uint64_t v___x_3073_; uint64_t v___x_3074_; uint64_t v___x_3075_; uint64_t v_fold_3076_; uint64_t v___x_3077_; uint64_t v___x_3078_; uint64_t v___x_3079_; size_t v___x_3080_; size_t v___x_3081_; size_t v___x_3082_; size_t v___x_3083_; size_t v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_buckets_3071_ = lean_ctor_get(v_m_3069_, 1);
v___x_3072_ = lean_array_get_size(v_buckets_3071_);
v___x_3073_ = lean_uint64_of_nat(v_a_3070_);
v___x_3074_ = 32ULL;
v___x_3075_ = lean_uint64_shift_right(v___x_3073_, v___x_3074_);
v_fold_3076_ = lean_uint64_xor(v___x_3073_, v___x_3075_);
v___x_3077_ = 16ULL;
v___x_3078_ = lean_uint64_shift_right(v_fold_3076_, v___x_3077_);
v___x_3079_ = lean_uint64_xor(v_fold_3076_, v___x_3078_);
v___x_3080_ = lean_uint64_to_usize(v___x_3079_);
v___x_3081_ = lean_usize_of_nat(v___x_3072_);
v___x_3082_ = ((size_t)1ULL);
v___x_3083_ = lean_usize_sub(v___x_3081_, v___x_3082_);
v___x_3084_ = lean_usize_land(v___x_3080_, v___x_3083_);
v___x_3085_ = lean_array_uget_borrowed(v_buckets_3071_, v___x_3084_);
v___x_3086_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg(v_a_3070_, v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg___boxed(lean_object* v_m_3087_, lean_object* v_a_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg(v_m_3087_, v_a_3088_);
lean_dec(v_a_3088_);
lean_dec_ref(v_m_3087_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__5___redArg(lean_object* v_m_3090_, lean_object* v_a_3091_, lean_object* v_b_3092_){
_start:
{
lean_object* v_size_3093_; lean_object* v_buckets_3094_; lean_object* v___x_3095_; uint64_t v___x_3096_; uint64_t v___x_3097_; uint64_t v___x_3098_; uint64_t v_fold_3099_; uint64_t v___x_3100_; uint64_t v___x_3101_; uint64_t v___x_3102_; size_t v___x_3103_; size_t v___x_3104_; size_t v___x_3105_; size_t v___x_3106_; size_t v___x_3107_; lean_object* v_bkt_3108_; uint8_t v___x_3109_; 
v_size_3093_ = lean_ctor_get(v_m_3090_, 0);
v_buckets_3094_ = lean_ctor_get(v_m_3090_, 1);
v___x_3095_ = lean_array_get_size(v_buckets_3094_);
v___x_3096_ = lean_uint64_of_nat(v_a_3091_);
v___x_3097_ = 32ULL;
v___x_3098_ = lean_uint64_shift_right(v___x_3096_, v___x_3097_);
v_fold_3099_ = lean_uint64_xor(v___x_3096_, v___x_3098_);
v___x_3100_ = 16ULL;
v___x_3101_ = lean_uint64_shift_right(v_fold_3099_, v___x_3100_);
v___x_3102_ = lean_uint64_xor(v_fold_3099_, v___x_3101_);
v___x_3103_ = lean_uint64_to_usize(v___x_3102_);
v___x_3104_ = lean_usize_of_nat(v___x_3095_);
v___x_3105_ = ((size_t)1ULL);
v___x_3106_ = lean_usize_sub(v___x_3104_, v___x_3105_);
v___x_3107_ = lean_usize_land(v___x_3103_, v___x_3106_);
v_bkt_3108_ = lean_array_uget_borrowed(v_buckets_3094_, v___x_3107_);
v___x_3109_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__0___redArg(v_a_3091_, v_bkt_3108_);
if (v___x_3109_ == 0)
{
lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3130_; 
lean_inc_ref(v_buckets_3094_);
lean_inc(v_size_3093_);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_m_3090_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; lean_object* v_unused_3132_; 
v_unused_3131_ = lean_ctor_get(v_m_3090_, 1);
lean_dec(v_unused_3131_);
v_unused_3132_ = lean_ctor_get(v_m_3090_, 0);
lean_dec(v_unused_3132_);
v___x_3111_ = v_m_3090_;
v_isShared_3112_ = v_isSharedCheck_3130_;
goto v_resetjp_3110_;
}
else
{
lean_dec(v_m_3090_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3130_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3113_; lean_object* v_size_x27_3114_; lean_object* v___x_3115_; lean_object* v_buckets_x27_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; uint8_t v___x_3122_; 
v___x_3113_ = lean_unsigned_to_nat(1u);
v_size_x27_3114_ = lean_nat_add(v_size_3093_, v___x_3113_);
lean_dec(v_size_3093_);
lean_inc(v_bkt_3108_);
v___x_3115_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3115_, 0, v_a_3091_);
lean_ctor_set(v___x_3115_, 1, v_b_3092_);
lean_ctor_set(v___x_3115_, 2, v_bkt_3108_);
v_buckets_x27_3116_ = lean_array_uset(v_buckets_3094_, v___x_3107_, v___x_3115_);
v___x_3117_ = lean_unsigned_to_nat(4u);
v___x_3118_ = lean_nat_mul(v_size_x27_3114_, v___x_3117_);
v___x_3119_ = lean_unsigned_to_nat(3u);
v___x_3120_ = lean_nat_div(v___x_3118_, v___x_3119_);
lean_dec(v___x_3118_);
v___x_3121_ = lean_array_get_size(v_buckets_x27_3116_);
v___x_3122_ = lean_nat_dec_le(v___x_3120_, v___x_3121_);
lean_dec(v___x_3120_);
if (v___x_3122_ == 0)
{
lean_object* v_val_3123_; lean_object* v___x_3125_; 
v_val_3123_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__0_spec__1___redArg(v_buckets_x27_3116_);
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v_val_3123_);
lean_ctor_set(v___x_3111_, 0, v_size_x27_3114_);
v___x_3125_ = v___x_3111_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_size_x27_3114_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v_val_3123_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
else
{
lean_object* v___x_3128_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 1, v_buckets_x27_3116_);
lean_ctor_set(v___x_3111_, 0, v_size_x27_3114_);
v___x_3128_ = v___x_3111_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_size_x27_3114_);
lean_ctor_set(v_reuseFailAlloc_3129_, 1, v_buckets_x27_3116_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_dec(v_b_3092_);
lean_dec(v_a_3091_);
return v_m_3090_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg(lean_object* v_upperBound_3133_, lean_object* v_alts_3134_, lean_object* v_invariants_3135_, lean_object* v_a_3136_, lean_object* v_b_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v_a_3146_; uint8_t v___x_3150_; 
v___x_3150_ = lean_nat_dec_lt(v_a_3136_, v_upperBound_3133_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; 
lean_dec(v_a_3136_);
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v_b_3137_);
return v___x_3151_;
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; 
v___x_3152_ = lean_unsigned_to_nat(1u);
v___x_3153_ = lean_nat_add(v_a_3136_, v___x_3152_);
v___x_3154_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(v_b_3137_, v___x_3153_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg(v_alts_3134_, v___x_3153_);
if (lean_obj_tag(v___x_3155_) == 1)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec_ref_known(v___x_3155_, 1);
v___x_3156_ = lean_array_fget_borrowed(v_invariants_3135_, v_a_3136_);
lean_inc(v___x_3156_);
v___x_3157_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_elabInvariant(v_alts_3134_, v___x_3153_, v___x_3156_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_dec_ref_known(v___x_3157_, 1);
v___x_3158_ = lean_box(0);
v___x_3159_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__5___redArg(v_b_3137_, v___x_3153_, v___x_3158_);
v_a_3146_ = v___x_3159_;
goto v___jp_3145_;
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v___x_3153_);
lean_dec_ref(v_b_3137_);
lean_dec(v_a_3136_);
v_a_3160_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___x_3157_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___x_3157_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
else
{
lean_dec(v___x_3155_);
lean_dec(v___x_3153_);
v_a_3146_ = v_b_3137_;
goto v___jp_3145_;
}
}
else
{
lean_dec(v___x_3153_);
v_a_3146_ = v_b_3137_;
goto v___jp_3145_;
}
}
v___jp_3145_:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3147_ = lean_unsigned_to_nat(1u);
v___x_3148_ = lean_nat_add(v_a_3136_, v___x_3147_);
lean_dec(v_a_3136_);
v_a_3136_ = v___x_3148_;
v_b_3137_ = v_a_3146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg___boxed(lean_object* v_upperBound_3168_, lean_object* v_alts_3169_, lean_object* v_invariants_3170_, lean_object* v_a_3171_, lean_object* v_b_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg(v_upperBound_3168_, v_alts_3169_, v_invariants_3170_, v_a_3171_, v_b_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
lean_dec(v___y_3178_);
lean_dec_ref(v___y_3177_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec_ref(v_invariants_3170_);
lean_dec_ref(v_alts_3169_);
lean_dec(v_upperBound_3168_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg(lean_object* v_ref_3181_, lean_object* v_msgData_3182_, uint8_t v_severity_3183_, uint8_t v_isSilent_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_){
_start:
{
lean_object* v___y_3191_; uint8_t v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; uint8_t v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3227_; uint8_t v___y_3228_; uint8_t v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3232_; uint8_t v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3252_; lean_object* v___y_3253_; uint8_t v___y_3254_; uint8_t v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; uint8_t v___y_3258_; lean_object* v___y_3259_; lean_object* v___y_3263_; uint8_t v___y_3264_; uint8_t v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3268_; uint8_t v___y_3269_; uint8_t v___x_3274_; lean_object* v___y_3276_; uint8_t v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; uint8_t v___y_3281_; uint8_t v___y_3282_; uint8_t v___y_3284_; uint8_t v___x_3299_; 
v___x_3274_ = 2;
v___x_3299_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3183_, v___x_3274_);
if (v___x_3299_ == 0)
{
v___y_3284_ = v___x_3299_;
goto v___jp_3283_;
}
else
{
uint8_t v___x_3300_; 
lean_inc_ref(v_msgData_3182_);
v___x_3300_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3182_);
v___y_3284_ = v___x_3300_;
goto v___jp_3283_;
}
v___jp_3190_:
{
lean_object* v___x_3200_; lean_object* v_currNamespace_3201_; lean_object* v_openDecls_3202_; lean_object* v_env_3203_; lean_object* v_nextMacroScope_3204_; lean_object* v_ngen_3205_; lean_object* v_auxDeclNGen_3206_; lean_object* v_traceState_3207_; lean_object* v_cache_3208_; lean_object* v_messages_3209_; lean_object* v_infoState_3210_; lean_object* v_snapshotTasks_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3225_; 
v___x_3200_ = lean_st_ref_take(v___y_3199_);
v_currNamespace_3201_ = lean_ctor_get(v___y_3198_, 6);
v_openDecls_3202_ = lean_ctor_get(v___y_3198_, 7);
v_env_3203_ = lean_ctor_get(v___x_3200_, 0);
v_nextMacroScope_3204_ = lean_ctor_get(v___x_3200_, 1);
v_ngen_3205_ = lean_ctor_get(v___x_3200_, 2);
v_auxDeclNGen_3206_ = lean_ctor_get(v___x_3200_, 3);
v_traceState_3207_ = lean_ctor_get(v___x_3200_, 4);
v_cache_3208_ = lean_ctor_get(v___x_3200_, 5);
v_messages_3209_ = lean_ctor_get(v___x_3200_, 6);
v_infoState_3210_ = lean_ctor_get(v___x_3200_, 7);
v_snapshotTasks_3211_ = lean_ctor_get(v___x_3200_, 8);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3213_ = v___x_3200_;
v_isShared_3214_ = v_isSharedCheck_3225_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_snapshotTasks_3211_);
lean_inc(v_infoState_3210_);
lean_inc(v_messages_3209_);
lean_inc(v_cache_3208_);
lean_inc(v_traceState_3207_);
lean_inc(v_auxDeclNGen_3206_);
lean_inc(v_ngen_3205_);
lean_inc(v_nextMacroScope_3204_);
lean_inc(v_env_3203_);
lean_dec(v___x_3200_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3225_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3220_; 
lean_inc(v_openDecls_3202_);
lean_inc(v_currNamespace_3201_);
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v_currNamespace_3201_);
lean_ctor_set(v___x_3215_, 1, v_openDecls_3202_);
v___x_3216_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v___y_3193_);
lean_inc_ref(v___y_3191_);
lean_inc_ref(v___y_3196_);
v___x_3217_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3217_, 0, v___y_3196_);
lean_ctor_set(v___x_3217_, 1, v___y_3194_);
lean_ctor_set(v___x_3217_, 2, v___y_3195_);
lean_ctor_set(v___x_3217_, 3, v___y_3191_);
lean_ctor_set(v___x_3217_, 4, v___x_3216_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*5, v___y_3192_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*5 + 1, v___y_3197_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*5 + 2, v_isSilent_3184_);
v___x_3218_ = l_Lean_MessageLog_add(v___x_3217_, v_messages_3209_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 6, v___x_3218_);
v___x_3220_ = v___x_3213_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_env_3203_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v_nextMacroScope_3204_);
lean_ctor_set(v_reuseFailAlloc_3224_, 2, v_ngen_3205_);
lean_ctor_set(v_reuseFailAlloc_3224_, 3, v_auxDeclNGen_3206_);
lean_ctor_set(v_reuseFailAlloc_3224_, 4, v_traceState_3207_);
lean_ctor_set(v_reuseFailAlloc_3224_, 5, v_cache_3208_);
lean_ctor_set(v_reuseFailAlloc_3224_, 6, v___x_3218_);
lean_ctor_set(v_reuseFailAlloc_3224_, 7, v_infoState_3210_);
lean_ctor_set(v_reuseFailAlloc_3224_, 8, v_snapshotTasks_3211_);
v___x_3220_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3221_ = lean_st_ref_set(v___y_3199_, v___x_3220_);
v___x_3222_ = lean_box(0);
v___x_3223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
return v___x_3223_;
}
}
}
v___jp_3226_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3250_; 
v___x_3235_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3182_);
v___x_3236_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v___x_3235_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3250_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3250_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_inc_ref_n(v___y_3232_, 2);
v___x_3241_ = l_Lean_FileMap_toPosition(v___y_3232_, v___y_3230_);
lean_dec(v___y_3230_);
v___x_3242_ = l_Lean_FileMap_toPosition(v___y_3232_, v___y_3234_);
lean_dec(v___y_3234_);
v___x_3243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3242_);
v___x_3244_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___closed__0));
if (v___y_3228_ == 0)
{
lean_del_object(v___x_3239_);
lean_dec_ref(v___y_3227_);
v___y_3191_ = v___x_3244_;
v___y_3192_ = v___y_3229_;
v___y_3193_ = v_a_3237_;
v___y_3194_ = v___x_3241_;
v___y_3195_ = v___x_3243_;
v___y_3196_ = v___y_3231_;
v___y_3197_ = v___y_3233_;
v___y_3198_ = v___y_3187_;
v___y_3199_ = v___y_3188_;
goto v___jp_3190_;
}
else
{
uint8_t v___x_3245_; 
lean_inc(v_a_3237_);
v___x_3245_ = l_Lean_MessageData_hasTag(v___y_3227_, v_a_3237_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3246_; lean_object* v___x_3248_; 
lean_dec_ref_known(v___x_3243_, 1);
lean_dec_ref(v___x_3241_);
lean_dec(v_a_3237_);
v___x_3246_ = lean_box(0);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3246_);
v___x_3248_ = v___x_3239_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
else
{
lean_del_object(v___x_3239_);
v___y_3191_ = v___x_3244_;
v___y_3192_ = v___y_3229_;
v___y_3193_ = v_a_3237_;
v___y_3194_ = v___x_3241_;
v___y_3195_ = v___x_3243_;
v___y_3196_ = v___y_3231_;
v___y_3197_ = v___y_3233_;
v___y_3198_ = v___y_3187_;
v___y_3199_ = v___y_3188_;
goto v___jp_3190_;
}
}
}
}
v___jp_3251_:
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Syntax_getTailPos_x3f(v___y_3253_, v___y_3254_);
lean_dec(v___y_3253_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_inc(v___y_3259_);
v___y_3227_ = v___y_3252_;
v___y_3228_ = v___y_3255_;
v___y_3229_ = v___y_3254_;
v___y_3230_ = v___y_3259_;
v___y_3231_ = v___y_3257_;
v___y_3232_ = v___y_3256_;
v___y_3233_ = v___y_3258_;
v___y_3234_ = v___y_3259_;
goto v___jp_3226_;
}
else
{
lean_object* v_val_3261_; 
v_val_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_val_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v___y_3227_ = v___y_3252_;
v___y_3228_ = v___y_3255_;
v___y_3229_ = v___y_3254_;
v___y_3230_ = v___y_3259_;
v___y_3231_ = v___y_3257_;
v___y_3232_ = v___y_3256_;
v___y_3233_ = v___y_3258_;
v___y_3234_ = v_val_3261_;
goto v___jp_3226_;
}
}
v___jp_3262_:
{
lean_object* v_ref_3270_; lean_object* v___x_3271_; 
v_ref_3270_ = l_Lean_replaceRef(v_ref_3181_, v___y_3268_);
v___x_3271_ = l_Lean_Syntax_getPos_x3f(v_ref_3270_, v___y_3265_);
if (lean_obj_tag(v___x_3271_) == 0)
{
lean_object* v___x_3272_; 
v___x_3272_ = lean_unsigned_to_nat(0u);
v___y_3252_ = v___y_3263_;
v___y_3253_ = v_ref_3270_;
v___y_3254_ = v___y_3265_;
v___y_3255_ = v___y_3264_;
v___y_3256_ = v___y_3267_;
v___y_3257_ = v___y_3266_;
v___y_3258_ = v___y_3269_;
v___y_3259_ = v___x_3272_;
goto v___jp_3251_;
}
else
{
lean_object* v_val_3273_; 
v_val_3273_ = lean_ctor_get(v___x_3271_, 0);
lean_inc(v_val_3273_);
lean_dec_ref_known(v___x_3271_, 1);
v___y_3252_ = v___y_3263_;
v___y_3253_ = v_ref_3270_;
v___y_3254_ = v___y_3265_;
v___y_3255_ = v___y_3264_;
v___y_3256_ = v___y_3267_;
v___y_3257_ = v___y_3266_;
v___y_3258_ = v___y_3269_;
v___y_3259_ = v_val_3273_;
goto v___jp_3251_;
}
}
v___jp_3275_:
{
if (v___y_3282_ == 0)
{
v___y_3263_ = v___y_3276_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3281_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3278_;
v___y_3268_ = v___y_3280_;
v___y_3269_ = v_severity_3183_;
goto v___jp_3262_;
}
else
{
v___y_3263_ = v___y_3276_;
v___y_3264_ = v___y_3277_;
v___y_3265_ = v___y_3281_;
v___y_3266_ = v___y_3279_;
v___y_3267_ = v___y_3278_;
v___y_3268_ = v___y_3280_;
v___y_3269_ = v___x_3274_;
goto v___jp_3262_;
}
}
v___jp_3283_:
{
if (v___y_3284_ == 0)
{
lean_object* v_fileName_3285_; lean_object* v_fileMap_3286_; lean_object* v_options_3287_; lean_object* v_ref_3288_; uint8_t v_suppressElabErrors_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___f_3292_; uint8_t v___x_3293_; uint8_t v___x_3294_; 
v_fileName_3285_ = lean_ctor_get(v___y_3187_, 0);
v_fileMap_3286_ = lean_ctor_get(v___y_3187_, 1);
v_options_3287_ = lean_ctor_get(v___y_3187_, 2);
v_ref_3288_ = lean_ctor_get(v___y_3187_, 5);
v_suppressElabErrors_3289_ = lean_ctor_get_uint8(v___y_3187_, sizeof(void*)*14 + 1);
v___x_3290_ = lean_box(v___y_3284_);
v___x_3291_ = lean_box(v_suppressElabErrors_3289_);
v___f_3292_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3292_, 0, v___x_3290_);
lean_closure_set(v___f_3292_, 1, v___x_3291_);
v___x_3293_ = 1;
v___x_3294_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3183_, v___x_3293_);
if (v___x_3294_ == 0)
{
v___y_3276_ = v___f_3292_;
v___y_3277_ = v_suppressElabErrors_3289_;
v___y_3278_ = v_fileMap_3286_;
v___y_3279_ = v_fileName_3285_;
v___y_3280_ = v_ref_3288_;
v___y_3281_ = v___y_3284_;
v___y_3282_ = v___x_3294_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3295_ = l_Lean_warningAsError;
v___x_3296_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_options_3287_, v___x_3295_);
v___y_3276_ = v___f_3292_;
v___y_3277_ = v_suppressElabErrors_3289_;
v___y_3278_ = v_fileMap_3286_;
v___y_3279_ = v_fileName_3285_;
v___y_3280_ = v_ref_3288_;
v___y_3281_ = v___y_3284_;
v___y_3282_ = v___x_3296_;
goto v___jp_3275_;
}
}
else
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
lean_dec_ref(v_msgData_3182_);
v___x_3297_ = lean_box(0);
v___x_3298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3297_);
return v___x_3298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg___boxed(lean_object* v_ref_3301_, lean_object* v_msgData_3302_, lean_object* v_severity_3303_, lean_object* v_isSilent_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
uint8_t v_severity_boxed_3310_; uint8_t v_isSilent_boxed_3311_; lean_object* v_res_3312_; 
v_severity_boxed_3310_ = lean_unbox(v_severity_3303_);
v_isSilent_boxed_3311_ = lean_unbox(v_isSilent_3304_);
v_res_3312_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg(v_ref_3301_, v_msgData_3302_, v_severity_boxed_3310_, v_isSilent_boxed_3311_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v_ref_3301_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0(lean_object* v_ref_3313_, lean_object* v_msgData_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
uint8_t v___x_3322_; uint8_t v___x_3323_; lean_object* v___x_3324_; 
v___x_3322_ = 1;
v___x_3323_ = 0;
v___x_3324_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg(v_ref_3313_, v_msgData_3314_, v___x_3322_, v___x_3323_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0___boxed(lean_object* v_ref_3325_, lean_object* v_msgData_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_res_3334_; 
v_res_3334_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0(v_ref_3325_, v_msgData_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
lean_dec(v___y_3332_);
lean_dec_ref(v___y_3331_);
lean_dec(v___y_3330_);
lean_dec_ref(v___y_3329_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v_ref_3325_);
return v_res_3334_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1(lean_object* v_a_3337_, lean_object* v_as_3338_, size_t v_sz_3339_, size_t v_i_3340_, lean_object* v_b_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_a_3350_; uint8_t v___x_3354_; 
v___x_3354_ = lean_usize_dec_lt(v_i_3340_, v_sz_3339_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
v___x_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3355_, 0, v_b_3341_);
return v___x_3355_;
}
else
{
lean_object* v_a_3356_; lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v_a_3356_ = lean_array_uget_borrowed(v_as_3338_, v_i_3340_);
v_fst_3357_ = lean_ctor_get(v_a_3356_, 0);
v_snd_3358_ = lean_ctor_get(v_a_3356_, 1);
v___x_3359_ = lean_box(0);
v___x_3360_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap_spec__1___redArg(v_a_3337_, v_fst_3357_);
if (v___x_3360_ == 0)
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___closed__0));
lean_inc(v_fst_3357_);
v___x_3362_ = l_Nat_reprFast(v_fst_3357_);
v___x_3363_ = lean_string_append(v___x_3361_, v___x_3362_);
lean_dec_ref(v___x_3362_);
v___x_3364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___closed__1));
v___x_3365_ = lean_string_append(v___x_3363_, v___x_3364_);
v___x_3366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
v___x_3367_ = l_Lean_MessageData_ofFormat(v___x_3366_);
v___x_3368_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0(v_snd_3358_, v___x_3367_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_dec_ref_known(v___x_3368_, 1);
v_a_3350_ = v___x_3359_;
goto v___jp_3349_;
}
else
{
return v___x_3368_;
}
}
else
{
v_a_3350_ = v___x_3359_;
goto v___jp_3349_;
}
}
v___jp_3349_:
{
size_t v___x_3351_; size_t v___x_3352_; 
v___x_3351_ = ((size_t)1ULL);
v___x_3352_ = lean_usize_add(v_i_3340_, v___x_3351_);
v_i_3340_ = v___x_3352_;
v_b_3341_ = v_a_3350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1___boxed(lean_object* v_a_3369_, lean_object* v_as_3370_, lean_object* v_sz_3371_, lean_object* v_i_3372_, lean_object* v_b_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
size_t v_sz_boxed_3381_; size_t v_i_boxed_3382_; lean_object* v_res_3383_; 
v_sz_boxed_3381_ = lean_unbox_usize(v_sz_3371_);
lean_dec(v_sz_3371_);
v_i_boxed_3382_ = lean_unbox_usize(v_i_3372_);
lean_dec(v_i_3372_);
v_res_3383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1(v_a_3369_, v_as_3370_, v_sz_boxed_3381_, v_i_boxed_3382_, v_b_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec(v___y_3375_);
lean_dec_ref(v___y_3374_);
lean_dec_ref(v_as_3370_);
lean_dec_ref(v_a_3369_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__2(lean_object* v_x_3384_, lean_object* v_x_3385_){
_start:
{
if (lean_obj_tag(v_x_3385_) == 0)
{
return v_x_3384_;
}
else
{
lean_object* v_key_3386_; lean_object* v_value_3387_; lean_object* v_tail_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v_key_3386_ = lean_ctor_get(v_x_3385_, 0);
v_value_3387_ = lean_ctor_get(v_x_3385_, 1);
v_tail_3388_ = lean_ctor_get(v_x_3385_, 2);
lean_inc(v_value_3387_);
lean_inc(v_key_3386_);
v___x_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3389_, 0, v_key_3386_);
lean_ctor_set(v___x_3389_, 1, v_value_3387_);
v___x_3390_ = lean_array_push(v_x_3384_, v___x_3389_);
v_x_3384_ = v___x_3390_;
v_x_3385_ = v_tail_3388_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__2___boxed(lean_object* v_x_3392_, lean_object* v_x_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__2(v_x_3392_, v_x_3393_);
lean_dec(v_x_3393_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3(lean_object* v_as_3395_, size_t v_i_3396_, size_t v_stop_3397_, lean_object* v_b_3398_){
_start:
{
uint8_t v___x_3399_; 
v___x_3399_ = lean_usize_dec_eq(v_i_3396_, v_stop_3397_);
if (v___x_3399_ == 0)
{
lean_object* v___x_3400_; lean_object* v___x_3401_; size_t v___x_3402_; size_t v___x_3403_; 
v___x_3400_ = lean_array_uget_borrowed(v_as_3395_, v_i_3396_);
v___x_3401_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__2(v_b_3398_, v___x_3400_);
v___x_3402_ = ((size_t)1ULL);
v___x_3403_ = lean_usize_add(v_i_3396_, v___x_3402_);
v_i_3396_ = v___x_3403_;
v_b_3398_ = v___x_3401_;
goto _start;
}
else
{
return v_b_3398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3___boxed(lean_object* v_as_3405_, lean_object* v_i_3406_, lean_object* v_stop_3407_, lean_object* v_b_3408_){
_start:
{
size_t v_i_boxed_3409_; size_t v_stop_boxed_3410_; lean_object* v_res_3411_; 
v_i_boxed_3409_ = lean_unbox_usize(v_i_3406_);
lean_dec(v_i_3406_);
v_stop_boxed_3410_ = lean_unbox_usize(v_stop_3407_);
lean_dec(v_stop_3407_);
v_res_3411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3(v_as_3405_, v_i_boxed_3409_, v_stop_boxed_3410_, v_b_3408_);
lean_dec_ref(v_as_3405_);
return v_res_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants(lean_object* v_alts_3412_, lean_object* v_invariants_3413_, lean_object* v_inlineHandled_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = lean_unsigned_to_nat(0u);
v___x_3423_ = lean_array_get_size(v_invariants_3413_);
v___x_3424_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg(v___x_3423_, v_alts_3412_, v_invariants_3413_, v___x_3422_, v_inlineHandled_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_object* v_a_3425_; lean_object* v___y_3427_; lean_object* v_size_3440_; lean_object* v_buckets_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; uint8_t v___x_3444_; 
v_a_3425_ = lean_ctor_get(v___x_3424_, 0);
lean_inc(v_a_3425_);
lean_dec_ref_known(v___x_3424_, 1);
v_size_3440_ = lean_ctor_get(v_alts_3412_, 0);
v_buckets_3441_ = lean_ctor_get(v_alts_3412_, 1);
v___x_3442_ = lean_mk_empty_array_with_capacity(v_size_3440_);
v___x_3443_ = lean_array_get_size(v_buckets_3441_);
v___x_3444_ = lean_nat_dec_lt(v___x_3422_, v___x_3443_);
if (v___x_3444_ == 0)
{
v___y_3427_ = v___x_3442_;
goto v___jp_3426_;
}
else
{
uint8_t v___x_3445_; 
v___x_3445_ = lean_nat_dec_le(v___x_3443_, v___x_3443_);
if (v___x_3445_ == 0)
{
if (v___x_3444_ == 0)
{
v___y_3427_ = v___x_3442_;
goto v___jp_3426_;
}
else
{
size_t v___x_3446_; size_t v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = ((size_t)0ULL);
v___x_3447_ = lean_usize_of_nat(v___x_3443_);
v___x_3448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3(v_buckets_3441_, v___x_3446_, v___x_3447_, v___x_3442_);
v___y_3427_ = v___x_3448_;
goto v___jp_3426_;
}
}
else
{
size_t v___x_3449_; size_t v___x_3450_; lean_object* v___x_3451_; 
v___x_3449_ = ((size_t)0ULL);
v___x_3450_ = lean_usize_of_nat(v___x_3443_);
v___x_3451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__3(v_buckets_3441_, v___x_3449_, v___x_3450_, v___x_3442_);
v___y_3427_ = v___x_3451_;
goto v___jp_3426_;
}
}
v___jp_3426_:
{
lean_object* v___x_3428_; size_t v_sz_3429_; size_t v___x_3430_; lean_object* v___x_3431_; 
v___x_3428_ = lean_box(0);
v_sz_3429_ = lean_array_size(v___y_3427_);
v___x_3430_ = ((size_t)0ULL);
v___x_3431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__1(v_a_3425_, v___y_3427_, v_sz_3429_, v___x_3430_, v___x_3428_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_);
lean_dec_ref(v___y_3427_);
lean_dec(v_a_3425_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3438_; 
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; 
v_unused_3439_ = lean_ctor_get(v___x_3431_, 0);
lean_dec(v_unused_3439_);
v___x_3433_ = v___x_3431_;
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
else
{
lean_dec(v___x_3431_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3438_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3436_; 
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3428_);
v___x_3436_ = v___x_3433_;
goto v_reusejp_3435_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3428_);
v___x_3436_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
return v___x_3436_;
}
}
}
else
{
return v___x_3431_;
}
}
}
else
{
lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3459_; 
v_a_3452_ = lean_ctor_get(v___x_3424_, 0);
v_isSharedCheck_3459_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3454_ = v___x_3424_;
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3424_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3459_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3457_; 
if (v_isShared_3455_ == 0)
{
v___x_3457_ = v___x_3454_;
goto v_reusejp_3456_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
v___x_3457_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3456_;
}
v_reusejp_3456_:
{
return v___x_3457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants___boxed(lean_object* v_alts_3460_, lean_object* v_invariants_3461_, lean_object* v_inlineHandled_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants(v_alts_3460_, v_invariants_3461_, v_inlineHandled_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec_ref(v_invariants_3461_);
lean_dec_ref(v_alts_3460_);
return v_res_3470_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4(lean_object* v_00_u03b2_3471_, lean_object* v_m_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v___x_3474_; 
v___x_3474_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___redArg(v_m_3472_, v_a_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4___boxed(lean_object* v_00_u03b2_3475_, lean_object* v_m_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4(v_00_u03b2_3475_, v_m_3476_, v_a_3477_);
lean_dec(v_a_3477_);
lean_dec_ref(v_m_3476_);
return v_res_3478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__5(lean_object* v_00_u03b2_3479_, lean_object* v_m_3480_, lean_object* v_a_3481_, lean_object* v_b_3482_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__5___redArg(v_m_3480_, v_a_3481_, v_b_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6(lean_object* v_upperBound_3484_, lean_object* v_alts_3485_, lean_object* v_invariants_3486_, lean_object* v_inst_3487_, lean_object* v_R_3488_, lean_object* v_a_3489_, lean_object* v_b_3490_, lean_object* v_c_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___redArg(v_upperBound_3484_, v_alts_3485_, v_invariants_3486_, v_a_3489_, v_b_3490_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6___boxed(lean_object* v_upperBound_3500_, lean_object* v_alts_3501_, lean_object* v_invariants_3502_, lean_object* v_inst_3503_, lean_object* v_R_3504_, lean_object* v_a_3505_, lean_object* v_b_3506_, lean_object* v_c_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__6(v_upperBound_3500_, v_alts_3501_, v_invariants_3502_, v_inst_3503_, v_R_3504_, v_a_3505_, v_b_3506_, v_c_3507_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
lean_dec(v___y_3513_);
lean_dec_ref(v___y_3512_);
lean_dec(v___y_3511_);
lean_dec_ref(v___y_3510_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v_invariants_3502_);
lean_dec_ref(v_alts_3501_);
lean_dec(v_upperBound_3500_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0(lean_object* v_ref_3516_, lean_object* v_msgData_3517_, uint8_t v_severity_3518_, uint8_t v_isSilent_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_){
_start:
{
lean_object* v___x_3527_; 
v___x_3527_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___redArg(v_ref_3516_, v_msgData_3517_, v_severity_3518_, v_isSilent_3519_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0___boxed(lean_object* v_ref_3528_, lean_object* v_msgData_3529_, lean_object* v_severity_3530_, lean_object* v_isSilent_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_){
_start:
{
uint8_t v_severity_boxed_3539_; uint8_t v_isSilent_boxed_3540_; lean_object* v_res_3541_; 
v_severity_boxed_3539_ = lean_unbox(v_severity_3530_);
v_isSilent_boxed_3540_ = lean_unbox(v_isSilent_3531_);
v_res_3541_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__0_spec__0(v_ref_3528_, v_msgData_3529_, v_severity_boxed_3539_, v_isSilent_boxed_3540_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v_ref_3528_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5(lean_object* v_00_u03b2_3542_, lean_object* v_a_3543_, lean_object* v_x_3544_){
_start:
{
lean_object* v___x_3545_; 
v___x_3545_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___redArg(v_a_3543_, v_x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5___boxed(lean_object* v_00_u03b2_3546_, lean_object* v_a_3547_, lean_object* v_x_3548_){
_start:
{
lean_object* v_res_3549_; 
v_res_3549_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants_spec__4_spec__5(v_00_u03b2_3546_, v_a_3547_, v_x_3548_);
lean_dec(v_x_3548_);
lean_dec(v_a_3547_);
return v_res_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0___redArg(lean_object* v_xs_3550_, lean_object* v_range_3551_, lean_object* v_b_3552_, lean_object* v_i_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
lean_object* v_stop_3559_; lean_object* v_step_3560_; uint8_t v___x_3561_; 
v_stop_3559_ = lean_ctor_get(v_range_3551_, 1);
v_step_3560_ = lean_ctor_get(v_range_3551_, 2);
v___x_3561_ = lean_nat_dec_lt(v_i_3553_, v_stop_3559_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; 
lean_dec(v_i_3553_);
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_b_3552_);
return v___x_3562_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = lean_array_fget_borrowed(v_xs_3550_, v_i_3553_);
lean_inc(v___y_3557_);
lean_inc_ref(v___y_3556_);
lean_inc(v___y_3555_);
lean_inc_ref(v___y_3554_);
lean_inc(v___x_3563_);
v___x_3564_ = lean_infer_type(v___x_3563_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_object* v_a_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v_a_3565_ = lean_ctor_get(v___x_3564_, 0);
lean_inc(v_a_3565_);
lean_dec_ref_known(v___x_3564_, 1);
v___x_3566_ = lean_expr_abstract_range(v_a_3565_, v_i_3553_, v_xs_3550_);
lean_dec(v_a_3565_);
v___x_3567_ = lean_array_push(v_b_3552_, v___x_3566_);
v___x_3568_ = lean_nat_add(v_i_3553_, v_step_3560_);
lean_dec(v_i_3553_);
v_b_3552_ = v___x_3567_;
v_i_3553_ = v___x_3568_;
goto _start;
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec(v_i_3553_);
lean_dec_ref(v_b_3552_);
v_a_3570_ = lean_ctor_get(v___x_3564_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3564_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3564_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0___redArg___boxed(lean_object* v_xs_3578_, lean_object* v_range_3579_, lean_object* v_b_3580_, lean_object* v_i_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0___redArg(v_xs_3578_, v_range_3579_, v_b_3580_, v_i_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec_ref(v_range_3579_);
lean_dec_ref(v_xs_3578_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__1(lean_object* v_as_3588_, size_t v_sz_3589_, size_t v_i_3590_, lean_object* v_b_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
uint8_t v___x_3597_; 
v___x_3597_ = lean_usize_dec_lt(v_i_3590_, v_sz_3589_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; 
v___x_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3598_, 0, v_b_3591_);
return v___x_3598_;
}
else
{
lean_object* v_a_3599_; lean_object* v___x_3600_; 
v_a_3599_ = lean_array_uget_borrowed(v_as_3588_, v_i_3590_);
lean_inc(v_a_3599_);
v___x_3600_ = l_Lean_Meta_Sym_mkProofInstInfo_x3f(v_a_3599_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v_a_3603_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
if (lean_obj_tag(v_a_3601_) == 1)
{
lean_object* v_val_3607_; lean_object* v___x_3608_; 
v_val_3607_ = lean_ctor_get(v_a_3601_, 0);
lean_inc(v_val_3607_);
lean_dec_ref_known(v_a_3601_, 1);
lean_inc(v_a_3599_);
v___x_3608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3608_, 0, v_a_3599_);
lean_ctor_set(v___x_3608_, 1, v_val_3607_);
lean_ctor_set(v___x_3608_, 2, v_b_3591_);
v_a_3603_ = v___x_3608_;
goto v___jp_3602_;
}
else
{
lean_dec(v_a_3601_);
v_a_3603_ = v_b_3591_;
goto v___jp_3602_;
}
v___jp_3602_:
{
size_t v___x_3604_; size_t v___x_3605_; 
v___x_3604_ = ((size_t)1ULL);
v___x_3605_ = lean_usize_add(v_i_3590_, v___x_3604_);
v_i_3590_ = v___x_3605_;
v_b_3591_ = v_a_3603_;
goto _start;
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v_b_3591_);
v_a_3609_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3600_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3600_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__1___boxed(lean_object* v_as_3617_, lean_object* v_sz_3618_, lean_object* v_i_3619_, lean_object* v_b_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
size_t v_sz_boxed_3626_; size_t v_i_boxed_3627_; lean_object* v_res_3628_; 
v_sz_boxed_3626_ = lean_unbox_usize(v_sz_3618_);
lean_dec(v_sz_3618_);
v_i_boxed_3627_ = lean_unbox_usize(v_i_3619_);
lean_dec(v_i_3619_);
v_res_3628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__1(v_as_3617_, v_sz_boxed_3626_, v_i_boxed_3627_, v_b_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec_ref(v_as_3617_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern(lean_object* v_xs_3631_, lean_object* v_e_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_){
_start:
{
lean_object* v___x_3638_; lean_object* v_varTypes_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3638_ = lean_unsigned_to_nat(0u);
v_varTypes_3639_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern___closed__0));
v___x_3640_ = lean_array_get_size(v_xs_3631_);
v___x_3641_ = lean_unsigned_to_nat(1u);
v___x_3642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3638_);
lean_ctor_set(v___x_3642_, 1, v___x_3640_);
lean_ctor_set(v___x_3642_, 2, v___x_3641_);
v___x_3643_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0___redArg(v_xs_3631_, v___x_3642_, v_varTypes_3639_, v___x_3638_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_);
lean_dec_ref_known(v___x_3642_, 3);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v_pattern_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; size_t v_sz_3648_; size_t v___x_3649_; lean_object* v___x_3650_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref_known(v___x_3643_, 1);
v_pattern_3645_ = lean_expr_abstract(v_e_3632_, v_xs_3631_);
v___x_3646_ = lean_box(0);
lean_inc_ref(v_pattern_3645_);
v___x_3647_ = l_Lean_Expr_getUsedConstants(v_pattern_3645_);
v_sz_3648_ = lean_array_size(v___x_3647_);
v___x_3649_ = ((size_t)0ULL);
v___x_3650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__1(v___x_3647_, v_sz_3648_, v___x_3649_, v___x_3646_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_);
lean_dec_ref(v___x_3647_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___x_3650_, 1);
v___x_3652_ = l_Lean_Meta_Sym_mkProofInstArgInfo_x3f(v_xs_3631_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3663_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3655_ = v___x_3652_;
v_isShared_3656_ = v_isSharedCheck_3663_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_a_3653_);
lean_dec(v___x_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3663_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3657_ = lean_box(0);
v___x_3658_ = lean_box(0);
v___x_3659_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3657_);
lean_ctor_set(v___x_3659_, 1, v_a_3644_);
lean_ctor_set(v___x_3659_, 2, v_a_3653_);
lean_ctor_set(v___x_3659_, 3, v_pattern_3645_);
lean_ctor_set(v___x_3659_, 4, v_a_3651_);
lean_ctor_set(v___x_3659_, 5, v___x_3658_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v___x_3659_);
v___x_3661_ = v___x_3655_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v_a_3651_);
lean_dec_ref(v_pattern_3645_);
lean_dec(v_a_3644_);
v_a_3664_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3652_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3652_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec_ref(v_pattern_3645_);
lean_dec(v_a_3644_);
v_a_3672_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3650_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3650_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
v_a_3680_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3643_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3643_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern___boxed(lean_object* v_xs_3688_, lean_object* v_e_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern(v_xs_3688_, v_e_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_);
lean_dec(v_a_3693_);
lean_dec_ref(v_a_3692_);
lean_dec(v_a_3691_);
lean_dec_ref(v_a_3690_);
lean_dec_ref(v_e_3689_);
lean_dec_ref(v_xs_3688_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0(lean_object* v_xs_3696_, lean_object* v_range_3697_, lean_object* v_b_3698_, lean_object* v_i_3699_, lean_object* v_hs_3700_, lean_object* v_hl_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
lean_object* v___x_3707_; 
v___x_3707_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0___redArg(v_xs_3696_, v_range_3697_, v_b_3698_, v_i_3699_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0___boxed(lean_object* v_xs_3708_, lean_object* v_range_3709_, lean_object* v_b_3710_, lean_object* v_i_3711_, lean_object* v_hs_3712_, lean_object* v_hl_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern_spec__0(v_xs_3708_, v_range_3709_, v_b_3710_, v_i_3711_, v_hs_3712_, v_hl_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec_ref(v_range_3709_);
lean_dec_ref(v_xs_3708_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0___redArg(lean_object* v_e_3720_, lean_object* v___y_3721_){
_start:
{
uint8_t v___x_3723_; 
v___x_3723_ = l_Lean_Expr_hasMVar(v_e_3720_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v_e_3720_);
return v___x_3724_;
}
else
{
lean_object* v___x_3725_; lean_object* v_mctx_3726_; lean_object* v___x_3727_; lean_object* v_fst_3728_; lean_object* v_snd_3729_; lean_object* v___x_3730_; lean_object* v_cache_3731_; lean_object* v_zetaDeltaFVarIds_3732_; lean_object* v_postponed_3733_; lean_object* v_diag_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3743_; 
v___x_3725_ = lean_st_ref_get(v___y_3721_);
v_mctx_3726_ = lean_ctor_get(v___x_3725_, 0);
lean_inc_ref(v_mctx_3726_);
lean_dec(v___x_3725_);
v___x_3727_ = l_Lean_instantiateMVarsCore(v_mctx_3726_, v_e_3720_);
v_fst_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_fst_3728_);
v_snd_3729_ = lean_ctor_get(v___x_3727_, 1);
lean_inc(v_snd_3729_);
lean_dec_ref(v___x_3727_);
v___x_3730_ = lean_st_ref_take(v___y_3721_);
v_cache_3731_ = lean_ctor_get(v___x_3730_, 1);
v_zetaDeltaFVarIds_3732_ = lean_ctor_get(v___x_3730_, 2);
v_postponed_3733_ = lean_ctor_get(v___x_3730_, 3);
v_diag_3734_ = lean_ctor_get(v___x_3730_, 4);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3743_ == 0)
{
lean_object* v_unused_3744_; 
v_unused_3744_ = lean_ctor_get(v___x_3730_, 0);
lean_dec(v_unused_3744_);
v___x_3736_ = v___x_3730_;
v_isShared_3737_ = v_isSharedCheck_3743_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_diag_3734_);
lean_inc(v_postponed_3733_);
lean_inc(v_zetaDeltaFVarIds_3732_);
lean_inc(v_cache_3731_);
lean_dec(v___x_3730_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3743_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v_snd_3729_);
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_snd_3729_);
lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_cache_3731_);
lean_ctor_set(v_reuseFailAlloc_3742_, 2, v_zetaDeltaFVarIds_3732_);
lean_ctor_set(v_reuseFailAlloc_3742_, 3, v_postponed_3733_);
lean_ctor_set(v_reuseFailAlloc_3742_, 4, v_diag_3734_);
v___x_3739_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = lean_st_ref_set(v___y_3721_, v___x_3739_);
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_fst_3728_);
return v___x_3741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0___redArg___boxed(lean_object* v_e_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0___redArg(v_e_3745_, v___y_3746_);
lean_dec(v___y_3746_);
return v_res_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0(lean_object* v_e_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_){
_start:
{
lean_object* v___x_3757_; 
v___x_3757_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0___redArg(v_e_3749_, v___y_3753_);
return v___x_3757_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0___boxed(lean_object* v_e_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_){
_start:
{
lean_object* v_res_3766_; 
v_res_3766_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0(v_e_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
lean_dec(v___y_3764_);
lean_dec_ref(v___y_3763_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
return v_res_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__2___redArg(lean_object* v_a_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_){
_start:
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
return v___x_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__2___redArg___boxed(lean_object* v_a_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__2___redArg(v_a_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__2(lean_object* v_00_u03b1_3785_, lean_object* v_a_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v_a_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__2___boxed(lean_object* v_00_u03b1_3795_, lean_object* v_a_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_Lean_Elab_Term_withoutErrToSorry___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__2(v_00_u03b1_3795_, v_a_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
lean_dec(v___y_3802_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3800_);
lean_dec_ref(v___y_3799_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3___redArg(lean_object* v_lctx_3805_, lean_object* v_localInsts_3806_, lean_object* v_x_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_){
_start:
{
lean_object* v___x_3813_; 
v___x_3813_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3805_, v_localInsts_3806_, v_x_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3813_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3813_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
v_a_3822_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3813_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3813_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3___redArg___boxed(lean_object* v_lctx_3830_, lean_object* v_localInsts_3831_, lean_object* v_x_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3___redArg(v_lctx_3830_, v_localInsts_3831_, v_x_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3(lean_object* v_00_u03b1_3839_, lean_object* v_lctx_3840_, lean_object* v_localInsts_3841_, lean_object* v_x_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
lean_object* v___x_3848_; 
v___x_3848_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3___redArg(v_lctx_3840_, v_localInsts_3841_, v_x_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_);
return v___x_3848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3___boxed(lean_object* v_00_u03b1_3849_, lean_object* v_lctx_3850_, lean_object* v_localInsts_3851_, lean_object* v_x_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3(v_00_u03b1_3849_, v_lctx_3850_, v_localInsts_3851_, v_x_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3855_);
lean_dec(v___y_3854_);
lean_dec_ref(v___y_3853_);
return v_res_3858_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__0(lean_object* v_x_3859_){
_start:
{
uint8_t v___x_3860_; 
v___x_3860_ = 0;
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__0___boxed(lean_object* v_x_3861_){
_start:
{
uint8_t v_res_3862_; lean_object* v_r_3863_; 
v_res_3862_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__0(v_x_3861_);
lean_dec(v_x_3861_);
v_r_3863_ = lean_box(v_res_3862_);
return v_r_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__1(size_t v_sz_3864_, size_t v_i_3865_, lean_object* v_bs_3866_){
_start:
{
uint8_t v___x_3867_; 
v___x_3867_ = lean_usize_dec_lt(v_i_3865_, v_sz_3864_);
if (v___x_3867_ == 0)
{
return v_bs_3866_;
}
else
{
lean_object* v_v_3868_; lean_object* v___x_3869_; lean_object* v_bs_x27_3870_; lean_object* v___x_3871_; size_t v___x_3872_; size_t v___x_3873_; lean_object* v___x_3874_; 
v_v_3868_ = lean_array_uget(v_bs_3866_, v_i_3865_);
v___x_3869_ = lean_unsigned_to_nat(0u);
v_bs_x27_3870_ = lean_array_uset(v_bs_3866_, v_i_3865_, v___x_3869_);
v___x_3871_ = l_Lean_Expr_mvar___override(v_v_3868_);
v___x_3872_ = ((size_t)1ULL);
v___x_3873_ = lean_usize_add(v_i_3865_, v___x_3872_);
v___x_3874_ = lean_array_uset(v_bs_x27_3870_, v_i_3865_, v___x_3871_);
v_i_3865_ = v___x_3873_;
v_bs_3866_ = v___x_3874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__1___boxed(lean_object* v_sz_3876_, lean_object* v_i_3877_, lean_object* v_bs_3878_){
_start:
{
size_t v_sz_boxed_3879_; size_t v_i_boxed_3880_; lean_object* v_res_3881_; 
v_sz_boxed_3879_ = lean_unbox_usize(v_sz_3876_);
lean_dec(v_sz_3876_);
v_i_boxed_3880_ = lean_unbox_usize(v_i_3877_);
lean_dec(v_i_3877_);
v_res_3881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__1(v_sz_boxed_3879_, v_i_boxed_3880_, v_bs_3878_);
return v_res_3881_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__0(void){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3882_ = lean_box(0);
v___x_3883_ = lean_unsigned_to_nat(16u);
v___x_3884_ = lean_mk_array(v___x_3883_, v___x_3882_);
return v___x_3884_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3885_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__0, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__0_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__0);
v___x_3886_ = lean_unsigned_to_nat(0u);
v___x_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
lean_ctor_set(v___x_3887_, 1, v___x_3885_);
return v___x_3887_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3890_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__2));
v___x_3891_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__1, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__1_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__1);
v___x_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
lean_ctor_set(v___x_3892_, 1, v___x_3890_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1(uint8_t v___x_3893_, lean_object* v___x_3894_, lean_object* v_m_3895_, lean_object* v_p_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Lean_Meta_mkFreshTypeMVar(v___x_3893_, v___x_3894_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; lean_object* v___x_3909_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
v___x_3906_ = l_Lean_Expr_app___override(v_m_3895_, v_a_3905_);
v___x_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
v___x_3908_ = 1;
v___x_3909_ = l_Lean_Elab_Term_elabTerm(v_p_3896_, v___x_3907_, v___x_3908_, v___x_3908_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; lean_object* v_a_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v_result_3915_; size_t v_sz_3916_; size_t v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__0___redArg(v_a_3910_, v___y_3900_);
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc_n(v_a_3912_, 2);
lean_dec_ref(v___x_3911_);
v___x_3913_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__3);
v___x_3914_ = l_Lean_Expr_collectMVars(v___x_3913_, v_a_3912_);
v_result_3915_ = lean_ctor_get(v___x_3914_, 1);
lean_inc_ref(v_result_3915_);
lean_dec_ref(v___x_3914_);
v_sz_3916_ = lean_array_size(v_result_3915_);
v___x_3917_ = ((size_t)0ULL);
v___x_3918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__1(v_sz_3916_, v___x_3917_, v_result_3915_);
v___x_3919_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_mkUntilPattern(v___x_3918_, v_a_3912_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
lean_dec(v_a_3912_);
lean_dec_ref(v___x_3918_);
return v___x_3919_;
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
v_a_3920_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3909_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3909_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec(v_p_3896_);
lean_dec_ref(v_m_3895_);
v_a_3928_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3904_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3904_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___boxed(lean_object* v___x_3936_, lean_object* v___x_3937_, lean_object* v_m_3938_, lean_object* v_p_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
uint8_t v___x_3884__boxed_3947_; lean_object* v_res_3948_; 
v___x_3884__boxed_3947_ = lean_unbox(v___x_3936_);
v_res_3948_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1(v___x_3884__boxed_3947_, v___x_3937_, v_m_3938_, v_p_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
return v_res_3948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__2(lean_object* v_p_3949_, lean_object* v___f_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
lean_object* v_fileName_3958_; lean_object* v_fileMap_3959_; lean_object* v_options_3960_; lean_object* v_currRecDepth_3961_; lean_object* v_maxRecDepth_3962_; lean_object* v_ref_3963_; lean_object* v_currNamespace_3964_; lean_object* v_openDecls_3965_; lean_object* v_initHeartbeats_3966_; lean_object* v_maxHeartbeats_3967_; lean_object* v_quotContext_3968_; lean_object* v_currMacroScope_3969_; uint8_t v_diag_3970_; lean_object* v_cancelTk_x3f_3971_; uint8_t v_suppressElabErrors_3972_; lean_object* v_inheritedTraceOptions_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_4008_; 
v_fileName_3958_ = lean_ctor_get(v___y_3955_, 0);
v_fileMap_3959_ = lean_ctor_get(v___y_3955_, 1);
v_options_3960_ = lean_ctor_get(v___y_3955_, 2);
v_currRecDepth_3961_ = lean_ctor_get(v___y_3955_, 3);
v_maxRecDepth_3962_ = lean_ctor_get(v___y_3955_, 4);
v_ref_3963_ = lean_ctor_get(v___y_3955_, 5);
v_currNamespace_3964_ = lean_ctor_get(v___y_3955_, 6);
v_openDecls_3965_ = lean_ctor_get(v___y_3955_, 7);
v_initHeartbeats_3966_ = lean_ctor_get(v___y_3955_, 8);
v_maxHeartbeats_3967_ = lean_ctor_get(v___y_3955_, 9);
v_quotContext_3968_ = lean_ctor_get(v___y_3955_, 10);
v_currMacroScope_3969_ = lean_ctor_get(v___y_3955_, 11);
v_diag_3970_ = lean_ctor_get_uint8(v___y_3955_, sizeof(void*)*14);
v_cancelTk_x3f_3971_ = lean_ctor_get(v___y_3955_, 12);
v_suppressElabErrors_3972_ = lean_ctor_get_uint8(v___y_3955_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3973_ = lean_ctor_get(v___y_3955_, 13);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___y_3955_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_3975_ = v___y_3955_;
v_isShared_3976_ = v_isSharedCheck_4008_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_inheritedTraceOptions_3973_);
lean_inc(v_cancelTk_x3f_3971_);
lean_inc(v_currMacroScope_3969_);
lean_inc(v_quotContext_3968_);
lean_inc(v_maxHeartbeats_3967_);
lean_inc(v_initHeartbeats_3966_);
lean_inc(v_openDecls_3965_);
lean_inc(v_currNamespace_3964_);
lean_inc(v_ref_3963_);
lean_inc(v_maxRecDepth_3962_);
lean_inc(v_currRecDepth_3961_);
lean_inc(v_options_3960_);
lean_inc(v_fileMap_3959_);
lean_inc(v_fileName_3958_);
lean_dec(v___y_3955_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_4008_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v_declName_x3f_3977_; lean_object* v_macroStack_3978_; uint8_t v_mayPostpone_3979_; uint8_t v_errToSorry_3980_; lean_object* v_autoBoundImplicitContext_3981_; lean_object* v_autoBoundImplicitForbidden_3982_; lean_object* v_sectionVars_3983_; lean_object* v_sectionFVars_3984_; uint8_t v_implicitLambda_3985_; uint8_t v_heedElabAsElim_3986_; uint8_t v_isNoncomputableSection_3987_; uint8_t v_isMetaSection_3988_; uint8_t v_inPattern_3989_; lean_object* v_tacSnap_x3f_3990_; uint8_t v_saveRecAppSyntax_3991_; uint8_t v_holesAsSyntheticOpaque_3992_; uint8_t v_checkDeprecated_3993_; lean_object* v_fixedTermElabs_3994_; lean_object* v___x_3996_; uint8_t v_isShared_3997_; uint8_t v_isSharedCheck_4007_; 
v_declName_x3f_3977_ = lean_ctor_get(v___y_3951_, 0);
v_macroStack_3978_ = lean_ctor_get(v___y_3951_, 1);
v_mayPostpone_3979_ = lean_ctor_get_uint8(v___y_3951_, sizeof(void*)*8);
v_errToSorry_3980_ = lean_ctor_get_uint8(v___y_3951_, sizeof(void*)*8 + 1);
v_autoBoundImplicitContext_3981_ = lean_ctor_get(v___y_3951_, 2);
v_autoBoundImplicitForbidden_3982_ = lean_ctor_get(v___y_3951_, 3);
v_sectionVars_3983_ = lean_ctor_get(v___y_3951_, 4);
v_sectionFVars_3984_ = lean_ctor_get(v___y_3951_, 5);
v_implicitLambda_3985_ = lean_ctor_get_uint8(v___y_3951_, sizeof(void*)*8 + 2);
v_heedElabAsElim_3986_ = lean_ctor_get_uint8(v___y_3951_, sizeof(void*)*8 + 3);
v_isNoncomputableSection_3987_ = lean_ctor_get_uint8(v___y_3951_, sizeof(void*)*8 + 4);
v_isMetaSection_3988_ = lean_ctor_get_uint8(v___y_3951_, sizeof(void*)*8 + 5);
v_inPattern_3989_ = lean_ctor_get_uint8(v___y_3951_, sizeof(void*)*8 + 7);
v_tacSnap_x3f_3990_ = lean_ctor_get(v___y_3951_, 6);
v_saveRecAppSyntax_3991_ = lean_ctor_get_uint8(v___y_3951_, sizeof(void*)*8 + 8);
v_holesAsSyntheticOpaque_3992_ = lean_ctor_get_uint8(v___y_3951_, sizeof(void*)*8 + 9);
v_checkDeprecated_3993_ = lean_ctor_get_uint8(v___y_3951_, sizeof(void*)*8 + 10);
v_fixedTermElabs_3994_ = lean_ctor_get(v___y_3951_, 7);
v_isSharedCheck_4007_ = !lean_is_exclusive(v___y_3951_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3996_ = v___y_3951_;
v_isShared_3997_ = v_isSharedCheck_4007_;
goto v_resetjp_3995_;
}
else
{
lean_inc(v_fixedTermElabs_3994_);
lean_inc(v_tacSnap_x3f_3990_);
lean_inc(v_sectionFVars_3984_);
lean_inc(v_sectionVars_3983_);
lean_inc(v_autoBoundImplicitForbidden_3982_);
lean_inc(v_autoBoundImplicitContext_3981_);
lean_inc(v_macroStack_3978_);
lean_inc(v_declName_x3f_3977_);
lean_dec(v___y_3951_);
v___x_3996_ = lean_box(0);
v_isShared_3997_ = v_isSharedCheck_4007_;
goto v_resetjp_3995_;
}
v_resetjp_3995_:
{
lean_object* v_ref_3998_; lean_object* v___x_4000_; 
v_ref_3998_ = l_Lean_replaceRef(v_p_3949_, v_ref_3963_);
lean_dec(v_ref_3963_);
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 5, v_ref_3998_);
v___x_4000_ = v___x_3975_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_fileName_3958_);
lean_ctor_set(v_reuseFailAlloc_4006_, 1, v_fileMap_3959_);
lean_ctor_set(v_reuseFailAlloc_4006_, 2, v_options_3960_);
lean_ctor_set(v_reuseFailAlloc_4006_, 3, v_currRecDepth_3961_);
lean_ctor_set(v_reuseFailAlloc_4006_, 4, v_maxRecDepth_3962_);
lean_ctor_set(v_reuseFailAlloc_4006_, 5, v_ref_3998_);
lean_ctor_set(v_reuseFailAlloc_4006_, 6, v_currNamespace_3964_);
lean_ctor_set(v_reuseFailAlloc_4006_, 7, v_openDecls_3965_);
lean_ctor_set(v_reuseFailAlloc_4006_, 8, v_initHeartbeats_3966_);
lean_ctor_set(v_reuseFailAlloc_4006_, 9, v_maxHeartbeats_3967_);
lean_ctor_set(v_reuseFailAlloc_4006_, 10, v_quotContext_3968_);
lean_ctor_set(v_reuseFailAlloc_4006_, 11, v_currMacroScope_3969_);
lean_ctor_set(v_reuseFailAlloc_4006_, 12, v_cancelTk_x3f_3971_);
lean_ctor_set(v_reuseFailAlloc_4006_, 13, v_inheritedTraceOptions_3973_);
lean_ctor_set_uint8(v_reuseFailAlloc_4006_, sizeof(void*)*14, v_diag_3970_);
lean_ctor_set_uint8(v_reuseFailAlloc_4006_, sizeof(void*)*14 + 1, v_suppressElabErrors_3972_);
v___x_4000_ = v_reuseFailAlloc_4006_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
uint8_t v___x_4001_; lean_object* v___x_4003_; 
v___x_4001_ = 1;
if (v_isShared_3997_ == 0)
{
v___x_4003_ = v___x_3996_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_declName_x3f_3977_);
lean_ctor_set(v_reuseFailAlloc_4005_, 1, v_macroStack_3978_);
lean_ctor_set(v_reuseFailAlloc_4005_, 2, v_autoBoundImplicitContext_3981_);
lean_ctor_set(v_reuseFailAlloc_4005_, 3, v_autoBoundImplicitForbidden_3982_);
lean_ctor_set(v_reuseFailAlloc_4005_, 4, v_sectionVars_3983_);
lean_ctor_set(v_reuseFailAlloc_4005_, 5, v_sectionFVars_3984_);
lean_ctor_set(v_reuseFailAlloc_4005_, 6, v_tacSnap_x3f_3990_);
lean_ctor_set(v_reuseFailAlloc_4005_, 7, v_fixedTermElabs_3994_);
lean_ctor_set_uint8(v_reuseFailAlloc_4005_, sizeof(void*)*8, v_mayPostpone_3979_);
lean_ctor_set_uint8(v_reuseFailAlloc_4005_, sizeof(void*)*8 + 1, v_errToSorry_3980_);
lean_ctor_set_uint8(v_reuseFailAlloc_4005_, sizeof(void*)*8 + 2, v_implicitLambda_3985_);
lean_ctor_set_uint8(v_reuseFailAlloc_4005_, sizeof(void*)*8 + 3, v_heedElabAsElim_3986_);
lean_ctor_set_uint8(v_reuseFailAlloc_4005_, sizeof(void*)*8 + 4, v_isNoncomputableSection_3987_);
lean_ctor_set_uint8(v_reuseFailAlloc_4005_, sizeof(void*)*8 + 5, v_isMetaSection_3988_);
lean_ctor_set_uint8(v_reuseFailAlloc_4005_, sizeof(void*)*8 + 7, v_inPattern_3989_);
lean_ctor_set_uint8(v_reuseFailAlloc_4005_, sizeof(void*)*8 + 8, v_saveRecAppSyntax_3991_);
lean_ctor_set_uint8(v_reuseFailAlloc_4005_, sizeof(void*)*8 + 9, v_holesAsSyntheticOpaque_3992_);
lean_ctor_set_uint8(v_reuseFailAlloc_4005_, sizeof(void*)*8 + 10, v_checkDeprecated_3993_);
v___x_4003_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
lean_object* v___x_4004_; 
lean_ctor_set_uint8(v___x_4003_, sizeof(void*)*8 + 6, v___x_4001_);
v___x_4004_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(v___f_3950_, v___x_4003_, v___y_3952_, v___y_3953_, v___y_3954_, v___x_4000_, v___y_3956_);
lean_dec_ref(v___x_4000_);
lean_dec_ref(v___x_4003_);
return v___x_4004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__2___boxed(lean_object* v_p_4009_, lean_object* v___f_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__2(v_p_4009_, v___f_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec(v_p_4009_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__3(lean_object* v___x_4019_, lean_object* v___x_4020_, lean_object* v___x_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v___x_4027_; 
v___x_4027_ = l_Lean_Elab_Term_TermElabM_run___redArg(v___x_4019_, v___x_4020_, v___x_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4036_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4036_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4036_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
lean_object* v_fst_4032_; lean_object* v___x_4034_; 
v_fst_4032_ = lean_ctor_get(v_a_4028_, 0);
lean_inc(v_fst_4032_);
lean_dec(v_a_4028_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 0, v_fst_4032_);
v___x_4034_ = v___x_4030_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_fst_4032_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
v_a_4037_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4027_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4027_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__3___boxed(lean_object* v___x_4045_, lean_object* v___x_4046_, lean_object* v___x_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__3(v___x_4045_, v___x_4046_, v___x_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4(lean_object* v_p_4059_, lean_object* v___f_4060_, lean_object* v_lctx_4061_, lean_object* v_localInstances_4062_, lean_object* v_m_4063_, lean_object* v___y_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_){
_start:
{
uint8_t v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___f_4072_; lean_object* v___f_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___f_4083_; lean_object* v___x_4084_; 
v___x_4069_ = 0;
v___x_4070_ = lean_box(0);
v___x_4071_ = lean_box(v___x_4069_);
lean_inc(v_p_4059_);
v___f_4072_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___boxed), 11, 4);
lean_closure_set(v___f_4072_, 0, v___x_4071_);
lean_closure_set(v___f_4072_, 1, v___x_4070_);
lean_closure_set(v___f_4072_, 2, v_m_4063_);
lean_closure_set(v___f_4072_, 3, v_p_4059_);
v___f_4073_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__2___boxed), 9, 2);
lean_closure_set(v___f_4073_, 0, v_p_4059_);
lean_closure_set(v___f_4073_, 1, v___f_4072_);
v___x_4074_ = lean_alloc_closure((void*)(l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___boxed), 9, 2);
lean_closure_set(v___x_4074_, 0, lean_box(0));
lean_closure_set(v___x_4074_, 1, v___f_4073_);
v___x_4075_ = lean_box(0);
v___x_4076_ = lean_box(0);
v___x_4077_ = 1;
v___x_4078_ = lean_box(1);
v___x_4079_ = 0;
v___x_4080_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___closed__0));
v___x_4081_ = lean_alloc_ctor(0, 8, 11);
lean_ctor_set(v___x_4081_, 0, v___x_4075_);
lean_ctor_set(v___x_4081_, 1, v___x_4076_);
lean_ctor_set(v___x_4081_, 2, v___x_4075_);
lean_ctor_set(v___x_4081_, 3, v___f_4060_);
lean_ctor_set(v___x_4081_, 4, v___x_4078_);
lean_ctor_set(v___x_4081_, 5, v___x_4078_);
lean_ctor_set(v___x_4081_, 6, v___x_4075_);
lean_ctor_set(v___x_4081_, 7, v___x_4080_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8, v___x_4077_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8 + 1, v___x_4077_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8 + 2, v___x_4077_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8 + 3, v___x_4077_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8 + 4, v___x_4079_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8 + 5, v___x_4079_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8 + 6, v___x_4079_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8 + 7, v___x_4079_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8 + 8, v___x_4077_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8 + 9, v___x_4079_);
lean_ctor_set_uint8(v___x_4081_, sizeof(void*)*8 + 10, v___x_4077_);
v___x_4082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___closed__1));
v___f_4083_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__3___boxed), 8, 3);
lean_closure_set(v___f_4083_, 0, v___x_4074_);
lean_closure_set(v___f_4083_, 1, v___x_4081_);
lean_closure_set(v___f_4083_, 2, v___x_4082_);
v___x_4084_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern_spec__3___redArg(v_lctx_4061_, v_localInstances_4062_, v___f_4083_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___boxed(lean_object* v_p_4085_, lean_object* v___f_4086_, lean_object* v_lctx_4087_, lean_object* v_localInstances_4088_, lean_object* v_m_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4(v_p_4085_, v___f_4086_, v_lctx_4087_, v_localInstances_4088_, v_m_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg(lean_object* v_p_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_lctx_4100_; lean_object* v_localInstances_4101_; lean_object* v___f_4102_; lean_object* v___f_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v_lctx_4100_ = lean_ctor_get(v_a_4098_, 2);
v_localInstances_4101_ = lean_ctor_get(v_a_4098_, 3);
v___f_4102_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___closed__0));
lean_inc_ref(v_localInstances_4101_);
lean_inc_ref(v_lctx_4100_);
v___f_4103_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__4___boxed), 10, 4);
lean_closure_set(v___f_4103_, 0, v_p_4097_);
lean_closure_set(v___f_4103_, 1, v___f_4102_);
lean_closure_set(v___f_4103_, 2, v_lctx_4100_);
lean_closure_set(v___f_4103_, 3, v_localInstances_4101_);
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___f_4103_);
v___x_4105_ = lean_st_mk_ref(v___x_4104_);
v___x_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
return v___x_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___boxed(lean_object* v_p_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg(v_p_4107_, v_a_4108_);
lean_dec_ref(v_a_4108_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern(lean_object* v_p_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg(v_p_4111_, v_a_4114_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___boxed(lean_object* v_p_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern(v_p_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_, v_a_4126_);
lean_dec(v_a_4126_);
lean_dec_ref(v_a_4125_);
lean_dec(v_a_4124_);
lean_dec_ref(v_a_4123_);
lean_dec(v_a_4122_);
lean_dec_ref(v_a_4121_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___lam__0(lean_object* v_x_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_){
_start:
{
lean_object* v___x_4137_; 
lean_inc(v___y_4131_);
lean_inc_ref(v___y_4130_);
v___x_4137_ = lean_apply_7(v_x_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, lean_box(0));
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___lam__0___boxed(lean_object* v_x_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___lam__0(v_x_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg(lean_object* v_mvarId_4147_, lean_object* v_x_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v___f_4156_; lean_object* v___x_4157_; 
lean_inc(v___y_4150_);
lean_inc_ref(v___y_4149_);
v___f_4156_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4156_, 0, v_x_4148_);
lean_closure_set(v___f_4156_, 1, v___y_4149_);
lean_closure_set(v___f_4156_, 2, v___y_4150_);
v___x_4157_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4147_, v___f_4156_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
if (lean_obj_tag(v___x_4157_) == 0)
{
return v___x_4157_;
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4157_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4157_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg___boxed(lean_object* v_mvarId_4166_, lean_object* v_x_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg(v_mvarId_4166_, v_x_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1(lean_object* v_00_u03b1_4176_, lean_object* v_mvarId_4177_, lean_object* v_x_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
lean_object* v___x_4186_; 
v___x_4186_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg(v_mvarId_4177_, v_x_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___boxed(lean_object* v_00_u03b1_4187_, lean_object* v_mvarId_4188_, lean_object* v_x_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1(v_00_u03b1_4187_, v_mvarId_4188_, v_x_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg(lean_object* v_ref_4198_, lean_object* v_msgData_4199_, uint8_t v_severity_4200_, uint8_t v_isSilent_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4211_; uint8_t v___y_4212_; uint8_t v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4244_; uint8_t v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; uint8_t v___y_4248_; lean_object* v___y_4249_; uint8_t v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4269_; uint8_t v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; uint8_t v___y_4274_; uint8_t v___y_4275_; lean_object* v___y_4276_; lean_object* v___y_4280_; uint8_t v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; uint8_t v___y_4285_; uint8_t v___y_4286_; uint8_t v___x_4291_; lean_object* v___y_4293_; uint8_t v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; uint8_t v___y_4298_; uint8_t v___y_4299_; uint8_t v___y_4301_; uint8_t v___x_4316_; 
v___x_4291_ = 2;
v___x_4316_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4200_, v___x_4291_);
if (v___x_4316_ == 0)
{
v___y_4301_ = v___x_4316_;
goto v___jp_4300_;
}
else
{
uint8_t v___x_4317_; 
lean_inc_ref(v_msgData_4199_);
v___x_4317_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4199_);
v___y_4301_ = v___x_4317_;
goto v___jp_4300_;
}
v___jp_4207_:
{
lean_object* v___x_4217_; lean_object* v_currNamespace_4218_; lean_object* v_openDecls_4219_; lean_object* v_env_4220_; lean_object* v_nextMacroScope_4221_; lean_object* v_ngen_4222_; lean_object* v_auxDeclNGen_4223_; lean_object* v_traceState_4224_; lean_object* v_cache_4225_; lean_object* v_messages_4226_; lean_object* v_infoState_4227_; lean_object* v_snapshotTasks_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4242_; 
v___x_4217_ = lean_st_ref_take(v___y_4216_);
v_currNamespace_4218_ = lean_ctor_get(v___y_4215_, 6);
v_openDecls_4219_ = lean_ctor_get(v___y_4215_, 7);
v_env_4220_ = lean_ctor_get(v___x_4217_, 0);
v_nextMacroScope_4221_ = lean_ctor_get(v___x_4217_, 1);
v_ngen_4222_ = lean_ctor_get(v___x_4217_, 2);
v_auxDeclNGen_4223_ = lean_ctor_get(v___x_4217_, 3);
v_traceState_4224_ = lean_ctor_get(v___x_4217_, 4);
v_cache_4225_ = lean_ctor_get(v___x_4217_, 5);
v_messages_4226_ = lean_ctor_get(v___x_4217_, 6);
v_infoState_4227_ = lean_ctor_get(v___x_4217_, 7);
v_snapshotTasks_4228_ = lean_ctor_get(v___x_4217_, 8);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4230_ = v___x_4217_;
v_isShared_4231_ = v_isSharedCheck_4242_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_snapshotTasks_4228_);
lean_inc(v_infoState_4227_);
lean_inc(v_messages_4226_);
lean_inc(v_cache_4225_);
lean_inc(v_traceState_4224_);
lean_inc(v_auxDeclNGen_4223_);
lean_inc(v_ngen_4222_);
lean_inc(v_nextMacroScope_4221_);
lean_inc(v_env_4220_);
lean_dec(v___x_4217_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4242_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4237_; 
lean_inc(v_openDecls_4219_);
lean_inc(v_currNamespace_4218_);
v___x_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4232_, 0, v_currNamespace_4218_);
lean_ctor_set(v___x_4232_, 1, v_openDecls_4219_);
v___x_4233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4232_);
lean_ctor_set(v___x_4233_, 1, v___y_4209_);
lean_inc_ref(v___y_4208_);
lean_inc_ref(v___y_4210_);
v___x_4234_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4234_, 0, v___y_4210_);
lean_ctor_set(v___x_4234_, 1, v___y_4214_);
lean_ctor_set(v___x_4234_, 2, v___y_4211_);
lean_ctor_set(v___x_4234_, 3, v___y_4208_);
lean_ctor_set(v___x_4234_, 4, v___x_4233_);
lean_ctor_set_uint8(v___x_4234_, sizeof(void*)*5, v___y_4213_);
lean_ctor_set_uint8(v___x_4234_, sizeof(void*)*5 + 1, v___y_4212_);
lean_ctor_set_uint8(v___x_4234_, sizeof(void*)*5 + 2, v_isSilent_4201_);
v___x_4235_ = l_Lean_MessageLog_add(v___x_4234_, v_messages_4226_);
if (v_isShared_4231_ == 0)
{
lean_ctor_set(v___x_4230_, 6, v___x_4235_);
v___x_4237_ = v___x_4230_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_env_4220_);
lean_ctor_set(v_reuseFailAlloc_4241_, 1, v_nextMacroScope_4221_);
lean_ctor_set(v_reuseFailAlloc_4241_, 2, v_ngen_4222_);
lean_ctor_set(v_reuseFailAlloc_4241_, 3, v_auxDeclNGen_4223_);
lean_ctor_set(v_reuseFailAlloc_4241_, 4, v_traceState_4224_);
lean_ctor_set(v_reuseFailAlloc_4241_, 5, v_cache_4225_);
lean_ctor_set(v_reuseFailAlloc_4241_, 6, v___x_4235_);
lean_ctor_set(v_reuseFailAlloc_4241_, 7, v_infoState_4227_);
lean_ctor_set(v_reuseFailAlloc_4241_, 8, v_snapshotTasks_4228_);
v___x_4237_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4238_ = lean_st_ref_set(v___y_4216_, v___x_4237_);
v___x_4239_ = lean_box(0);
v___x_4240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4240_, 0, v___x_4239_);
return v___x_4240_;
}
}
}
v___jp_4243_:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v_a_4254_; lean_object* v___x_4256_; uint8_t v_isShared_4257_; uint8_t v_isSharedCheck_4267_; 
v___x_4252_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4199_);
v___x_4253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v___x_4252_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4256_ = v___x_4253_;
v_isShared_4257_ = v_isSharedCheck_4267_;
goto v_resetjp_4255_;
}
else
{
lean_inc(v_a_4254_);
lean_dec(v___x_4253_);
v___x_4256_ = lean_box(0);
v_isShared_4257_ = v_isSharedCheck_4267_;
goto v_resetjp_4255_;
}
v_resetjp_4255_:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
lean_inc_ref_n(v___y_4249_, 2);
v___x_4258_ = l_Lean_FileMap_toPosition(v___y_4249_, v___y_4246_);
lean_dec(v___y_4246_);
v___x_4259_ = l_Lean_FileMap_toPosition(v___y_4249_, v___y_4251_);
lean_dec(v___y_4251_);
v___x_4260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4259_);
v___x_4261_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___closed__0));
if (v___y_4245_ == 0)
{
lean_del_object(v___x_4256_);
lean_dec_ref(v___y_4244_);
v___y_4208_ = v___x_4261_;
v___y_4209_ = v_a_4254_;
v___y_4210_ = v___y_4247_;
v___y_4211_ = v___x_4260_;
v___y_4212_ = v___y_4248_;
v___y_4213_ = v___y_4250_;
v___y_4214_ = v___x_4258_;
v___y_4215_ = v___y_4204_;
v___y_4216_ = v___y_4205_;
goto v___jp_4207_;
}
else
{
uint8_t v___x_4262_; 
lean_inc(v_a_4254_);
v___x_4262_ = l_Lean_MessageData_hasTag(v___y_4244_, v_a_4254_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4263_; lean_object* v___x_4265_; 
lean_dec_ref_known(v___x_4260_, 1);
lean_dec_ref(v___x_4258_);
lean_dec(v_a_4254_);
v___x_4263_ = lean_box(0);
if (v_isShared_4257_ == 0)
{
lean_ctor_set(v___x_4256_, 0, v___x_4263_);
v___x_4265_ = v___x_4256_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v___x_4263_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
else
{
lean_del_object(v___x_4256_);
v___y_4208_ = v___x_4261_;
v___y_4209_ = v_a_4254_;
v___y_4210_ = v___y_4247_;
v___y_4211_ = v___x_4260_;
v___y_4212_ = v___y_4248_;
v___y_4213_ = v___y_4250_;
v___y_4214_ = v___x_4258_;
v___y_4215_ = v___y_4204_;
v___y_4216_ = v___y_4205_;
goto v___jp_4207_;
}
}
}
}
v___jp_4268_:
{
lean_object* v___x_4277_; 
v___x_4277_ = l_Lean_Syntax_getTailPos_x3f(v___y_4272_, v___y_4275_);
lean_dec(v___y_4272_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_inc(v___y_4276_);
v___y_4244_ = v___y_4269_;
v___y_4245_ = v___y_4270_;
v___y_4246_ = v___y_4276_;
v___y_4247_ = v___y_4271_;
v___y_4248_ = v___y_4274_;
v___y_4249_ = v___y_4273_;
v___y_4250_ = v___y_4275_;
v___y_4251_ = v___y_4276_;
goto v___jp_4243_;
}
else
{
lean_object* v_val_4278_; 
v_val_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_val_4278_);
lean_dec_ref_known(v___x_4277_, 1);
v___y_4244_ = v___y_4269_;
v___y_4245_ = v___y_4270_;
v___y_4246_ = v___y_4276_;
v___y_4247_ = v___y_4271_;
v___y_4248_ = v___y_4274_;
v___y_4249_ = v___y_4273_;
v___y_4250_ = v___y_4275_;
v___y_4251_ = v_val_4278_;
goto v___jp_4243_;
}
}
v___jp_4279_:
{
lean_object* v_ref_4287_; lean_object* v___x_4288_; 
v_ref_4287_ = l_Lean_replaceRef(v_ref_4198_, v___y_4282_);
v___x_4288_ = l_Lean_Syntax_getPos_x3f(v_ref_4287_, v___y_4285_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v___x_4289_; 
v___x_4289_ = lean_unsigned_to_nat(0u);
v___y_4269_ = v___y_4280_;
v___y_4270_ = v___y_4281_;
v___y_4271_ = v___y_4283_;
v___y_4272_ = v_ref_4287_;
v___y_4273_ = v___y_4284_;
v___y_4274_ = v___y_4286_;
v___y_4275_ = v___y_4285_;
v___y_4276_ = v___x_4289_;
goto v___jp_4268_;
}
else
{
lean_object* v_val_4290_; 
v_val_4290_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_val_4290_);
lean_dec_ref_known(v___x_4288_, 1);
v___y_4269_ = v___y_4280_;
v___y_4270_ = v___y_4281_;
v___y_4271_ = v___y_4283_;
v___y_4272_ = v_ref_4287_;
v___y_4273_ = v___y_4284_;
v___y_4274_ = v___y_4286_;
v___y_4275_ = v___y_4285_;
v___y_4276_ = v_val_4290_;
goto v___jp_4268_;
}
}
v___jp_4292_:
{
if (v___y_4299_ == 0)
{
v___y_4280_ = v___y_4296_;
v___y_4281_ = v___y_4294_;
v___y_4282_ = v___y_4293_;
v___y_4283_ = v___y_4295_;
v___y_4284_ = v___y_4297_;
v___y_4285_ = v___y_4298_;
v___y_4286_ = v_severity_4200_;
goto v___jp_4279_;
}
else
{
v___y_4280_ = v___y_4296_;
v___y_4281_ = v___y_4294_;
v___y_4282_ = v___y_4293_;
v___y_4283_ = v___y_4295_;
v___y_4284_ = v___y_4297_;
v___y_4285_ = v___y_4298_;
v___y_4286_ = v___x_4291_;
goto v___jp_4279_;
}
}
v___jp_4300_:
{
if (v___y_4301_ == 0)
{
lean_object* v_fileName_4302_; lean_object* v_fileMap_4303_; lean_object* v_options_4304_; lean_object* v_ref_4305_; uint8_t v_suppressElabErrors_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___f_4309_; uint8_t v___x_4310_; uint8_t v___x_4311_; 
v_fileName_4302_ = lean_ctor_get(v___y_4204_, 0);
v_fileMap_4303_ = lean_ctor_get(v___y_4204_, 1);
v_options_4304_ = lean_ctor_get(v___y_4204_, 2);
v_ref_4305_ = lean_ctor_get(v___y_4204_, 5);
v_suppressElabErrors_4306_ = lean_ctor_get_uint8(v___y_4204_, sizeof(void*)*14 + 1);
v___x_4307_ = lean_box(v___y_4301_);
v___x_4308_ = lean_box(v_suppressElabErrors_4306_);
v___f_4309_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig_spec__0_spec__0_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4309_, 0, v___x_4307_);
lean_closure_set(v___f_4309_, 1, v___x_4308_);
v___x_4310_ = 1;
v___x_4311_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4200_, v___x_4310_);
if (v___x_4311_ == 0)
{
v___y_4293_ = v_ref_4305_;
v___y_4294_ = v_suppressElabErrors_4306_;
v___y_4295_ = v_fileName_4302_;
v___y_4296_ = v___f_4309_;
v___y_4297_ = v_fileMap_4303_;
v___y_4298_ = v___y_4301_;
v___y_4299_ = v___x_4311_;
goto v___jp_4292_;
}
else
{
lean_object* v___x_4312_; uint8_t v___x_4313_; 
v___x_4312_ = l_Lean_warningAsError;
v___x_4313_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_options_4304_, v___x_4312_);
v___y_4293_ = v_ref_4305_;
v___y_4294_ = v_suppressElabErrors_4306_;
v___y_4295_ = v_fileName_4302_;
v___y_4296_ = v___f_4309_;
v___y_4297_ = v_fileMap_4303_;
v___y_4298_ = v___y_4301_;
v___y_4299_ = v___x_4313_;
goto v___jp_4292_;
}
}
else
{
lean_object* v___x_4314_; lean_object* v___x_4315_; 
lean_dec_ref(v_msgData_4199_);
v___x_4314_ = lean_box(0);
v___x_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4314_);
return v___x_4315_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg___boxed(lean_object* v_ref_4318_, lean_object* v_msgData_4319_, lean_object* v_severity_4320_, lean_object* v_isSilent_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
uint8_t v_severity_boxed_4327_; uint8_t v_isSilent_boxed_4328_; lean_object* v_res_4329_; 
v_severity_boxed_4327_ = lean_unbox(v_severity_4320_);
v_isSilent_boxed_4328_ = lean_unbox(v_isSilent_4321_);
v_res_4329_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg(v_ref_4318_, v_msgData_4319_, v_severity_boxed_4327_, v_isSilent_boxed_4328_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v_ref_4318_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0(lean_object* v_ref_4330_, lean_object* v_msgData_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
uint8_t v___x_4339_; uint8_t v___x_4340_; lean_object* v___x_4341_; 
v___x_4339_ = 1;
v___x_4340_ = 0;
v___x_4341_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg(v_ref_4330_, v_msgData_4331_, v___x_4339_, v___x_4340_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
return v___x_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0___boxed(lean_object* v_ref_4342_, lean_object* v_msgData_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v_res_4351_; 
v_res_4351_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0(v_ref_4342_, v_msgData_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec_ref(v___y_4346_);
lean_dec(v___y_4345_);
lean_dec_ref(v___y_4344_);
lean_dec(v_ref_4342_);
return v_res_4351_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
v___x_4359_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__2));
v___x_4360_ = l_Lean_MessageData_ofFormat(v___x_4359_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0(lean_object* v_stx_4361_, lean_object* v_goal_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
uint8_t v___y_4371_; uint8_t v___y_4372_; lean_object* v___y_4373_; uint8_t v___y_4374_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v___y_4377_; lean_object* v___y_4378_; lean_object* v___y_4379_; uint8_t v___y_4380_; uint8_t v___y_4381_; lean_object* v___y_4382_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v_untilPat_x3f_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v_options_4497_; lean_object* v___x_4498_; uint8_t v___x_4499_; 
v_options_4497_ = lean_ctor_get(v___y_4367_, 2);
v___x_4498_ = l_Lean_Elab_Tactic_Do_mvcgen_warning;
v___x_4499_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__2_spec__5(v_options_4497_, v___x_4498_);
if (v___x_4499_ == 0)
{
v___y_4436_ = v___y_4363_;
v___y_4437_ = v___y_4364_;
v___y_4438_ = v___y_4365_;
v___y_4439_ = v___y_4366_;
v___y_4440_ = v___y_4367_;
v___y_4441_ = v___y_4368_;
goto v___jp_4435_;
}
else
{
lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4500_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__3);
v___x_4501_ = l_Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0(v_stx_4361_, v___x_4500_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_dec_ref_known(v___x_4501_, 1);
v___y_4436_ = v___y_4363_;
v___y_4437_ = v___y_4364_;
v___y_4438_ = v___y_4365_;
v___y_4439_ = v___y_4366_;
v___y_4440_ = v___y_4367_;
v___y_4441_ = v___y_4368_;
goto v___jp_4435_;
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
lean_dec(v_goal_4362_);
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4501_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4501_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
v___jp_4370_:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; 
v___x_4383_ = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(v___x_4383_, 0, v___y_4376_);
lean_ctor_set(v___x_4383_, 1, v___y_4375_);
lean_ctor_set(v___x_4383_, 2, v___y_4382_);
lean_ctor_set(v___x_4383_, 3, v___y_4373_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*4, v___y_4381_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*4 + 1, v___y_4380_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*4 + 2, v___y_4374_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*4 + 3, v___y_4372_);
lean_ctor_set_uint8(v___x_4383_, sizeof(void*)*4 + 4, v___y_4371_);
v___x_4384_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4384_, 0, v___y_4377_);
lean_ctor_set(v___x_4384_, 1, v___x_4383_);
lean_ctor_set(v___x_4384_, 2, v___y_4379_);
lean_ctor_set(v___x_4384_, 3, v___y_4378_);
v___x_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
return v___x_4385_;
}
v___jp_4386_:
{
lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4397_ = lean_unsigned_to_nat(5u);
v___x_4398_ = l_Lean_Syntax_getArg(v_stx_4361_, v___x_4397_);
v___x_4399_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabSimplifyingAssumptions(v___x_4398_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___x_4398_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref_known(v___x_4399_, 1);
v___x_4401_ = lean_unsigned_to_nat(4u);
v___x_4402_ = l_Lean_Syntax_getArg(v_stx_4361_, v___x_4401_);
v___x_4403_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseInvariantMap(v___x_4402_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___x_4402_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
if (lean_obj_tag(v_a_4404_) == 0)
{
lean_object* v_backwardRules_4405_; uint8_t v_trivial_4406_; uint8_t v_jp_4407_; uint8_t v_errorOnMissingSpec_4408_; uint8_t v_debug_4409_; uint8_t v_internalize_4410_; lean_object* v___x_4411_; 
v_backwardRules_4405_ = lean_ctor_get(v___y_4387_, 0);
lean_inc_ref(v_backwardRules_4405_);
lean_dec_ref(v___y_4387_);
v_trivial_4406_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*1);
v_jp_4407_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*1 + 3);
v_errorOnMissingSpec_4408_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*1 + 4);
v_debug_4409_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*1 + 5);
v_internalize_4410_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*1 + 6);
v___x_4411_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__2);
v___y_4371_ = v_internalize_4410_;
v___y_4372_ = v_debug_4409_;
v___y_4373_ = v_untilPat_x3f_4390_;
v___y_4374_ = v_errorOnMissingSpec_4408_;
v___y_4375_ = v_a_4400_;
v___y_4376_ = v_backwardRules_4405_;
v___y_4377_ = v___y_4388_;
v___y_4378_ = v_a_4404_;
v___y_4379_ = v___y_4389_;
v___y_4380_ = v_jp_4407_;
v___y_4381_ = v_trivial_4406_;
v___y_4382_ = v___x_4411_;
goto v___jp_4370_;
}
else
{
lean_object* v_backwardRules_4412_; uint8_t v_trivial_4413_; uint8_t v_jp_4414_; uint8_t v_errorOnMissingSpec_4415_; uint8_t v_debug_4416_; uint8_t v_internalize_4417_; lean_object* v_val_4418_; 
v_backwardRules_4412_ = lean_ctor_get(v___y_4387_, 0);
lean_inc_ref(v_backwardRules_4412_);
lean_dec_ref(v___y_4387_);
v_trivial_4413_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*1);
v_jp_4414_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*1 + 3);
v_errorOnMissingSpec_4415_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*1 + 4);
v_debug_4416_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*1 + 5);
v_internalize_4417_ = lean_ctor_get_uint8(v___y_4388_, sizeof(void*)*1 + 6);
v_val_4418_ = lean_ctor_get(v_a_4404_, 0);
lean_inc(v_val_4418_);
v___y_4371_ = v_internalize_4417_;
v___y_4372_ = v_debug_4416_;
v___y_4373_ = v_untilPat_x3f_4390_;
v___y_4374_ = v_errorOnMissingSpec_4415_;
v___y_4375_ = v_a_4400_;
v___y_4376_ = v_backwardRules_4412_;
v___y_4377_ = v___y_4388_;
v___y_4378_ = v_a_4404_;
v___y_4379_ = v___y_4389_;
v___y_4380_ = v_jp_4414_;
v___y_4381_ = v_trivial_4413_;
v___y_4382_ = v_val_4418_;
goto v___jp_4370_;
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_dec(v_a_4400_);
lean_dec(v_untilPat_x3f_4390_);
lean_dec_ref(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec_ref(v___y_4387_);
v_a_4419_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4403_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4403_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
else
{
lean_object* v_a_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4434_; 
lean_dec(v_untilPat_x3f_4390_);
lean_dec_ref(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec_ref(v___y_4387_);
v_a_4427_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4434_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4434_ == 0)
{
v___x_4429_ = v___x_4399_;
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_a_4427_);
lean_dec(v___x_4399_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4434_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4432_; 
if (v_isShared_4430_ == 0)
{
v___x_4432_ = v___x_4429_;
goto v_reusejp_4431_;
}
else
{
lean_object* v_reuseFailAlloc_4433_; 
v_reuseFailAlloc_4433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4433_, 0, v_a_4427_);
v___x_4432_ = v_reuseFailAlloc_4433_;
goto v_reusejp_4431_;
}
v_reusejp_4431_:
{
return v___x_4432_;
}
}
}
}
v___jp_4435_:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; uint8_t v___x_4444_; uint8_t v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4442_ = lean_unsigned_to_nat(1u);
v___x_4443_ = l_Lean_Syntax_getArg(v_stx_4361_, v___x_4442_);
v___x_4444_ = 1;
v___x_4445_ = 0;
v___x_4446_ = lean_box(0);
v___x_4447_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___closed__0));
v___x_4448_ = lean_box(v___x_4444_);
v___x_4449_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabConfig___boxed), 12, 3);
lean_closure_set(v___x_4449_, 0, v___x_4443_);
lean_closure_set(v___x_4449_, 1, v___x_4447_);
lean_closure_set(v___x_4449_, 2, v___x_4448_);
v___x_4450_ = lean_box(0);
v___x_4451_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg(v___x_4449_, v___x_4450_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_object* v_a_4452_; lean_object* v___x_4453_; 
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref_known(v___x_4451_, 1);
v___x_4453_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_warnIgnoredConfig(v_a_4452_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
lean_dec_ref_known(v___x_4453_, 1);
v___x_4454_ = lean_unsigned_to_nat(2u);
v___x_4455_ = l_Lean_Syntax_getArg(v_stx_4361_, v___x_4454_);
v___x_4456_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext(v___x_4455_, v_goal_4362_, v___x_4445_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___x_4455_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v_fst_4458_; lean_object* v_snd_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; uint8_t v___x_4462_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4457_);
lean_dec_ref_known(v___x_4456_, 1);
v_fst_4458_ = lean_ctor_get(v_a_4457_, 0);
lean_inc(v_fst_4458_);
v_snd_4459_ = lean_ctor_get(v_a_4457_, 1);
lean_inc(v_snd_4459_);
lean_dec(v_a_4457_);
v___x_4460_ = lean_unsigned_to_nat(3u);
v___x_4461_ = l_Lean_Syntax_getArg(v_stx_4361_, v___x_4460_);
v___x_4462_ = l_Lean_Syntax_isNone(v___x_4461_);
if (v___x_4462_ == 0)
{
lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
v___x_4463_ = l_Lean_Syntax_getArg(v___x_4461_, v___x_4442_);
lean_dec(v___x_4461_);
v___x_4464_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg(v___x_4463_, v___y_4438_);
v_a_4465_ = lean_ctor_get(v___x_4464_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4464_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4464_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4464_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
lean_ctor_set_tag(v___x_4467_, 1);
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
v___y_4387_ = v_fst_4458_;
v___y_4388_ = v_a_4452_;
v___y_4389_ = v_snd_4459_;
v_untilPat_x3f_4390_ = v___x_4470_;
v___y_4391_ = v___y_4436_;
v___y_4392_ = v___y_4437_;
v___y_4393_ = v___y_4438_;
v___y_4394_ = v___y_4439_;
v___y_4395_ = v___y_4440_;
v___y_4396_ = v___y_4441_;
goto v___jp_4386_;
}
}
}
else
{
lean_dec(v___x_4461_);
v___y_4387_ = v_fst_4458_;
v___y_4388_ = v_a_4452_;
v___y_4389_ = v_snd_4459_;
v_untilPat_x3f_4390_ = v___x_4446_;
v___y_4391_ = v___y_4436_;
v___y_4392_ = v___y_4437_;
v___y_4393_ = v___y_4438_;
v___y_4394_ = v___y_4439_;
v___y_4395_ = v___y_4440_;
v___y_4396_ = v___y_4441_;
goto v___jp_4386_;
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
lean_dec(v_a_4452_);
v_a_4473_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___x_4456_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4456_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
return v___x_4478_;
}
}
}
}
else
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4488_; 
lean_dec(v_a_4452_);
lean_dec(v_goal_4362_);
v_a_4481_ = lean_ctor_get(v___x_4453_, 0);
v_isSharedCheck_4488_ = !lean_is_exclusive(v___x_4453_);
if (v_isSharedCheck_4488_ == 0)
{
v___x_4483_ = v___x_4453_;
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4453_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4488_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
if (v_isShared_4484_ == 0)
{
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
return v___x_4486_;
}
}
}
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec(v_goal_4362_);
v_a_4489_ = lean_ctor_get(v___x_4451_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4451_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4451_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4451_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___boxed(lean_object* v_stx_4510_, lean_object* v_goal_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0(v_stx_4510_, v_goal_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec(v___y_4515_);
lean_dec_ref(v___y_4514_);
lean_dec(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec(v_stx_4510_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs(lean_object* v_stx_4520_, lean_object* v_goal_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v___f_4529_; lean_object* v___x_4530_; 
lean_inc(v_goal_4521_);
v___f_4529_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___lam__0___boxed), 9, 2);
lean_closure_set(v___f_4529_, 0, v_stx_4520_);
lean_closure_set(v___f_4529_, 1, v_goal_4521_);
v___x_4530_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__1___redArg(v_goal_4521_, v___f_4529_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
return v___x_4530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs___boxed(lean_object* v_stx_4531_, lean_object* v_goal_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs(v_stx_4531_, v_goal_4532_, v_a_4533_, v_a_4534_, v_a_4535_, v_a_4536_, v_a_4537_, v_a_4538_);
lean_dec(v_a_4538_);
lean_dec_ref(v_a_4537_);
lean_dec(v_a_4536_);
lean_dec_ref(v_a_4535_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0(lean_object* v_ref_4541_, lean_object* v_msgData_4542_, uint8_t v_severity_4543_, uint8_t v_isSilent_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v___x_4552_; 
v___x_4552_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___redArg(v_ref_4541_, v_msgData_4542_, v_severity_4543_, v_isSilent_4544_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0___boxed(lean_object* v_ref_4553_, lean_object* v_msgData_4554_, lean_object* v_severity_4555_, lean_object* v_isSilent_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
uint8_t v_severity_boxed_4564_; uint8_t v_isSilent_boxed_4565_; lean_object* v_res_4566_; 
v_severity_boxed_4564_ = lean_unbox(v_severity_4555_);
v_isSilent_boxed_4565_ = lean_unbox(v_isSilent_4556_);
v_res_4566_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs_spec__0_spec__0(v_ref_4553_, v_msgData_4554_, v_severity_boxed_4564_, v_isSilent_boxed_4565_, v___y_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v_ref_4553_);
return v_res_4566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__0(lean_object* v_a_4567_, lean_object* v_ctx_4568_, lean_object* v_scope_4569_, lean_object* v_stepLimit_4570_, lean_object* v_invariantAlts_x3f_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_){
_start:
{
lean_object* v___x_4582_; 
v___x_4582_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_run(v_a_4567_, v_ctx_4568_, v_scope_4569_, v_stepLimit_4570_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4582_) == 0)
{
if (lean_obj_tag(v_invariantAlts_x3f_4571_) == 1)
{
lean_object* v_a_4583_; lean_object* v_val_4584_; lean_object* v_invariants_4585_; lean_object* v_inlineHandledInvariants_4586_; lean_object* v___x_4587_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4583_);
lean_dec_ref_known(v___x_4582_, 1);
v_val_4584_ = lean_ctor_get(v_invariantAlts_x3f_4571_, 0);
v_invariants_4585_ = lean_ctor_get(v_a_4583_, 0);
v_inlineHandledInvariants_4586_ = lean_ctor_get(v_a_4583_, 2);
lean_inc_ref(v_inlineHandledInvariants_4586_);
v___x_4587_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabRemainingInvariants(v_val_4584_, v_invariants_4585_, v_inlineHandledInvariants_4586_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
if (lean_obj_tag(v___x_4587_) == 0)
{
lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4594_; 
v_isSharedCheck_4594_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4594_ == 0)
{
lean_object* v_unused_4595_; 
v_unused_4595_ = lean_ctor_get(v___x_4587_, 0);
lean_dec(v_unused_4595_);
v___x_4589_ = v___x_4587_;
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
else
{
lean_dec(v___x_4587_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4594_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4592_; 
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 0, v_a_4583_);
v___x_4592_ = v___x_4589_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4583_);
v___x_4592_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
return v___x_4592_;
}
}
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
lean_dec(v_a_4583_);
v_a_4596_ = lean_ctor_get(v___x_4587_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4587_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4598_ = v___x_4587_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4587_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
else
{
return v___x_4582_;
}
}
else
{
return v___x_4582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__0___boxed(lean_object* v_a_4604_, lean_object* v_ctx_4605_, lean_object* v_scope_4606_, lean_object* v_stepLimit_4607_, lean_object* v_invariantAlts_x3f_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__0(v_a_4604_, v_ctx_4605_, v_scope_4606_, v_stepLimit_4607_, v_invariantAlts_x3f_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_, v___y_4617_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec(v_invariantAlts_x3f_4608_);
lean_dec_ref(v_ctx_4605_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__1(lean_object* v_x_4620_, lean_object* v_x_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_){
_start:
{
if (lean_obj_tag(v_x_4620_) == 0)
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = l_List_reverse___redArg(v_x_4621_);
v___x_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4632_);
return v___x_4633_;
}
else
{
lean_object* v_head_4634_; lean_object* v_tail_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4653_; 
v_head_4634_ = lean_ctor_get(v_x_4620_, 0);
v_tail_4635_ = lean_ctor_get(v_x_4620_, 1);
v_isSharedCheck_4653_ = !lean_is_exclusive(v_x_4620_);
if (v_isSharedCheck_4653_ == 0)
{
v___x_4637_ = v_x_4620_;
v_isShared_4638_ = v_isSharedCheck_4653_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_tail_4635_);
lean_inc(v_head_4634_);
lean_dec(v_x_4620_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4653_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4639_; 
v___x_4639_ = l_Lean_Meta_Grind_mkGoalCore(v_head_4634_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v_a_4640_; lean_object* v___x_4642_; 
v_a_4640_ = lean_ctor_get(v___x_4639_, 0);
lean_inc(v_a_4640_);
lean_dec_ref_known(v___x_4639_, 1);
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 1, v_x_4621_);
lean_ctor_set(v___x_4637_, 0, v_a_4640_);
v___x_4642_ = v___x_4637_;
goto v_reusejp_4641_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_a_4640_);
lean_ctor_set(v_reuseFailAlloc_4644_, 1, v_x_4621_);
v___x_4642_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4641_;
}
v_reusejp_4641_:
{
v_x_4620_ = v_tail_4635_;
v_x_4621_ = v___x_4642_;
goto _start;
}
}
else
{
lean_object* v_a_4645_; lean_object* v___x_4647_; uint8_t v_isShared_4648_; uint8_t v_isSharedCheck_4652_; 
lean_del_object(v___x_4637_);
lean_dec(v_tail_4635_);
lean_dec(v_x_4621_);
v_a_4645_ = lean_ctor_get(v___x_4639_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4647_ = v___x_4639_;
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
else
{
lean_inc(v_a_4645_);
lean_dec(v___x_4639_);
v___x_4647_ = lean_box(0);
v_isShared_4648_ = v_isSharedCheck_4652_;
goto v_resetjp_4646_;
}
v_resetjp_4646_:
{
lean_object* v___x_4650_; 
if (v_isShared_4648_ == 0)
{
v___x_4650_ = v___x_4647_;
goto v_reusejp_4649_;
}
else
{
lean_object* v_reuseFailAlloc_4651_; 
v_reuseFailAlloc_4651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4651_, 0, v_a_4645_);
v___x_4650_ = v_reuseFailAlloc_4651_;
goto v_reusejp_4649_;
}
v_reusejp_4649_:
{
return v___x_4650_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__1___boxed(lean_object* v_x_4654_, lean_object* v_x_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__1(v_x_4654_, v_x_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec(v___y_4658_);
lean_dec_ref(v___y_4657_);
lean_dec(v___y_4656_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__1(lean_object* v___x_4667_, lean_object* v___x_4668_, lean_object* v_a_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = l_List_mapM_loop___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__1(v___x_4667_, v___x_4668_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4691_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4691_ == 0)
{
v___x_4683_ = v___x_4680_;
v_isShared_4684_ = v_isSharedCheck_4691_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4680_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4691_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v_vcs_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4689_; 
v_vcs_4685_ = lean_ctor_get(v_a_4669_, 1);
lean_inc_ref(v_vcs_4685_);
lean_dec_ref(v_a_4669_);
v___x_4686_ = lean_array_to_list(v_vcs_4685_);
v___x_4687_ = l_List_appendTR___redArg(v_a_4681_, v___x_4686_);
if (v_isShared_4684_ == 0)
{
lean_ctor_set(v___x_4683_, 0, v___x_4687_);
v___x_4689_ = v___x_4683_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v___x_4687_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
}
else
{
lean_dec_ref(v_a_4669_);
return v___x_4680_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__1___boxed(lean_object* v___x_4692_, lean_object* v___x_4693_, lean_object* v_a_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__1(v___x_4692_, v___x_4693_, v_a_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec(v___y_4695_);
return v_res_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__3(size_t v_sz_4706_, size_t v_i_4707_, lean_object* v_bs_4708_){
_start:
{
uint8_t v___x_4709_; 
v___x_4709_ = lean_usize_dec_lt(v_i_4707_, v_sz_4706_);
if (v___x_4709_ == 0)
{
return v_bs_4708_;
}
else
{
lean_object* v_v_4710_; lean_object* v_mvarId_4711_; lean_object* v___x_4712_; lean_object* v_bs_x27_4713_; size_t v___x_4714_; size_t v___x_4715_; lean_object* v___x_4716_; 
v_v_4710_ = lean_array_uget_borrowed(v_bs_4708_, v_i_4707_);
v_mvarId_4711_ = lean_ctor_get(v_v_4710_, 1);
lean_inc(v_mvarId_4711_);
v___x_4712_ = lean_unsigned_to_nat(0u);
v_bs_x27_4713_ = lean_array_uset(v_bs_4708_, v_i_4707_, v___x_4712_);
v___x_4714_ = ((size_t)1ULL);
v___x_4715_ = lean_usize_add(v_i_4707_, v___x_4714_);
v___x_4716_ = lean_array_uset(v_bs_x27_4713_, v_i_4707_, v_mvarId_4711_);
v_i_4707_ = v___x_4715_;
v_bs_4708_ = v___x_4716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__3___boxed(lean_object* v_sz_4718_, lean_object* v_i_4719_, lean_object* v_bs_4720_){
_start:
{
size_t v_sz_boxed_4721_; size_t v_i_boxed_4722_; lean_object* v_res_4723_; 
v_sz_boxed_4721_ = lean_unbox_usize(v_sz_4718_);
lean_dec(v_sz_4718_);
v_i_boxed_4722_ = lean_unbox_usize(v_i_4719_);
lean_dec(v_i_4719_);
v_res_4723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__3(v_sz_boxed_4721_, v_i_boxed_4722_, v_bs_4720_);
return v_res_4723_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5___redArg(lean_object* v_keys_4724_, lean_object* v_i_4725_, lean_object* v_k_4726_){
_start:
{
lean_object* v___x_4727_; uint8_t v___x_4728_; 
v___x_4727_ = lean_array_get_size(v_keys_4724_);
v___x_4728_ = lean_nat_dec_lt(v_i_4725_, v___x_4727_);
if (v___x_4728_ == 0)
{
lean_dec(v_i_4725_);
return v___x_4728_;
}
else
{
lean_object* v_k_x27_4729_; uint8_t v___x_4730_; 
v_k_x27_4729_ = lean_array_fget_borrowed(v_keys_4724_, v_i_4725_);
v___x_4730_ = l_Lean_instBEqMVarId_beq(v_k_4726_, v_k_x27_4729_);
if (v___x_4730_ == 0)
{
lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4731_ = lean_unsigned_to_nat(1u);
v___x_4732_ = lean_nat_add(v_i_4725_, v___x_4731_);
lean_dec(v_i_4725_);
v_i_4725_ = v___x_4732_;
goto _start;
}
else
{
lean_dec(v_i_4725_);
return v___x_4730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_keys_4734_, lean_object* v_i_4735_, lean_object* v_k_4736_){
_start:
{
uint8_t v_res_4737_; lean_object* v_r_4738_; 
v_res_4737_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_4734_, v_i_4735_, v_k_4736_);
lean_dec(v_k_4736_);
lean_dec_ref(v_keys_4734_);
v_r_4738_ = lean_box(v_res_4737_);
return v_r_4738_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1___redArg(lean_object* v_x_4739_, size_t v_x_4740_, lean_object* v_x_4741_){
_start:
{
if (lean_obj_tag(v_x_4739_) == 0)
{
lean_object* v_es_4742_; lean_object* v___x_4743_; size_t v___x_4744_; size_t v___x_4745_; lean_object* v_j_4746_; lean_object* v___x_4747_; 
v_es_4742_ = lean_ctor_get(v_x_4739_, 0);
v___x_4743_ = lean_box(2);
v___x_4744_ = ((size_t)31ULL);
v___x_4745_ = lean_usize_land(v_x_4740_, v___x_4744_);
v_j_4746_ = lean_usize_to_nat(v___x_4745_);
v___x_4747_ = lean_array_get_borrowed(v___x_4743_, v_es_4742_, v_j_4746_);
lean_dec(v_j_4746_);
switch(lean_obj_tag(v___x_4747_))
{
case 0:
{
lean_object* v_key_4748_; uint8_t v___x_4749_; 
v_key_4748_ = lean_ctor_get(v___x_4747_, 0);
v___x_4749_ = l_Lean_instBEqMVarId_beq(v_x_4741_, v_key_4748_);
return v___x_4749_;
}
case 1:
{
lean_object* v_node_4750_; size_t v___x_4751_; size_t v___x_4752_; 
v_node_4750_ = lean_ctor_get(v___x_4747_, 0);
v___x_4751_ = ((size_t)5ULL);
v___x_4752_ = lean_usize_shift_right(v_x_4740_, v___x_4751_);
v_x_4739_ = v_node_4750_;
v_x_4740_ = v___x_4752_;
goto _start;
}
default: 
{
uint8_t v___x_4754_; 
v___x_4754_ = 0;
return v___x_4754_;
}
}
}
else
{
lean_object* v_ks_4755_; lean_object* v___x_4756_; uint8_t v___x_4757_; 
v_ks_4755_ = lean_ctor_get(v_x_4739_, 0);
v___x_4756_ = lean_unsigned_to_nat(0u);
v___x_4757_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5___redArg(v_ks_4755_, v___x_4756_, v_x_4741_);
return v___x_4757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4758_, lean_object* v_x_4759_, lean_object* v_x_4760_){
_start:
{
size_t v_x_6258__boxed_4761_; uint8_t v_res_4762_; lean_object* v_r_4763_; 
v_x_6258__boxed_4761_ = lean_unbox_usize(v_x_4759_);
lean_dec(v_x_4759_);
v_res_4762_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1___redArg(v_x_4758_, v_x_6258__boxed_4761_, v_x_4760_);
lean_dec(v_x_4760_);
lean_dec_ref(v_x_4758_);
v_r_4763_ = lean_box(v_res_4762_);
return v_r_4763_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0___redArg(lean_object* v_x_4764_, lean_object* v_x_4765_){
_start:
{
uint64_t v___x_4766_; size_t v___x_4767_; uint8_t v___x_4768_; 
v___x_4766_ = l_Lean_instHashableMVarId_hash(v_x_4765_);
v___x_4767_ = lean_uint64_to_usize(v___x_4766_);
v___x_4768_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1___redArg(v_x_4764_, v___x_4767_, v_x_4765_);
return v___x_4768_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0___redArg___boxed(lean_object* v_x_4769_, lean_object* v_x_4770_){
_start:
{
uint8_t v_res_4771_; lean_object* v_r_4772_; 
v_res_4771_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0___redArg(v_x_4769_, v_x_4770_);
lean_dec(v_x_4770_);
lean_dec_ref(v_x_4769_);
v_r_4772_ = lean_box(v_res_4771_);
return v_r_4772_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0___redArg(lean_object* v_mvarId_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v___x_4776_; lean_object* v_mctx_4777_; lean_object* v_eAssignment_4778_; uint8_t v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4776_ = lean_st_ref_get(v___y_4774_);
v_mctx_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc_ref(v_mctx_4777_);
lean_dec(v___x_4776_);
v_eAssignment_4778_ = lean_ctor_get(v_mctx_4777_, 8);
lean_inc_ref(v_eAssignment_4778_);
lean_dec_ref(v_mctx_4777_);
v___x_4779_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0___redArg(v_eAssignment_4778_, v_mvarId_4773_);
lean_dec_ref(v_eAssignment_4778_);
v___x_4780_ = lean_box(v___x_4779_);
v___x_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4780_);
return v___x_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0___redArg___boxed(lean_object* v_mvarId_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0___redArg(v_mvarId_4782_, v___y_4783_);
lean_dec(v___y_4783_);
lean_dec(v_mvarId_4782_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__2(lean_object* v_as_4786_, size_t v_i_4787_, size_t v_stop_4788_, lean_object* v_b_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v_a_4800_; uint8_t v___x_4804_; 
v___x_4804_ = lean_usize_dec_eq(v_i_4787_, v_stop_4788_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; lean_object* v___x_4808_; 
v___x_4805_ = lean_array_uget_borrowed(v_as_4786_, v_i_4787_);
v___x_4808_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0___redArg(v___x_4805_, v___y_4795_);
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v_a_4809_; uint8_t v___x_4810_; 
v_a_4809_ = lean_ctor_get(v___x_4808_, 0);
lean_inc(v_a_4809_);
lean_dec_ref_known(v___x_4808_, 1);
v___x_4810_ = lean_unbox(v_a_4809_);
lean_dec(v_a_4809_);
if (v___x_4810_ == 0)
{
goto v___jp_4806_;
}
else
{
v_a_4800_ = v_b_4789_;
goto v___jp_4799_;
}
}
else
{
if (lean_obj_tag(v___x_4808_) == 0)
{
lean_object* v_a_4811_; uint8_t v___x_4812_; 
v_a_4811_ = lean_ctor_get(v___x_4808_, 0);
lean_inc(v_a_4811_);
lean_dec_ref_known(v___x_4808_, 1);
v___x_4812_ = lean_unbox(v_a_4811_);
lean_dec(v_a_4811_);
if (v___x_4812_ == 0)
{
v_a_4800_ = v_b_4789_;
goto v___jp_4799_;
}
else
{
goto v___jp_4806_;
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
lean_dec_ref(v_b_4789_);
v_a_4813_ = lean_ctor_get(v___x_4808_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4808_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___x_4808_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4808_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
v___jp_4806_:
{
lean_object* v___x_4807_; 
lean_inc(v___x_4805_);
v___x_4807_ = lean_array_push(v_b_4789_, v___x_4805_);
v_a_4800_ = v___x_4807_;
goto v___jp_4799_;
}
}
else
{
lean_object* v___x_4821_; 
v___x_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4821_, 0, v_b_4789_);
return v___x_4821_;
}
v___jp_4799_:
{
size_t v___x_4801_; size_t v___x_4802_; 
v___x_4801_ = ((size_t)1ULL);
v___x_4802_ = lean_usize_add(v_i_4787_, v___x_4801_);
v_i_4787_ = v___x_4802_;
v_b_4789_ = v_a_4800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__2___boxed(lean_object* v_as_4822_, lean_object* v_i_4823_, lean_object* v_stop_4824_, lean_object* v_b_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
size_t v_i_boxed_4835_; size_t v_stop_boxed_4836_; lean_object* v_res_4837_; 
v_i_boxed_4835_ = lean_unbox_usize(v_i_4823_);
lean_dec(v_i_4823_);
v_stop_boxed_4836_ = lean_unbox_usize(v_stop_4824_);
lean_dec(v_stop_4824_);
v_res_4837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__2(v_as_4822_, v_i_boxed_4835_, v_stop_boxed_4836_, v_b_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec_ref(v_as_4822_);
return v_res_4837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen(lean_object* v_stx_4838_, lean_object* v_a_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_, lean_object* v_a_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_, lean_object* v_a_4846_){
_start:
{
lean_object* v___x_4848_; 
v___x_4848_ = l_Lean_Elab_Tactic_Grind_getMainGoal___redArg(v_a_4840_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_);
if (lean_obj_tag(v___x_4848_) == 0)
{
lean_object* v_a_4849_; lean_object* v_mvarId_4850_; lean_object* v___x_4851_; 
v_a_4849_ = lean_ctor_get(v___x_4848_, 0);
lean_inc(v_a_4849_);
lean_dec_ref_known(v___x_4848_, 1);
v_mvarId_4850_ = lean_ctor_get(v_a_4849_, 1);
lean_inc(v_mvarId_4850_);
lean_inc(v_stx_4838_);
v___x_4851_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_parseArgs(v_stx_4838_, v_mvarId_4850_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v_config_4853_; lean_object* v_ctx_4854_; lean_object* v_scope_4855_; lean_object* v_invariantAlts_x3f_4856_; lean_object* v_stepLimit_4857_; lean_object* v___f_4858_; lean_object* v___x_4859_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4851_, 1);
v_config_4853_ = lean_ctor_get(v_a_4852_, 0);
lean_inc_ref(v_config_4853_);
v_ctx_4854_ = lean_ctor_get(v_a_4852_, 1);
lean_inc_ref(v_ctx_4854_);
v_scope_4855_ = lean_ctor_get(v_a_4852_, 2);
lean_inc_ref(v_scope_4855_);
v_invariantAlts_x3f_4856_ = lean_ctor_get(v_a_4852_, 3);
lean_inc_n(v_invariantAlts_x3f_4856_, 2);
lean_dec(v_a_4852_);
v_stepLimit_4857_ = lean_ctor_get(v_config_4853_, 0);
lean_inc(v_stepLimit_4857_);
lean_dec_ref(v_config_4853_);
v___f_4858_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__0___boxed), 15, 5);
lean_closure_set(v___f_4858_, 0, v_a_4849_);
lean_closure_set(v___f_4858_, 1, v_ctx_4854_);
lean_closure_set(v___f_4858_, 2, v_scope_4855_);
lean_closure_set(v___f_4858_, 3, v_stepLimit_4857_);
lean_closure_set(v___f_4858_, 4, v_invariantAlts_x3f_4856_);
v___x_4859_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_4858_, v_a_4839_, v_a_4840_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; lean_object* v___y_4862_; lean_object* v___y_4863_; lean_object* v___y_4864_; lean_object* v___y_4865_; lean_object* v___y_4866_; lean_object* v___y_4867_; lean_object* v_a_4868_; lean_object* v___y_4884_; lean_object* v___y_4885_; lean_object* v___y_4886_; lean_object* v___y_4887_; lean_object* v___y_4888_; lean_object* v___y_4889_; lean_object* v___y_4890_; lean_object* v___y_4901_; lean_object* v___y_4902_; lean_object* v___y_4903_; lean_object* v___y_4904_; lean_object* v___y_4905_; lean_object* v___y_4906_; lean_object* v___y_4907_; lean_object* v___y_4908_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
lean_inc(v_a_4860_);
lean_dec_ref_known(v___x_4859_, 1);
if (lean_obj_tag(v_invariantAlts_x3f_4856_) == 0)
{
lean_object* v_invariants_4921_; lean_object* v_vcs_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; size_t v_sz_4925_; size_t v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v_invariants_4921_ = lean_ctor_get(v_a_4860_, 0);
v_vcs_4922_ = lean_ctor_get(v_a_4860_, 1);
v___x_4923_ = lean_unsigned_to_nat(4u);
v___x_4924_ = l_Lean_Syntax_getArg(v_stx_4838_, v___x_4923_);
lean_dec(v_stx_4838_);
v_sz_4925_ = lean_array_size(v_vcs_4922_);
v___x_4926_ = ((size_t)0ULL);
lean_inc_ref(v_vcs_4922_);
v___x_4927_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__3(v_sz_4925_, v___x_4926_, v_vcs_4922_);
v___x_4928_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_suggestInvariant___boxed), 11, 1);
lean_closure_set(v___x_4928_, 0, v___x_4927_);
lean_inc_ref_n(v_invariants_4921_, 2);
v___x_4929_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_elabInvariants___boxed), 12, 3);
lean_closure_set(v___x_4929_, 0, v___x_4924_);
lean_closure_set(v___x_4929_, 1, v_invariants_4921_);
lean_closure_set(v___x_4929_, 2, v___x_4928_);
v___x_4930_ = lean_array_to_list(v_invariants_4921_);
v___x_4931_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_runTacticM___redArg(v___x_4929_, v___x_4930_, v_a_4841_, v_a_4842_, v_a_4843_, v_a_4844_, v_a_4845_, v_a_4846_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_dec_ref_known(v___x_4931_, 1);
v___y_4901_ = v_a_4839_;
v___y_4902_ = v_a_4840_;
v___y_4903_ = v_a_4841_;
v___y_4904_ = v_a_4842_;
v___y_4905_ = v_a_4843_;
v___y_4906_ = v_a_4844_;
v___y_4907_ = v_a_4845_;
v___y_4908_ = v_a_4846_;
goto v___jp_4900_;
}
else
{
lean_dec(v_a_4860_);
return v___x_4931_;
}
}
else
{
lean_dec_ref_known(v_invariantAlts_x3f_4856_, 1);
lean_dec(v_stx_4838_);
v___y_4901_ = v_a_4839_;
v___y_4902_ = v_a_4840_;
v___y_4903_ = v_a_4841_;
v___y_4904_ = v_a_4842_;
v___y_4905_ = v_a_4843_;
v___y_4906_ = v_a_4844_;
v___y_4907_ = v_a_4845_;
v___y_4908_ = v_a_4846_;
goto v___jp_4900_;
}
v___jp_4861_:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___f_4871_; lean_object* v___x_4872_; 
v___x_4869_ = lean_array_to_list(v_a_4868_);
v___x_4870_ = lean_box(0);
v___f_4871_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___lam__1___boxed), 13, 3);
lean_closure_set(v___f_4871_, 0, v___x_4869_);
lean_closure_set(v___f_4871_, 1, v___x_4870_);
lean_closure_set(v___f_4871_, 2, v_a_4860_);
v___x_4872_ = l_Lean_Elab_Tactic_Grind_liftGrindM___redArg(v___f_4871_, v___y_4867_, v___y_4865_, v___y_4864_, v___y_4866_, v___y_4863_, v___y_4862_);
if (lean_obj_tag(v___x_4872_) == 0)
{
lean_object* v_a_4873_; lean_object* v___x_4874_; 
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc(v_a_4873_);
lean_dec_ref_known(v___x_4872_, 1);
v___x_4874_ = l_Lean_Elab_Tactic_Grind_replaceMainGoal___redArg(v_a_4873_, v___y_4865_, v___y_4864_, v___y_4866_, v___y_4863_, v___y_4862_);
return v___x_4874_;
}
else
{
lean_object* v_a_4875_; lean_object* v___x_4877_; uint8_t v_isShared_4878_; uint8_t v_isSharedCheck_4882_; 
v_a_4875_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4877_ = v___x_4872_;
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
else
{
lean_inc(v_a_4875_);
lean_dec(v___x_4872_);
v___x_4877_ = lean_box(0);
v_isShared_4878_ = v_isSharedCheck_4882_;
goto v_resetjp_4876_;
}
v_resetjp_4876_:
{
lean_object* v___x_4880_; 
if (v_isShared_4878_ == 0)
{
v___x_4880_ = v___x_4877_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_a_4875_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
}
v___jp_4883_:
{
if (lean_obj_tag(v___y_4890_) == 0)
{
lean_object* v_a_4891_; 
v_a_4891_ = lean_ctor_get(v___y_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref_known(v___y_4890_, 1);
v___y_4862_ = v___y_4884_;
v___y_4863_ = v___y_4885_;
v___y_4864_ = v___y_4887_;
v___y_4865_ = v___y_4886_;
v___y_4866_ = v___y_4888_;
v___y_4867_ = v___y_4889_;
v_a_4868_ = v_a_4891_;
goto v___jp_4861_;
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec(v_a_4860_);
v_a_4892_ = lean_ctor_get(v___y_4890_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___y_4890_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___y_4890_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___y_4890_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
v___jp_4900_:
{
lean_object* v_invariants_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; uint8_t v___x_4913_; 
v_invariants_4909_ = lean_ctor_get(v_a_4860_, 0);
v___x_4910_ = lean_unsigned_to_nat(0u);
v___x_4911_ = lean_array_get_size(v_invariants_4909_);
v___x_4912_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabUntilPattern___redArg___lam__1___closed__2));
v___x_4913_ = lean_nat_dec_lt(v___x_4910_, v___x_4911_);
if (v___x_4913_ == 0)
{
v___y_4862_ = v___y_4908_;
v___y_4863_ = v___y_4907_;
v___y_4864_ = v___y_4905_;
v___y_4865_ = v___y_4902_;
v___y_4866_ = v___y_4906_;
v___y_4867_ = v___y_4901_;
v_a_4868_ = v___x_4912_;
goto v___jp_4861_;
}
else
{
uint8_t v___x_4914_; 
v___x_4914_ = lean_nat_dec_le(v___x_4911_, v___x_4911_);
if (v___x_4914_ == 0)
{
if (v___x_4913_ == 0)
{
v___y_4862_ = v___y_4908_;
v___y_4863_ = v___y_4907_;
v___y_4864_ = v___y_4905_;
v___y_4865_ = v___y_4902_;
v___y_4866_ = v___y_4906_;
v___y_4867_ = v___y_4901_;
v_a_4868_ = v___x_4912_;
goto v___jp_4861_;
}
else
{
size_t v___x_4915_; size_t v___x_4916_; lean_object* v___x_4917_; 
v___x_4915_ = ((size_t)0ULL);
v___x_4916_ = lean_usize_of_nat(v___x_4911_);
v___x_4917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__2(v_invariants_4909_, v___x_4915_, v___x_4916_, v___x_4912_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
v___y_4884_ = v___y_4908_;
v___y_4885_ = v___y_4907_;
v___y_4886_ = v___y_4902_;
v___y_4887_ = v___y_4905_;
v___y_4888_ = v___y_4906_;
v___y_4889_ = v___y_4901_;
v___y_4890_ = v___x_4917_;
goto v___jp_4883_;
}
}
else
{
size_t v___x_4918_; size_t v___x_4919_; lean_object* v___x_4920_; 
v___x_4918_ = ((size_t)0ULL);
v___x_4919_ = lean_usize_of_nat(v___x_4911_);
v___x_4920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__2(v_invariants_4909_, v___x_4918_, v___x_4919_, v___x_4912_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
v___y_4884_ = v___y_4908_;
v___y_4885_ = v___y_4907_;
v___y_4886_ = v___y_4902_;
v___y_4887_ = v___y_4905_;
v___y_4888_ = v___y_4906_;
v___y_4889_ = v___y_4901_;
v___y_4890_ = v___x_4920_;
goto v___jp_4883_;
}
}
}
}
else
{
lean_object* v_a_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4939_; 
lean_dec(v_invariantAlts_x3f_4856_);
lean_dec(v_stx_4838_);
v_a_4932_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4934_ = v___x_4859_;
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_a_4932_);
lean_dec(v___x_4859_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4937_; 
if (v_isShared_4935_ == 0)
{
v___x_4937_ = v___x_4934_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
else
{
lean_object* v_a_4940_; lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
lean_dec(v_a_4849_);
lean_dec(v_stx_4838_);
v_a_4940_ = lean_ctor_get(v___x_4851_, 0);
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4851_);
if (v_isSharedCheck_4947_ == 0)
{
v___x_4942_ = v___x_4851_;
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
else
{
lean_inc(v_a_4940_);
lean_dec(v___x_4851_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v_a_4940_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
lean_dec(v_stx_4838_);
v_a_4948_ = lean_ctor_get(v___x_4848_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4848_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4848_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4848_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___boxed(lean_object* v_stx_4956_, lean_object* v_a_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen(v_stx_4956_, v_a_4957_, v_a_4958_, v_a_4959_, v_a_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_);
lean_dec(v_a_4964_);
lean_dec_ref(v_a_4963_);
lean_dec(v_a_4962_);
lean_dec_ref(v_a_4961_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
lean_dec(v_a_4958_);
lean_dec_ref(v_a_4957_);
return v_res_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0(lean_object* v_mvarId_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_){
_start:
{
lean_object* v___x_4977_; 
v___x_4977_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0___redArg(v_mvarId_4967_, v___y_4973_);
return v___x_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0___boxed(lean_object* v_mvarId_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_){
_start:
{
lean_object* v_res_4988_; 
v_res_4988_ = l_Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0(v_mvarId_4978_, v___y_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_);
lean_dec(v___y_4986_);
lean_dec_ref(v___y_4985_);
lean_dec(v___y_4984_);
lean_dec_ref(v___y_4983_);
lean_dec(v___y_4982_);
lean_dec_ref(v___y_4981_);
lean_dec(v___y_4980_);
lean_dec_ref(v___y_4979_);
lean_dec(v_mvarId_4978_);
return v_res_4988_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0(lean_object* v_00_u03b2_4989_, lean_object* v_x_4990_, lean_object* v_x_4991_){
_start:
{
uint8_t v___x_4992_; 
v___x_4992_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0___redArg(v_x_4990_, v_x_4991_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4993_, lean_object* v_x_4994_, lean_object* v_x_4995_){
_start:
{
uint8_t v_res_4996_; lean_object* v_r_4997_; 
v_res_4996_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0(v_00_u03b2_4993_, v_x_4994_, v_x_4995_);
lean_dec(v_x_4995_);
lean_dec_ref(v_x_4994_);
v_r_4997_ = lean_box(v_res_4996_);
return v_r_4997_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4998_, lean_object* v_x_4999_, size_t v_x_5000_, lean_object* v_x_5001_){
_start:
{
uint8_t v___x_5002_; 
v___x_5002_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1___redArg(v_x_4999_, v_x_5000_, v_x_5001_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5003_, lean_object* v_x_5004_, lean_object* v_x_5005_, lean_object* v_x_5006_){
_start:
{
size_t v_x_6639__boxed_5007_; uint8_t v_res_5008_; lean_object* v_r_5009_; 
v_x_6639__boxed_5007_ = lean_unbox_usize(v_x_5005_);
lean_dec(v_x_5005_);
v_res_5008_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1(v_00_u03b2_5003_, v_x_5004_, v_x_6639__boxed_5007_, v_x_5006_);
lean_dec(v_x_5006_);
lean_dec_ref(v_x_5004_);
v_r_5009_ = lean_box(v_res_5008_);
return v_r_5009_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_5010_, lean_object* v_keys_5011_, lean_object* v_vals_5012_, lean_object* v_heq_5013_, lean_object* v_i_5014_, lean_object* v_k_5015_){
_start:
{
uint8_t v___x_5016_; 
v___x_5016_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5___redArg(v_keys_5011_, v_i_5014_, v_k_5015_);
return v___x_5016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_5017_, lean_object* v_keys_5018_, lean_object* v_vals_5019_, lean_object* v_heq_5020_, lean_object* v_i_5021_, lean_object* v_k_5022_){
_start:
{
uint8_t v_res_5023_; lean_object* v_r_5024_; 
v_res_5023_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_spec__0_spec__0_spec__1_spec__5(v_00_u03b2_5017_, v_keys_5018_, v_vals_5019_, v_heq_5020_, v_i_5021_, v_k_5022_);
lean_dec(v_k_5022_);
lean_dec_ref(v_vals_5019_);
lean_dec_ref(v_keys_5018_);
v_r_5024_ = lean_box(v_res_5023_);
return v_r_5024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1(){
_start:
{
lean_object* v___x_5085_; lean_object* v___x_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; 
v___x_5085_ = l_Lean_Elab_Tactic_Grind_grindTacElabAttribute;
v___x_5086_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__2));
v___x_5087_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__23));
v___x_5088_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___boxed), 10, 0);
v___x_5089_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5085_, v___x_5086_, v___x_5087_, v___x_5088_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___boxed(lean_object* v_a_5090_){
_start:
{
lean_object* v_res_5091_; 
v_res_5091_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1();
return v_res_5091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_docString__3(){
_start:
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5094_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__23));
v___x_5095_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_docString__3___closed__0));
v___x_5096_ = l_Lean_addBuiltinDocString(v___x_5094_, v___x_5095_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_docString__3___boxed(lean_object* v_a_5097_){
_start:
{
lean_object* v_res_5098_; 
v_res_5098_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_docString__3();
return v_res_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0___redArg(lean_object* v_msg_5099_, lean_object* v___y_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_){
_start:
{
lean_object* v_ref_5105_; lean_object* v___x_5106_; lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5115_; 
v_ref_5105_ = lean_ctor_get(v___y_5102_, 5);
v___x_5106_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__1_spec__1(v_msg_5099_, v___y_5100_, v___y_5101_, v___y_5102_, v___y_5103_);
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5115_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5115_ == 0)
{
v___x_5109_ = v___x_5106_;
v_isShared_5110_ = v_isSharedCheck_5115_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_5106_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5115_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5111_; lean_object* v___x_5113_; 
lean_inc(v_ref_5105_);
v___x_5111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5111_, 0, v_ref_5105_);
lean_ctor_set(v___x_5111_, 1, v_a_5107_);
if (v_isShared_5110_ == 0)
{
lean_ctor_set_tag(v___x_5109_, 1);
lean_ctor_set(v___x_5109_, 0, v___x_5111_);
v___x_5113_ = v___x_5109_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v___x_5111_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
return v___x_5113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0___redArg___boxed(lean_object* v_msg_5116_, lean_object* v___y_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0___redArg(v_msg_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_);
lean_dec(v___y_5120_);
lean_dec_ref(v___y_5119_);
lean_dec(v___y_5118_);
lean_dec_ref(v___y_5117_);
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0___redArg(lean_object* v_ref_5123_, lean_object* v_msg_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v_fileName_5134_; lean_object* v_fileMap_5135_; lean_object* v_options_5136_; lean_object* v_currRecDepth_5137_; lean_object* v_maxRecDepth_5138_; lean_object* v_ref_5139_; lean_object* v_currNamespace_5140_; lean_object* v_openDecls_5141_; lean_object* v_initHeartbeats_5142_; lean_object* v_maxHeartbeats_5143_; lean_object* v_quotContext_5144_; lean_object* v_currMacroScope_5145_; uint8_t v_diag_5146_; lean_object* v_cancelTk_x3f_5147_; uint8_t v_suppressElabErrors_5148_; lean_object* v_inheritedTraceOptions_5149_; lean_object* v_ref_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
v_fileName_5134_ = lean_ctor_get(v___y_5131_, 0);
v_fileMap_5135_ = lean_ctor_get(v___y_5131_, 1);
v_options_5136_ = lean_ctor_get(v___y_5131_, 2);
v_currRecDepth_5137_ = lean_ctor_get(v___y_5131_, 3);
v_maxRecDepth_5138_ = lean_ctor_get(v___y_5131_, 4);
v_ref_5139_ = lean_ctor_get(v___y_5131_, 5);
v_currNamespace_5140_ = lean_ctor_get(v___y_5131_, 6);
v_openDecls_5141_ = lean_ctor_get(v___y_5131_, 7);
v_initHeartbeats_5142_ = lean_ctor_get(v___y_5131_, 8);
v_maxHeartbeats_5143_ = lean_ctor_get(v___y_5131_, 9);
v_quotContext_5144_ = lean_ctor_get(v___y_5131_, 10);
v_currMacroScope_5145_ = lean_ctor_get(v___y_5131_, 11);
v_diag_5146_ = lean_ctor_get_uint8(v___y_5131_, sizeof(void*)*14);
v_cancelTk_x3f_5147_ = lean_ctor_get(v___y_5131_, 12);
v_suppressElabErrors_5148_ = lean_ctor_get_uint8(v___y_5131_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5149_ = lean_ctor_get(v___y_5131_, 13);
v_ref_5150_ = l_Lean_replaceRef(v_ref_5123_, v_ref_5139_);
lean_inc_ref(v_inheritedTraceOptions_5149_);
lean_inc(v_cancelTk_x3f_5147_);
lean_inc(v_currMacroScope_5145_);
lean_inc(v_quotContext_5144_);
lean_inc(v_maxHeartbeats_5143_);
lean_inc(v_initHeartbeats_5142_);
lean_inc(v_openDecls_5141_);
lean_inc(v_currNamespace_5140_);
lean_inc(v_maxRecDepth_5138_);
lean_inc(v_currRecDepth_5137_);
lean_inc_ref(v_options_5136_);
lean_inc_ref(v_fileMap_5135_);
lean_inc_ref(v_fileName_5134_);
v___x_5151_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5151_, 0, v_fileName_5134_);
lean_ctor_set(v___x_5151_, 1, v_fileMap_5135_);
lean_ctor_set(v___x_5151_, 2, v_options_5136_);
lean_ctor_set(v___x_5151_, 3, v_currRecDepth_5137_);
lean_ctor_set(v___x_5151_, 4, v_maxRecDepth_5138_);
lean_ctor_set(v___x_5151_, 5, v_ref_5150_);
lean_ctor_set(v___x_5151_, 6, v_currNamespace_5140_);
lean_ctor_set(v___x_5151_, 7, v_openDecls_5141_);
lean_ctor_set(v___x_5151_, 8, v_initHeartbeats_5142_);
lean_ctor_set(v___x_5151_, 9, v_maxHeartbeats_5143_);
lean_ctor_set(v___x_5151_, 10, v_quotContext_5144_);
lean_ctor_set(v___x_5151_, 11, v_currMacroScope_5145_);
lean_ctor_set(v___x_5151_, 12, v_cancelTk_x3f_5147_);
lean_ctor_set(v___x_5151_, 13, v_inheritedTraceOptions_5149_);
lean_ctor_set_uint8(v___x_5151_, sizeof(void*)*14, v_diag_5146_);
lean_ctor_set_uint8(v___x_5151_, sizeof(void*)*14 + 1, v_suppressElabErrors_5148_);
v___x_5152_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0___redArg(v_msg_5124_, v___y_5129_, v___y_5130_, v___x_5151_, v___y_5132_);
lean_dec_ref_known(v___x_5151_, 14);
return v___x_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0___redArg___boxed(lean_object* v_ref_5153_, lean_object* v_msg_5154_, lean_object* v___y_5155_, lean_object* v___y_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_){
_start:
{
lean_object* v_res_5164_; 
v_res_5164_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0___redArg(v_ref_5153_, v_msg_5154_, v___y_5155_, v___y_5156_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_);
lean_dec(v___y_5162_);
lean_dec_ref(v___y_5161_);
lean_dec(v___y_5160_);
lean_dec_ref(v___y_5159_);
lean_dec(v___y_5158_);
lean_dec_ref(v___y_5157_);
lean_dec(v___y_5156_);
lean_dec_ref(v___y_5155_);
lean_dec(v_ref_5153_);
return v_res_5164_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__3(void){
_start:
{
lean_object* v___x_5172_; lean_object* v___x_5173_; 
v___x_5172_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__2));
v___x_5173_ = l_Lean_stringToMessageData(v___x_5172_);
return v___x_5173_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__5(void){
_start:
{
lean_object* v___x_5175_; lean_object* v___x_5176_; 
v___x_5175_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__4));
v___x_5176_ = l_Lean_stringToMessageData(v___x_5175_);
return v___x_5176_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__6(void){
_start:
{
lean_object* v___x_5177_; lean_object* v___x_5178_; 
v___x_5177_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__5, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__5_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__5);
v___x_5178_ = l_Lean_MessageData_hint_x27(v___x_5177_);
return v___x_5178_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__7(void){
_start:
{
lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
v___x_5179_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__6, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__6_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__6);
v___x_5180_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__3, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__3_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__3);
v___x_5181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5181_, 0, v___x_5180_);
lean_ctor_set(v___x_5181_, 1, v___x_5179_);
return v___x_5181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge(lean_object* v_w_x3f_5182_, lean_object* v_a_5183_, lean_object* v_a_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_, lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_){
_start:
{
if (lean_obj_tag(v_w_x3f_5182_) == 0)
{
lean_object* v___x_5192_; 
v___x_5192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5192_, 0, v_w_x3f_5182_);
return v___x_5192_;
}
else
{
lean_object* v_val_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5208_; 
v_val_5193_ = lean_ctor_get(v_w_x3f_5182_, 0);
v_isSharedCheck_5208_ = !lean_is_exclusive(v_w_x3f_5182_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5195_ = v_w_x3f_5182_;
v_isShared_5196_ = v_isSharedCheck_5208_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_val_5193_);
lean_dec(v_w_x3f_5182_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5208_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5197_; lean_object* v___x_5198_; uint8_t v___x_5199_; 
lean_inc(v_val_5193_);
v___x_5197_ = l_Lean_Syntax_getKind(v_val_5193_);
v___x_5198_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__1));
v___x_5199_ = lean_name_eq(v___x_5197_, v___x_5198_);
lean_dec(v___x_5197_);
if (v___x_5199_ == 0)
{
lean_object* v___x_5200_; lean_object* v___x_5201_; 
lean_del_object(v___x_5195_);
v___x_5200_ = lean_obj_once(&l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__7, &l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__7_once, _init_l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___closed__7);
v___x_5201_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0___redArg(v_val_5193_, v___x_5200_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_, v_a_5188_, v_a_5189_, v_a_5190_);
lean_dec(v_val_5193_);
return v___x_5201_;
}
else
{
lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5205_; 
v___x_5202_ = lean_unsigned_to_nat(0u);
v___x_5203_ = l_Lean_Syntax_getArg(v_val_5193_, v___x_5202_);
lean_dec(v_val_5193_);
if (v_isShared_5196_ == 0)
{
lean_ctor_set(v___x_5195_, 0, v___x_5203_);
v___x_5205_ = v___x_5195_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5207_; 
v_reuseFailAlloc_5207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5207_, 0, v___x_5203_);
v___x_5205_ = v_reuseFailAlloc_5207_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
lean_object* v___x_5206_; 
v___x_5206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5206_, 0, v___x_5205_);
return v___x_5206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge___boxed(lean_object* v_w_x3f_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge(v_w_x3f_5209_, v_a_5210_, v_a_5211_, v_a_5212_, v_a_5213_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec(v_a_5213_);
lean_dec_ref(v_a_5212_);
lean_dec(v_a_5211_);
lean_dec_ref(v_a_5210_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0(lean_object* v_00_u03b1_5220_, lean_object* v_ref_5221_, lean_object* v_msg_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_){
_start:
{
lean_object* v___x_5232_; 
v___x_5232_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0___redArg(v_ref_5221_, v_msg_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0___boxed(lean_object* v_00_u03b1_5233_, lean_object* v_ref_5234_, lean_object* v_msg_5235_, lean_object* v___y_5236_, lean_object* v___y_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v_res_5245_; 
v_res_5245_ = l_Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0(v_00_u03b1_5233_, v_ref_5234_, v_msg_5235_, v___y_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
lean_dec(v___y_5243_);
lean_dec_ref(v___y_5242_);
lean_dec(v___y_5241_);
lean_dec_ref(v___y_5240_);
lean_dec(v___y_5239_);
lean_dec_ref(v___y_5238_);
lean_dec(v___y_5237_);
lean_dec_ref(v___y_5236_);
lean_dec(v_ref_5234_);
return v_res_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0(lean_object* v_00_u03b1_5246_, lean_object* v_msg_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_, lean_object* v___y_5251_, lean_object* v___y_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_){
_start:
{
lean_object* v___x_5257_; 
v___x_5257_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0___redArg(v_msg_5247_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_);
return v___x_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0___boxed(lean_object* v_00_u03b1_5258_, lean_object* v_msg_5259_, lean_object* v___y_5260_, lean_object* v___y_5261_, lean_object* v___y_5262_, lean_object* v___y_5263_, lean_object* v___y_5264_, lean_object* v___y_5265_, lean_object* v___y_5266_, lean_object* v___y_5267_, lean_object* v___y_5268_){
_start:
{
lean_object* v_res_5269_; 
v_res_5269_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge_spec__0_spec__0(v_00_u03b1_5258_, v_msg_5259_, v___y_5260_, v___y_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_);
lean_dec(v___y_5267_);
lean_dec_ref(v___y_5266_);
lean_dec(v___y_5265_);
lean_dec_ref(v___y_5264_);
lean_dec(v___y_5263_);
lean_dec_ref(v___y_5262_);
lean_dec(v___y_5261_);
lean_dec_ref(v___y_5260_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg(){
_start:
{
lean_object* v___x_5271_; lean_object* v___x_5272_; 
v___x_5271_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__0___redArg___closed__0);
v___x_5272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5272_, 0, v___x_5271_);
return v___x_5272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg___boxed(lean_object* v___y_5273_){
_start:
{
lean_object* v_res_5274_; 
v_res_5274_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg();
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0(lean_object* v_00_u03b1_5275_, lean_object* v___y_5276_, lean_object* v___y_5277_, lean_object* v___y_5278_, lean_object* v___y_5279_, lean_object* v___y_5280_, lean_object* v___y_5281_, lean_object* v___y_5282_, lean_object* v___y_5283_){
_start:
{
lean_object* v___x_5285_; 
v___x_5285_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg();
return v___x_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___boxed(lean_object* v_00_u03b1_5286_, lean_object* v___y_5287_, lean_object* v___y_5288_, lean_object* v___y_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_, lean_object* v___y_5295_){
_start:
{
lean_object* v_res_5296_; 
v_res_5296_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0(v_00_u03b1_5286_, v___y_5287_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
lean_dec(v___y_5294_);
lean_dec_ref(v___y_5293_);
lean_dec(v___y_5292_);
lean_dec_ref(v___y_5291_);
lean_dec(v___y_5290_);
lean_dec_ref(v___y_5289_);
lean_dec(v___y_5288_);
lean_dec_ref(v___y_5287_);
return v_res_5296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0(lean_object* v_x_5299_, lean_object* v_x_5300_){
_start:
{
lean_object* v___x_5301_; 
v___x_5301_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___closed__0));
return v___x_5301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___boxed(lean_object* v_x_5302_, lean_object* v_x_5303_){
_start:
{
lean_object* v_res_5304_; 
v_res_5304_ = l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0(v_x_5302_, v_x_5303_);
lean_dec(v_x_5303_);
lean_dec(v_x_5302_);
return v_res_5304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__1(lean_object* v_00___5305_){
_start:
{
lean_object* v___x_5306_; 
v___x_5306_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___closed__0));
return v___x_5306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__2(lean_object* v_x_5307_){
_start:
{
lean_object* v___x_5308_; lean_object* v___x_5309_; 
v___x_5308_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___closed__0));
v___x_5309_ = lean_array_push(v___x_5308_, v_x_5307_);
return v___x_5309_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__1(lean_object* v_a_5310_, lean_object* v_a_5311_){
_start:
{
if (lean_obj_tag(v_a_5310_) == 0)
{
lean_object* v___x_5312_; 
v___x_5312_ = l_List_reverse___redArg(v_a_5311_);
return v___x_5312_;
}
else
{
lean_object* v_head_5313_; lean_object* v_tail_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5323_; 
v_head_5313_ = lean_ctor_get(v_a_5310_, 0);
v_tail_5314_ = lean_ctor_get(v_a_5310_, 1);
v_isSharedCheck_5323_ = !lean_is_exclusive(v_a_5310_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5316_ = v_a_5310_;
v_isShared_5317_ = v_isSharedCheck_5323_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_tail_5314_);
lean_inc(v_head_5313_);
lean_dec(v_a_5310_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5323_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v_mvarId_5318_; lean_object* v___x_5320_; 
v_mvarId_5318_ = lean_ctor_get(v_head_5313_, 1);
lean_inc(v_mvarId_5318_);
lean_dec(v_head_5313_);
if (v_isShared_5317_ == 0)
{
lean_ctor_set(v___x_5316_, 1, v_a_5311_);
lean_ctor_set(v___x_5316_, 0, v_mvarId_5318_);
v___x_5320_ = v___x_5316_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_mvarId_5318_);
lean_ctor_set(v_reuseFailAlloc_5322_, 1, v_a_5311_);
v___x_5320_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
v_a_5310_ = v_tail_5314_;
v_a_5311_ = v___x_5320_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__5(void){
_start:
{
lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5329_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__4));
v___x_5330_ = l_String_toRawSubstring_x27(v___x_5329_);
return v___x_5330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3(uint8_t v___x_5333_, lean_object* v_stx_5334_, lean_object* v___x_5335_, lean_object* v___x_5336_, lean_object* v___x_5337_, uint8_t v___x_5338_, lean_object* v___f_5339_, lean_object* v___f_5340_, lean_object* v___f_5341_, lean_object* v___x_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_){
_start:
{
lean_object* v___y_5353_; lean_object* v_step_5354_; lean_object* v___y_5355_; lean_object* v___y_5356_; lean_object* v___y_5357_; lean_object* v___y_5358_; lean_object* v___y_5359_; lean_object* v___y_5360_; lean_object* v___y_5361_; lean_object* v___y_5362_; lean_object* v___y_5411_; lean_object* v___y_5412_; lean_object* v___y_5413_; lean_object* v___y_5414_; lean_object* v___y_5415_; lean_object* v___y_5416_; lean_object* v___y_5417_; lean_object* v___y_5418_; lean_object* v___y_5419_; lean_object* v___y_5420_; lean_object* v___y_5421_; lean_object* v___y_5422_; lean_object* v___y_5423_; lean_object* v___y_5424_; lean_object* v___y_5425_; lean_object* v___y_5426_; lean_object* v___y_5427_; lean_object* v___y_5428_; lean_object* v___y_5429_; lean_object* v___y_5430_; lean_object* v___y_5431_; lean_object* v___y_5442_; lean_object* v___y_5443_; lean_object* v___y_5444_; lean_object* v___y_5445_; lean_object* v___y_5446_; lean_object* v___y_5447_; lean_object* v___y_5448_; lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5451_; lean_object* v___y_5452_; lean_object* v___y_5453_; lean_object* v___y_5454_; lean_object* v___y_5455_; lean_object* v___y_5456_; lean_object* v___y_5457_; lean_object* v___y_5458_; lean_object* v___y_5459_; lean_object* v___y_5460_; lean_object* v___y_5461_; lean_object* v___y_5462_; lean_object* v___y_5463_; lean_object* v___y_5464_; 
if (v___x_5333_ == 0)
{
lean_object* v___x_5468_; 
lean_dec_ref(v___x_5342_);
lean_dec_ref(v___f_5341_);
lean_dec_ref(v___f_5340_);
lean_dec_ref(v___f_5339_);
lean_dec_ref(v___x_5337_);
lean_dec_ref(v___x_5336_);
lean_dec_ref(v___x_5335_);
v___x_5468_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg();
return v___x_5468_;
}
else
{
lean_object* v___x_5469_; lean_object* v_cfg_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; uint8_t v___x_5473_; 
v___x_5469_ = lean_unsigned_to_nat(1u);
v_cfg_5470_ = l_Lean_Syntax_getArg(v_stx_5334_, v___x_5469_);
v___x_5471_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__6));
lean_inc_ref(v___x_5337_);
lean_inc_ref(v___x_5336_);
lean_inc_ref(v___x_5335_);
v___x_5472_ = l_Lean_Name_mkStr4(v___x_5335_, v___x_5336_, v___x_5337_, v___x_5471_);
lean_inc(v_cfg_5470_);
v___x_5473_ = l_Lean_Syntax_isOfKind(v_cfg_5470_, v___x_5472_);
if (v___x_5473_ == 0)
{
lean_object* v___x_5474_; 
lean_dec(v___x_5472_);
lean_dec(v_cfg_5470_);
lean_dec_ref(v___x_5342_);
lean_dec_ref(v___f_5341_);
lean_dec_ref(v___f_5340_);
lean_dec_ref(v___f_5339_);
lean_dec_ref(v___x_5337_);
lean_dec_ref(v___x_5336_);
lean_dec_ref(v___x_5335_);
v___x_5474_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg();
return v___x_5474_;
}
else
{
lean_object* v___x_5475_; lean_object* v___y_5477_; lean_object* v___y_5478_; lean_object* v___y_5479_; lean_object* v___y_5480_; lean_object* v___y_5481_; lean_object* v___y_5482_; lean_object* v___y_5483_; lean_object* v___y_5484_; lean_object* v___y_5485_; lean_object* v___y_5486_; lean_object* v___y_5487_; lean_object* v___y_5488_; lean_object* v___y_5489_; lean_object* v___y_5490_; lean_object* v___y_5491_; lean_object* v___y_5492_; lean_object* v___y_5493_; lean_object* v___y_5494_; lean_object* v___y_5495_; lean_object* v___y_5496_; lean_object* v___y_5497_; lean_object* v___y_5498_; lean_object* v___y_5499_; lean_object* v___y_5512_; lean_object* v___y_5513_; lean_object* v___y_5514_; lean_object* v___y_5515_; lean_object* v___y_5516_; lean_object* v___y_5517_; lean_object* v___y_5518_; lean_object* v___y_5519_; lean_object* v___y_5520_; lean_object* v___y_5521_; lean_object* v___y_5522_; lean_object* v___y_5523_; lean_object* v___y_5524_; lean_object* v___y_5525_; lean_object* v___y_5526_; lean_object* v___y_5527_; lean_object* v___y_5528_; lean_object* v___y_5529_; lean_object* v___y_5530_; lean_object* v___y_5531_; lean_object* v___y_5532_; lean_object* v___y_5533_; lean_object* v___y_5547_; lean_object* v___y_5548_; lean_object* v___y_5549_; lean_object* v___y_5550_; lean_object* v___y_5551_; lean_object* v___y_5552_; lean_object* v___y_5553_; lean_object* v___y_5554_; lean_object* v___y_5555_; lean_object* v___y_5556_; lean_object* v___y_5557_; lean_object* v___y_5558_; lean_object* v___y_5559_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v___y_5562_; lean_object* v___y_5563_; lean_object* v___y_5564_; lean_object* v___y_5565_; lean_object* v___y_5566_; lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5576_; lean_object* v___y_5577_; lean_object* v___y_5578_; lean_object* v___y_5579_; lean_object* v___y_5580_; lean_object* v___y_5581_; lean_object* v___y_5582_; lean_object* v___y_5583_; lean_object* v___y_5584_; lean_object* v___y_5585_; lean_object* v___y_5586_; lean_object* v___y_5587_; lean_object* v___y_5588_; lean_object* v___y_5589_; lean_object* v___y_5590_; lean_object* v___y_5591_; lean_object* v___y_5592_; lean_object* v___y_5593_; lean_object* v___y_5594_; lean_object* v___y_5595_; lean_object* v___y_5596_; lean_object* v___y_5597_; lean_object* v_tk_5605_; lean_object* v___y_5607_; lean_object* v___y_5608_; lean_object* v___y_5609_; lean_object* v___y_5610_; lean_object* v___y_5611_; lean_object* v___y_5612_; lean_object* v___y_5613_; lean_object* v_cfg_5614_; lean_object* v___y_5615_; lean_object* v___y_5616_; lean_object* v___y_5617_; lean_object* v___y_5618_; lean_object* v___y_5619_; lean_object* v___y_5620_; lean_object* v___y_5621_; lean_object* v_ref_5622_; lean_object* v___y_5623_; lean_object* v___y_5642_; lean_object* v___y_5643_; lean_object* v___y_5644_; lean_object* v___y_5645_; lean_object* v___y_5646_; lean_object* v___y_5647_; lean_object* v___y_5648_; lean_object* v___y_5649_; lean_object* v___y_5650_; lean_object* v___y_5651_; lean_object* v___y_5652_; lean_object* v___y_5653_; lean_object* v___y_5654_; lean_object* v___y_5655_; lean_object* v___y_5656_; lean_object* v___y_5691_; lean_object* v___y_5692_; lean_object* v___y_5693_; lean_object* v___y_5694_; lean_object* v___y_5695_; lean_object* v___y_5696_; lean_object* v_w_5697_; lean_object* v___y_5698_; lean_object* v___y_5699_; lean_object* v___y_5700_; lean_object* v___y_5701_; lean_object* v___y_5702_; lean_object* v___y_5703_; lean_object* v___y_5704_; lean_object* v___y_5705_; lean_object* v___x_5716_; lean_object* v___y_5718_; lean_object* v___y_5719_; lean_object* v___y_5720_; lean_object* v___y_5721_; lean_object* v_sa_5722_; lean_object* v_thms_5723_; lean_object* v___y_5724_; lean_object* v___y_5725_; lean_object* v___y_5726_; lean_object* v___y_5727_; lean_object* v___y_5728_; lean_object* v___y_5729_; lean_object* v___y_5730_; lean_object* v___y_5731_; lean_object* v___y_5741_; lean_object* v___y_5742_; lean_object* v___y_5743_; lean_object* v___y_5744_; lean_object* v___y_5745_; lean_object* v___y_5746_; lean_object* v___y_5747_; lean_object* v___y_5748_; lean_object* v___y_5749_; lean_object* v___y_5750_; lean_object* v___y_5751_; lean_object* v___y_5752_; lean_object* v___y_5753_; lean_object* v___y_5754_; lean_object* v___y_5758_; lean_object* v___y_5759_; lean_object* v___y_5760_; lean_object* v___y_5761_; lean_object* v___y_5762_; lean_object* v_thms_5763_; lean_object* v___y_5764_; lean_object* v___y_5765_; lean_object* v___y_5766_; lean_object* v___y_5767_; lean_object* v___y_5768_; lean_object* v___y_5769_; lean_object* v___y_5770_; lean_object* v___y_5771_; lean_object* v___y_5783_; lean_object* v___y_5784_; lean_object* v_u_5785_; lean_object* v___y_5786_; lean_object* v___y_5787_; lean_object* v___y_5788_; lean_object* v___y_5789_; lean_object* v___y_5790_; lean_object* v___y_5791_; lean_object* v___y_5792_; lean_object* v___y_5793_; lean_object* v_lems_5812_; lean_object* v___y_5813_; lean_object* v___y_5814_; lean_object* v___y_5815_; lean_object* v___y_5816_; lean_object* v___y_5817_; lean_object* v___y_5818_; lean_object* v___y_5819_; lean_object* v___y_5820_; lean_object* v___x_5829_; uint8_t v___x_5830_; 
v___x_5475_ = lean_unsigned_to_nat(0u);
v_tk_5605_ = l_Lean_Syntax_getArg(v_stx_5334_, v___x_5475_);
v___x_5716_ = lean_unsigned_to_nat(2u);
v___x_5829_ = l_Lean_Syntax_getArg(v_stx_5334_, v___x_5716_);
v___x_5830_ = l_Lean_Syntax_isNone(v___x_5829_);
if (v___x_5830_ == 0)
{
lean_object* v___x_5831_; uint8_t v___x_5832_; 
v___x_5831_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_5829_);
v___x_5832_ = l_Lean_Syntax_matchesNull(v___x_5829_, v___x_5831_);
if (v___x_5832_ == 0)
{
lean_object* v___x_5833_; 
lean_dec(v___x_5829_);
lean_dec(v_tk_5605_);
lean_dec(v___x_5472_);
lean_dec(v_cfg_5470_);
lean_dec_ref(v___x_5342_);
lean_dec_ref(v___f_5341_);
lean_dec_ref(v___f_5340_);
lean_dec_ref(v___f_5339_);
lean_dec_ref(v___x_5337_);
lean_dec_ref(v___x_5336_);
lean_dec_ref(v___x_5335_);
v___x_5833_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg();
return v___x_5833_;
}
else
{
lean_object* v___x_5834_; lean_object* v_lems_5835_; lean_object* v___x_5836_; 
v___x_5834_ = l_Lean_Syntax_getArg(v___x_5829_, v___x_5469_);
lean_dec(v___x_5829_);
v_lems_5835_ = l_Lean_Syntax_getArgs(v___x_5834_);
lean_dec(v___x_5834_);
v___x_5836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5836_, 0, v_lems_5835_);
v_lems_5812_ = v___x_5836_;
v___y_5813_ = v___y_5343_;
v___y_5814_ = v___y_5344_;
v___y_5815_ = v___y_5345_;
v___y_5816_ = v___y_5346_;
v___y_5817_ = v___y_5347_;
v___y_5818_ = v___y_5348_;
v___y_5819_ = v___y_5349_;
v___y_5820_ = v___y_5350_;
goto v___jp_5811_;
}
}
else
{
lean_object* v___x_5837_; 
lean_dec(v___x_5829_);
v___x_5837_ = lean_box(0);
v_lems_5812_ = v___x_5837_;
v___y_5813_ = v___y_5343_;
v___y_5814_ = v___y_5344_;
v___y_5815_ = v___y_5345_;
v___y_5816_ = v___y_5346_;
v___y_5817_ = v___y_5347_;
v___y_5818_ = v___y_5348_;
v___y_5819_ = v___y_5349_;
v___y_5820_ = v___y_5350_;
goto v___jp_5811_;
}
v___jp_5476_:
{
lean_object* v___x_5500_; lean_object* v___x_5501_; 
lean_inc_ref(v___y_5486_);
v___x_5500_ = l_Array_append___redArg(v___y_5486_, v___y_5499_);
lean_dec_ref(v___y_5499_);
lean_inc(v___y_5490_);
lean_inc(v___y_5491_);
v___x_5501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5501_, 0, v___y_5491_);
lean_ctor_set(v___x_5501_, 1, v___y_5490_);
lean_ctor_set(v___x_5501_, 2, v___x_5500_);
if (lean_obj_tag(v___y_5488_) == 1)
{
lean_object* v_val_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5508_; lean_object* v___x_5509_; 
v_val_5502_ = lean_ctor_get(v___y_5488_, 0);
lean_inc(v_val_5502_);
lean_dec_ref_known(v___y_5488_, 1);
v___x_5503_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25));
lean_inc_n(v___y_5491_, 3);
v___x_5504_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5504_, 0, v___y_5491_);
lean_ctor_set(v___x_5504_, 1, v___x_5503_);
lean_inc_ref(v___y_5486_);
v___x_5505_ = l_Array_append___redArg(v___y_5486_, v_val_5502_);
lean_dec(v_val_5502_);
lean_inc(v___y_5490_);
v___x_5506_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5506_, 0, v___y_5491_);
lean_ctor_set(v___x_5506_, 1, v___y_5490_);
lean_ctor_set(v___x_5506_, 2, v___x_5505_);
v___x_5507_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27));
v___x_5508_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5508_, 0, v___y_5491_);
lean_ctor_set(v___x_5508_, 1, v___x_5507_);
v___x_5509_ = l_Array_mkArray3___redArg(v___x_5504_, v___x_5506_, v___x_5508_);
v___y_5442_ = v___y_5477_;
v___y_5443_ = v___y_5478_;
v___y_5444_ = v___y_5479_;
v___y_5445_ = v___y_5480_;
v___y_5446_ = v___y_5481_;
v___y_5447_ = v___y_5482_;
v___y_5448_ = v___y_5483_;
v___y_5449_ = v___y_5484_;
v___y_5450_ = v___x_5501_;
v___y_5451_ = v___y_5485_;
v___y_5452_ = v___y_5487_;
v___y_5453_ = v___y_5486_;
v___y_5454_ = v___y_5489_;
v___y_5455_ = v___y_5490_;
v___y_5456_ = v___y_5491_;
v___y_5457_ = v___y_5492_;
v___y_5458_ = v___y_5493_;
v___y_5459_ = v___y_5495_;
v___y_5460_ = v___y_5494_;
v___y_5461_ = v___y_5497_;
v___y_5462_ = v___y_5496_;
v___y_5463_ = v___y_5498_;
v___y_5464_ = v___x_5509_;
goto v___jp_5441_;
}
else
{
lean_object* v___x_5510_; 
lean_dec(v___y_5488_);
v___x_5510_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___closed__0));
v___y_5442_ = v___y_5477_;
v___y_5443_ = v___y_5478_;
v___y_5444_ = v___y_5479_;
v___y_5445_ = v___y_5480_;
v___y_5446_ = v___y_5481_;
v___y_5447_ = v___y_5482_;
v___y_5448_ = v___y_5483_;
v___y_5449_ = v___y_5484_;
v___y_5450_ = v___x_5501_;
v___y_5451_ = v___y_5485_;
v___y_5452_ = v___y_5487_;
v___y_5453_ = v___y_5486_;
v___y_5454_ = v___y_5489_;
v___y_5455_ = v___y_5490_;
v___y_5456_ = v___y_5491_;
v___y_5457_ = v___y_5492_;
v___y_5458_ = v___y_5493_;
v___y_5459_ = v___y_5495_;
v___y_5460_ = v___y_5494_;
v___y_5461_ = v___y_5497_;
v___y_5462_ = v___y_5496_;
v___y_5463_ = v___y_5498_;
v___y_5464_ = v___x_5510_;
goto v___jp_5441_;
}
}
v___jp_5511_:
{
lean_object* v___x_5534_; lean_object* v___x_5535_; 
lean_inc_ref(v___y_5519_);
v___x_5534_ = l_Array_append___redArg(v___y_5519_, v___y_5533_);
lean_dec_ref(v___y_5533_);
lean_inc(v___y_5523_);
lean_inc(v___y_5524_);
v___x_5535_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5535_, 0, v___y_5524_);
lean_ctor_set(v___x_5535_, 1, v___y_5523_);
lean_ctor_set(v___x_5535_, 2, v___x_5534_);
if (lean_obj_tag(v___y_5522_) == 1)
{
if (lean_obj_tag(v___y_5529_) == 1)
{
lean_object* v_val_5536_; lean_object* v_val_5537_; lean_object* v___x_5538_; lean_object* v___x_5539_; 
lean_dec_ref(v___f_5341_);
v_val_5536_ = lean_ctor_get(v___y_5522_, 0);
lean_inc(v_val_5536_);
lean_dec_ref_known(v___y_5522_, 1);
v_val_5537_ = lean_ctor_get(v___y_5529_, 0);
lean_inc(v_val_5537_);
lean_dec_ref_known(v___y_5529_, 1);
v___x_5538_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__2));
lean_inc(v___y_5524_);
v___x_5539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5539_, 0, v___y_5524_);
lean_ctor_set(v___x_5539_, 1, v___x_5538_);
if (lean_obj_tag(v_val_5536_) == 0)
{
lean_object* v___x_5540_; lean_object* v___x_5541_; 
lean_dec_ref(v___f_5340_);
v___x_5540_ = lean_box(0);
v___x_5541_ = lean_apply_1(v___f_5339_, v___x_5540_);
v___y_5477_ = v___y_5512_;
v___y_5478_ = v___y_5513_;
v___y_5479_ = v___y_5514_;
v___y_5480_ = v___x_5539_;
v___y_5481_ = v___y_5515_;
v___y_5482_ = v___y_5516_;
v___y_5483_ = v___y_5517_;
v___y_5484_ = v___y_5518_;
v___y_5485_ = v___x_5535_;
v___y_5486_ = v___y_5519_;
v___y_5487_ = v___y_5520_;
v___y_5488_ = v_val_5537_;
v___y_5489_ = v___y_5521_;
v___y_5490_ = v___y_5523_;
v___y_5491_ = v___y_5524_;
v___y_5492_ = v___y_5525_;
v___y_5493_ = v___y_5526_;
v___y_5494_ = v___y_5528_;
v___y_5495_ = v___y_5527_;
v___y_5496_ = v___y_5531_;
v___y_5497_ = v___y_5530_;
v___y_5498_ = v___y_5532_;
v___y_5499_ = v___x_5541_;
goto v___jp_5476_;
}
else
{
lean_object* v_val_5542_; lean_object* v___x_5543_; 
lean_dec_ref(v___f_5339_);
v_val_5542_ = lean_ctor_get(v_val_5536_, 0);
lean_inc(v_val_5542_);
lean_dec_ref_known(v_val_5536_, 1);
v___x_5543_ = lean_apply_1(v___f_5340_, v_val_5542_);
v___y_5477_ = v___y_5512_;
v___y_5478_ = v___y_5513_;
v___y_5479_ = v___y_5514_;
v___y_5480_ = v___x_5539_;
v___y_5481_ = v___y_5515_;
v___y_5482_ = v___y_5516_;
v___y_5483_ = v___y_5517_;
v___y_5484_ = v___y_5518_;
v___y_5485_ = v___x_5535_;
v___y_5486_ = v___y_5519_;
v___y_5487_ = v___y_5520_;
v___y_5488_ = v_val_5537_;
v___y_5489_ = v___y_5521_;
v___y_5490_ = v___y_5523_;
v___y_5491_ = v___y_5524_;
v___y_5492_ = v___y_5525_;
v___y_5493_ = v___y_5526_;
v___y_5494_ = v___y_5528_;
v___y_5495_ = v___y_5527_;
v___y_5496_ = v___y_5531_;
v___y_5497_ = v___y_5530_;
v___y_5498_ = v___y_5532_;
v___y_5499_ = v___x_5543_;
goto v___jp_5476_;
}
}
else
{
lean_object* v___x_5544_; 
lean_dec_ref(v___f_5340_);
lean_dec_ref(v___f_5339_);
v___x_5544_ = lean_apply_2(v___f_5341_, v___y_5522_, v___y_5529_);
v___y_5411_ = v___y_5512_;
v___y_5412_ = v___y_5513_;
v___y_5413_ = v___y_5514_;
v___y_5414_ = v___y_5515_;
v___y_5415_ = v___y_5516_;
v___y_5416_ = v___y_5517_;
v___y_5417_ = v___y_5518_;
v___y_5418_ = v___x_5535_;
v___y_5419_ = v___y_5520_;
v___y_5420_ = v___y_5519_;
v___y_5421_ = v___y_5521_;
v___y_5422_ = v___y_5523_;
v___y_5423_ = v___y_5524_;
v___y_5424_ = v___y_5525_;
v___y_5425_ = v___y_5526_;
v___y_5426_ = v___y_5528_;
v___y_5427_ = v___y_5527_;
v___y_5428_ = v___y_5531_;
v___y_5429_ = v___y_5530_;
v___y_5430_ = v___y_5532_;
v___y_5431_ = v___x_5544_;
goto v___jp_5410_;
}
}
else
{
lean_object* v___x_5545_; 
lean_dec_ref(v___f_5340_);
lean_dec_ref(v___f_5339_);
v___x_5545_ = lean_apply_2(v___f_5341_, v___y_5522_, v___y_5529_);
v___y_5411_ = v___y_5512_;
v___y_5412_ = v___y_5513_;
v___y_5413_ = v___y_5514_;
v___y_5414_ = v___y_5515_;
v___y_5415_ = v___y_5516_;
v___y_5416_ = v___y_5517_;
v___y_5417_ = v___y_5518_;
v___y_5418_ = v___x_5535_;
v___y_5419_ = v___y_5520_;
v___y_5420_ = v___y_5519_;
v___y_5421_ = v___y_5521_;
v___y_5422_ = v___y_5523_;
v___y_5423_ = v___y_5524_;
v___y_5424_ = v___y_5525_;
v___y_5425_ = v___y_5526_;
v___y_5426_ = v___y_5528_;
v___y_5427_ = v___y_5527_;
v___y_5428_ = v___y_5531_;
v___y_5429_ = v___y_5530_;
v___y_5430_ = v___y_5532_;
v___y_5431_ = v___x_5545_;
goto v___jp_5410_;
}
}
v___jp_5546_:
{
lean_object* v___x_5569_; lean_object* v___x_5570_; 
lean_inc_ref(v___y_5554_);
v___x_5569_ = l_Array_append___redArg(v___y_5554_, v___y_5568_);
lean_dec_ref(v___y_5568_);
lean_inc(v___y_5558_);
lean_inc(v___y_5559_);
v___x_5570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5570_, 0, v___y_5559_);
lean_ctor_set(v___x_5570_, 1, v___y_5558_);
lean_ctor_set(v___x_5570_, 2, v___x_5569_);
if (lean_obj_tag(v___y_5560_) == 0)
{
lean_object* v___x_5571_; lean_object* v___x_5572_; 
v___x_5571_ = lean_box(0);
lean_inc_ref(v___f_5339_);
v___x_5572_ = lean_apply_1(v___f_5339_, v___x_5571_);
v___y_5512_ = v___y_5547_;
v___y_5513_ = v___y_5548_;
v___y_5514_ = v___y_5549_;
v___y_5515_ = v___y_5550_;
v___y_5516_ = v___y_5551_;
v___y_5517_ = v___y_5552_;
v___y_5518_ = v___y_5553_;
v___y_5519_ = v___y_5554_;
v___y_5520_ = v___y_5555_;
v___y_5521_ = v___y_5556_;
v___y_5522_ = v___y_5557_;
v___y_5523_ = v___y_5558_;
v___y_5524_ = v___y_5559_;
v___y_5525_ = v___y_5561_;
v___y_5526_ = v___y_5562_;
v___y_5527_ = v___y_5564_;
v___y_5528_ = v___y_5563_;
v___y_5529_ = v___y_5565_;
v___y_5530_ = v___y_5567_;
v___y_5531_ = v___y_5566_;
v___y_5532_ = v___x_5570_;
v___y_5533_ = v___x_5572_;
goto v___jp_5511_;
}
else
{
lean_object* v_val_5573_; lean_object* v___x_5574_; 
v_val_5573_ = lean_ctor_get(v___y_5560_, 0);
lean_inc(v_val_5573_);
lean_dec_ref_known(v___y_5560_, 1);
lean_inc_ref(v___f_5340_);
v___x_5574_ = lean_apply_1(v___f_5340_, v_val_5573_);
v___y_5512_ = v___y_5547_;
v___y_5513_ = v___y_5548_;
v___y_5514_ = v___y_5549_;
v___y_5515_ = v___y_5550_;
v___y_5516_ = v___y_5551_;
v___y_5517_ = v___y_5552_;
v___y_5518_ = v___y_5553_;
v___y_5519_ = v___y_5554_;
v___y_5520_ = v___y_5555_;
v___y_5521_ = v___y_5556_;
v___y_5522_ = v___y_5557_;
v___y_5523_ = v___y_5558_;
v___y_5524_ = v___y_5559_;
v___y_5525_ = v___y_5561_;
v___y_5526_ = v___y_5562_;
v___y_5527_ = v___y_5564_;
v___y_5528_ = v___y_5563_;
v___y_5529_ = v___y_5565_;
v___y_5530_ = v___y_5567_;
v___y_5531_ = v___y_5566_;
v___y_5532_ = v___x_5570_;
v___y_5533_ = v___x_5574_;
goto v___jp_5511_;
}
}
v___jp_5575_:
{
lean_object* v___x_5598_; lean_object* v___x_5599_; 
lean_inc_ref(v___y_5583_);
v___x_5598_ = l_Array_append___redArg(v___y_5583_, v___y_5597_);
lean_dec_ref(v___y_5597_);
lean_inc(v___y_5587_);
lean_inc(v___y_5588_);
v___x_5599_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5599_, 0, v___y_5588_);
lean_ctor_set(v___x_5599_, 1, v___y_5587_);
lean_ctor_set(v___x_5599_, 2, v___x_5598_);
if (lean_obj_tag(v___y_5576_) == 1)
{
lean_object* v_val_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5603_; 
v_val_5600_ = lean_ctor_get(v___y_5576_, 0);
lean_inc(v_val_5600_);
lean_dec_ref_known(v___y_5576_, 1);
v___x_5601_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__3));
lean_inc(v___y_5588_);
v___x_5602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5602_, 0, v___y_5588_);
lean_ctor_set(v___x_5602_, 1, v___x_5601_);
v___x_5603_ = l_Array_mkArray2___redArg(v___x_5602_, v_val_5600_);
v___y_5547_ = v___y_5577_;
v___y_5548_ = v___y_5578_;
v___y_5549_ = v___y_5579_;
v___y_5550_ = v___x_5599_;
v___y_5551_ = v___y_5580_;
v___y_5552_ = v___y_5581_;
v___y_5553_ = v___y_5582_;
v___y_5554_ = v___y_5583_;
v___y_5555_ = v___y_5584_;
v___y_5556_ = v___y_5585_;
v___y_5557_ = v___y_5586_;
v___y_5558_ = v___y_5587_;
v___y_5559_ = v___y_5588_;
v___y_5560_ = v___y_5590_;
v___y_5561_ = v___y_5589_;
v___y_5562_ = v___y_5591_;
v___y_5563_ = v___y_5593_;
v___y_5564_ = v___y_5592_;
v___y_5565_ = v___y_5594_;
v___y_5566_ = v___y_5596_;
v___y_5567_ = v___y_5595_;
v___y_5568_ = v___x_5603_;
goto v___jp_5546_;
}
else
{
lean_object* v___x_5604_; 
lean_dec(v___y_5576_);
v___x_5604_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___closed__0));
v___y_5547_ = v___y_5577_;
v___y_5548_ = v___y_5578_;
v___y_5549_ = v___y_5579_;
v___y_5550_ = v___x_5599_;
v___y_5551_ = v___y_5580_;
v___y_5552_ = v___y_5581_;
v___y_5553_ = v___y_5582_;
v___y_5554_ = v___y_5583_;
v___y_5555_ = v___y_5584_;
v___y_5556_ = v___y_5585_;
v___y_5557_ = v___y_5586_;
v___y_5558_ = v___y_5587_;
v___y_5559_ = v___y_5588_;
v___y_5560_ = v___y_5590_;
v___y_5561_ = v___y_5589_;
v___y_5562_ = v___y_5591_;
v___y_5563_ = v___y_5593_;
v___y_5564_ = v___y_5592_;
v___y_5565_ = v___y_5594_;
v___y_5566_ = v___y_5596_;
v___y_5567_ = v___y_5595_;
v___y_5568_ = v___x_5604_;
goto v___jp_5546_;
}
}
v___jp_5606_:
{
uint8_t v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5624_ = 0;
v___x_5625_ = l_Lean_SourceInfo_fromRef(v_ref_5622_, v___x_5624_);
v___x_5626_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__0));
lean_inc_ref(v___x_5342_);
lean_inc_ref(v___x_5337_);
lean_inc_ref(v___x_5336_);
lean_inc_ref(v___x_5335_);
v___x_5627_ = l_Lean_Name_mkStr5(v___x_5335_, v___x_5336_, v___x_5337_, v___x_5626_, v___x_5342_);
v___x_5628_ = l_Lean_SourceInfo_fromRef(v_tk_5605_, v___x_5338_);
lean_dec(v_tk_5605_);
v___x_5629_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5629_, 0, v___x_5628_);
lean_ctor_set(v___x_5629_, 1, v___x_5342_);
v___x_5630_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9));
v___x_5631_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24, &l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__24);
if (lean_obj_tag(v___y_5612_) == 1)
{
lean_object* v_val_5632_; lean_object* v___x_5633_; lean_object* v___x_5634_; lean_object* v___x_5635_; lean_object* v___x_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5639_; 
v_val_5632_ = lean_ctor_get(v___y_5612_, 0);
lean_inc(v_val_5632_);
lean_dec_ref_known(v___y_5612_, 1);
v___x_5633_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__25));
lean_inc_n(v___x_5625_, 3);
v___x_5634_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5634_, 0, v___x_5625_);
lean_ctor_set(v___x_5634_, 1, v___x_5633_);
v___x_5635_ = l_Array_append___redArg(v___x_5631_, v_val_5632_);
lean_dec(v_val_5632_);
v___x_5636_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5636_, 0, v___x_5625_);
lean_ctor_set(v___x_5636_, 1, v___x_5630_);
lean_ctor_set(v___x_5636_, 2, v___x_5635_);
v___x_5637_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__27));
v___x_5638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5638_, 0, v___x_5625_);
lean_ctor_set(v___x_5638_, 1, v___x_5637_);
v___x_5639_ = l_Array_mkArray3___redArg(v___x_5634_, v___x_5636_, v___x_5638_);
v___y_5576_ = v___y_5607_;
v___y_5577_ = v___x_5626_;
v___y_5578_ = v___y_5609_;
v___y_5579_ = v___x_5629_;
v___y_5580_ = v___y_5619_;
v___y_5581_ = v___y_5618_;
v___y_5582_ = v___y_5611_;
v___y_5583_ = v___x_5631_;
v___y_5584_ = v___y_5620_;
v___y_5585_ = v___y_5616_;
v___y_5586_ = v___y_5608_;
v___y_5587_ = v___x_5630_;
v___y_5588_ = v___x_5625_;
v___y_5589_ = v___y_5617_;
v___y_5590_ = v___y_5610_;
v___y_5591_ = v___y_5615_;
v___y_5592_ = v___y_5621_;
v___y_5593_ = v___y_5623_;
v___y_5594_ = v___y_5613_;
v___y_5595_ = v_cfg_5614_;
v___y_5596_ = v___x_5627_;
v___y_5597_ = v___x_5639_;
goto v___jp_5575_;
}
else
{
lean_object* v___x_5640_; 
lean_dec(v___y_5612_);
v___x_5640_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__0___closed__0));
v___y_5576_ = v___y_5607_;
v___y_5577_ = v___x_5626_;
v___y_5578_ = v___y_5609_;
v___y_5579_ = v___x_5629_;
v___y_5580_ = v___y_5619_;
v___y_5581_ = v___y_5618_;
v___y_5582_ = v___y_5611_;
v___y_5583_ = v___x_5631_;
v___y_5584_ = v___y_5620_;
v___y_5585_ = v___y_5616_;
v___y_5586_ = v___y_5608_;
v___y_5587_ = v___x_5630_;
v___y_5588_ = v___x_5625_;
v___y_5589_ = v___y_5617_;
v___y_5590_ = v___y_5610_;
v___y_5591_ = v___y_5615_;
v___y_5592_ = v___y_5621_;
v___y_5593_ = v___y_5623_;
v___y_5594_ = v___y_5613_;
v___y_5595_ = v_cfg_5614_;
v___y_5596_ = v___x_5627_;
v___y_5597_ = v___x_5640_;
goto v___jp_5575_;
}
}
v___jp_5641_:
{
lean_object* v___x_5657_; 
v___x_5657_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGenDischarge(v___y_5645_, v___y_5646_, v___y_5649_, v___y_5652_, v___y_5655_, v___y_5650_, v___y_5642_, v___y_5648_, v___y_5647_);
if (lean_obj_tag(v___x_5657_) == 0)
{
lean_object* v_a_5658_; 
v_a_5658_ = lean_ctor_get(v___x_5657_, 0);
lean_inc(v_a_5658_);
lean_dec_ref_known(v___x_5657_, 1);
if (lean_obj_tag(v_a_5658_) == 0)
{
lean_object* v_ref_5659_; lean_object* v_quotContext_5660_; lean_object* v_currMacroScope_5661_; uint8_t v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; 
v_ref_5659_ = lean_ctor_get(v___y_5648_, 5);
v_quotContext_5660_ = lean_ctor_get(v___y_5648_, 10);
v_currMacroScope_5661_ = lean_ctor_get(v___y_5648_, 11);
v___x_5662_ = 0;
v___x_5663_ = l_Lean_SourceInfo_fromRef(v_ref_5659_, v___x_5662_);
v___x_5664_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__9));
v___x_5665_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__10));
lean_inc_ref_n(v___x_5337_, 2);
lean_inc_ref_n(v___x_5336_, 2);
lean_inc_ref_n(v___x_5335_, 2);
v___x_5666_ = l_Lean_Name_mkStr4(v___x_5335_, v___x_5336_, v___x_5337_, v___x_5665_);
v___x_5667_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__18));
v___x_5668_ = l_Lean_Name_mkStr4(v___x_5335_, v___x_5336_, v___x_5337_, v___x_5667_);
v___x_5669_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkContext___closed__20));
lean_inc_n(v___x_5663_, 5);
v___x_5670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5670_, 0, v___x_5663_);
lean_ctor_set(v___x_5670_, 1, v___x_5669_);
v___x_5671_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__5, &l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__5_once, _init_l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__5);
v___x_5672_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__6));
lean_inc(v_currMacroScope_5661_);
lean_inc(v_quotContext_5660_);
v___x_5673_ = l_Lean_addMacroScope(v_quotContext_5660_, v___x_5672_, v_currMacroScope_5661_);
v___x_5674_ = lean_box(0);
v___x_5675_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_5675_, 0, v___x_5663_);
lean_ctor_set(v___x_5675_, 1, v___x_5671_);
lean_ctor_set(v___x_5675_, 2, v___x_5673_);
lean_ctor_set(v___x_5675_, 3, v___x_5674_);
v___x_5676_ = l_Lean_Syntax_node2(v___x_5663_, v___x_5668_, v___x_5670_, v___x_5675_);
v___x_5677_ = l_Lean_Syntax_node1(v___x_5663_, v___x_5666_, v___x_5676_);
v___x_5678_ = l_Lean_Syntax_node1(v___x_5663_, v___x_5664_, v___x_5677_);
v___x_5679_ = l_Lean_Syntax_node1(v___x_5663_, v___x_5472_, v___x_5678_);
v___x_5680_ = l_Lean_Parser_Tactic_appendConfig(v___x_5679_, v_cfg_5470_);
v___y_5607_ = v___y_5643_;
v___y_5608_ = v___y_5651_;
v___y_5609_ = v___y_5644_;
v___y_5610_ = v___y_5656_;
v___y_5611_ = v_a_5658_;
v___y_5612_ = v___y_5653_;
v___y_5613_ = v___y_5654_;
v_cfg_5614_ = v___x_5680_;
v___y_5615_ = v___y_5646_;
v___y_5616_ = v___y_5649_;
v___y_5617_ = v___y_5652_;
v___y_5618_ = v___y_5655_;
v___y_5619_ = v___y_5650_;
v___y_5620_ = v___y_5642_;
v___y_5621_ = v___y_5648_;
v_ref_5622_ = v_ref_5659_;
v___y_5623_ = v___y_5647_;
goto v___jp_5606_;
}
else
{
lean_object* v_ref_5681_; 
lean_dec(v___x_5472_);
v_ref_5681_ = lean_ctor_get(v___y_5648_, 5);
v___y_5607_ = v___y_5643_;
v___y_5608_ = v___y_5651_;
v___y_5609_ = v___y_5644_;
v___y_5610_ = v___y_5656_;
v___y_5611_ = v_a_5658_;
v___y_5612_ = v___y_5653_;
v___y_5613_ = v___y_5654_;
v_cfg_5614_ = v_cfg_5470_;
v___y_5615_ = v___y_5646_;
v___y_5616_ = v___y_5649_;
v___y_5617_ = v___y_5652_;
v___y_5618_ = v___y_5655_;
v___y_5619_ = v___y_5650_;
v___y_5620_ = v___y_5642_;
v___y_5621_ = v___y_5648_;
v_ref_5622_ = v_ref_5681_;
v___y_5623_ = v___y_5647_;
goto v___jp_5606_;
}
}
else
{
lean_object* v_a_5682_; lean_object* v___x_5684_; uint8_t v_isShared_5685_; uint8_t v_isSharedCheck_5689_; 
lean_dec(v___y_5656_);
lean_dec(v___y_5654_);
lean_dec(v___y_5653_);
lean_dec(v___y_5651_);
lean_dec(v___y_5644_);
lean_dec(v___y_5643_);
lean_dec(v_tk_5605_);
lean_dec(v___x_5472_);
lean_dec(v_cfg_5470_);
lean_dec_ref(v___x_5342_);
lean_dec_ref(v___f_5341_);
lean_dec_ref(v___f_5340_);
lean_dec_ref(v___f_5339_);
lean_dec_ref(v___x_5337_);
lean_dec_ref(v___x_5336_);
lean_dec_ref(v___x_5335_);
v_a_5682_ = lean_ctor_get(v___x_5657_, 0);
v_isSharedCheck_5689_ = !lean_is_exclusive(v___x_5657_);
if (v_isSharedCheck_5689_ == 0)
{
v___x_5684_ = v___x_5657_;
v_isShared_5685_ = v_isSharedCheck_5689_;
goto v_resetjp_5683_;
}
else
{
lean_inc(v_a_5682_);
lean_dec(v___x_5657_);
v___x_5684_ = lean_box(0);
v_isShared_5685_ = v_isSharedCheck_5689_;
goto v_resetjp_5683_;
}
v_resetjp_5683_:
{
lean_object* v___x_5687_; 
if (v_isShared_5685_ == 0)
{
v___x_5687_ = v___x_5684_;
goto v_reusejp_5686_;
}
else
{
lean_object* v_reuseFailAlloc_5688_; 
v_reuseFailAlloc_5688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5688_, 0, v_a_5682_);
v___x_5687_ = v_reuseFailAlloc_5688_;
goto v_reusejp_5686_;
}
v_reusejp_5686_:
{
return v___x_5687_;
}
}
}
}
v___jp_5690_:
{
lean_object* v___x_5706_; 
v___x_5706_ = l_Lean_Syntax_getOptional_x3f(v___y_5694_);
lean_dec(v___y_5694_);
if (lean_obj_tag(v___x_5706_) == 0)
{
lean_object* v___x_5707_; 
v___x_5707_ = lean_box(0);
v___y_5642_ = v___y_5703_;
v___y_5643_ = v___y_5691_;
v___y_5644_ = v___y_5693_;
v___y_5645_ = v_w_5697_;
v___y_5646_ = v___y_5698_;
v___y_5647_ = v___y_5705_;
v___y_5648_ = v___y_5704_;
v___y_5649_ = v___y_5699_;
v___y_5650_ = v___y_5702_;
v___y_5651_ = v___y_5692_;
v___y_5652_ = v___y_5700_;
v___y_5653_ = v___y_5695_;
v___y_5654_ = v___y_5696_;
v___y_5655_ = v___y_5701_;
v___y_5656_ = v___x_5707_;
goto v___jp_5641_;
}
else
{
lean_object* v_val_5708_; lean_object* v___x_5710_; uint8_t v_isShared_5711_; uint8_t v_isSharedCheck_5715_; 
v_val_5708_ = lean_ctor_get(v___x_5706_, 0);
v_isSharedCheck_5715_ = !lean_is_exclusive(v___x_5706_);
if (v_isSharedCheck_5715_ == 0)
{
v___x_5710_ = v___x_5706_;
v_isShared_5711_ = v_isSharedCheck_5715_;
goto v_resetjp_5709_;
}
else
{
lean_inc(v_val_5708_);
lean_dec(v___x_5706_);
v___x_5710_ = lean_box(0);
v_isShared_5711_ = v_isSharedCheck_5715_;
goto v_resetjp_5709_;
}
v_resetjp_5709_:
{
lean_object* v___x_5713_; 
if (v_isShared_5711_ == 0)
{
v___x_5713_ = v___x_5710_;
goto v_reusejp_5712_;
}
else
{
lean_object* v_reuseFailAlloc_5714_; 
v_reuseFailAlloc_5714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_val_5708_);
v___x_5713_ = v_reuseFailAlloc_5714_;
goto v_reusejp_5712_;
}
v_reusejp_5712_:
{
v___y_5642_ = v___y_5703_;
v___y_5643_ = v___y_5691_;
v___y_5644_ = v___y_5693_;
v___y_5645_ = v_w_5697_;
v___y_5646_ = v___y_5698_;
v___y_5647_ = v___y_5705_;
v___y_5648_ = v___y_5704_;
v___y_5649_ = v___y_5699_;
v___y_5650_ = v___y_5702_;
v___y_5651_ = v___y_5692_;
v___y_5652_ = v___y_5700_;
v___y_5653_ = v___y_5695_;
v___y_5654_ = v___y_5696_;
v___y_5655_ = v___y_5701_;
v___y_5656_ = v___x_5713_;
goto v___jp_5641_;
}
}
}
}
v___jp_5717_:
{
lean_object* v___x_5732_; lean_object* v___x_5733_; uint8_t v___x_5734_; 
v___x_5732_ = lean_unsigned_to_nat(6u);
v___x_5733_ = l_Lean_Syntax_getArg(v_stx_5334_, v___x_5732_);
v___x_5734_ = l_Lean_Syntax_isNone(v___x_5733_);
if (v___x_5734_ == 0)
{
uint8_t v___x_5735_; 
lean_inc(v___x_5733_);
v___x_5735_ = l_Lean_Syntax_matchesNull(v___x_5733_, v___x_5716_);
if (v___x_5735_ == 0)
{
lean_object* v___x_5736_; 
lean_dec(v___x_5733_);
lean_dec(v_thms_5723_);
lean_dec(v_sa_5722_);
lean_dec(v___y_5721_);
lean_dec(v___y_5720_);
lean_dec(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec(v_tk_5605_);
lean_dec(v___x_5472_);
lean_dec(v_cfg_5470_);
lean_dec_ref(v___x_5342_);
lean_dec_ref(v___f_5341_);
lean_dec_ref(v___f_5340_);
lean_dec_ref(v___f_5339_);
lean_dec_ref(v___x_5337_);
lean_dec_ref(v___x_5336_);
lean_dec_ref(v___x_5335_);
v___x_5736_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg();
return v___x_5736_;
}
else
{
lean_object* v_w_5737_; lean_object* v___x_5738_; 
v_w_5737_ = l_Lean_Syntax_getArg(v___x_5733_, v___x_5469_);
lean_dec(v___x_5733_);
v___x_5738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5738_, 0, v_w_5737_);
v___y_5691_ = v___y_5718_;
v___y_5692_ = v_sa_5722_;
v___y_5693_ = v___y_5719_;
v___y_5694_ = v___y_5720_;
v___y_5695_ = v___y_5721_;
v___y_5696_ = v_thms_5723_;
v_w_5697_ = v___x_5738_;
v___y_5698_ = v___y_5724_;
v___y_5699_ = v___y_5725_;
v___y_5700_ = v___y_5726_;
v___y_5701_ = v___y_5727_;
v___y_5702_ = v___y_5728_;
v___y_5703_ = v___y_5729_;
v___y_5704_ = v___y_5730_;
v___y_5705_ = v___y_5731_;
goto v___jp_5690_;
}
}
else
{
lean_object* v___x_5739_; 
lean_dec(v___x_5733_);
v___x_5739_ = lean_box(0);
v___y_5691_ = v___y_5718_;
v___y_5692_ = v_sa_5722_;
v___y_5693_ = v___y_5719_;
v___y_5694_ = v___y_5720_;
v___y_5695_ = v___y_5721_;
v___y_5696_ = v_thms_5723_;
v_w_5697_ = v___x_5739_;
v___y_5698_ = v___y_5724_;
v___y_5699_ = v___y_5725_;
v___y_5700_ = v___y_5726_;
v___y_5701_ = v___y_5727_;
v___y_5702_ = v___y_5728_;
v___y_5703_ = v___y_5729_;
v___y_5704_ = v___y_5730_;
v___y_5705_ = v___y_5731_;
goto v___jp_5690_;
}
}
v___jp_5740_:
{
lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___x_5755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5755_, 0, v___y_5754_);
v___x_5756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5756_, 0, v___y_5749_);
v___y_5718_ = v___y_5742_;
v___y_5719_ = v___y_5743_;
v___y_5720_ = v___y_5745_;
v___y_5721_ = v___y_5751_;
v_sa_5722_ = v___x_5755_;
v_thms_5723_ = v___x_5756_;
v___y_5724_ = v___y_5741_;
v___y_5725_ = v___y_5748_;
v___y_5726_ = v___y_5746_;
v___y_5727_ = v___y_5752_;
v___y_5728_ = v___y_5747_;
v___y_5729_ = v___y_5744_;
v___y_5730_ = v___y_5750_;
v___y_5731_ = v___y_5753_;
goto v___jp_5717_;
}
v___jp_5757_:
{
lean_object* v___x_5772_; 
v___x_5772_ = l_Lean_Syntax_getOptional_x3f(v___y_5760_);
lean_dec(v___y_5760_);
if (lean_obj_tag(v___x_5772_) == 0)
{
lean_object* v___x_5773_; 
v___x_5773_ = lean_box(0);
v___y_5741_ = v___y_5764_;
v___y_5742_ = v___y_5758_;
v___y_5743_ = v___y_5759_;
v___y_5744_ = v___y_5769_;
v___y_5745_ = v___y_5761_;
v___y_5746_ = v___y_5766_;
v___y_5747_ = v___y_5768_;
v___y_5748_ = v___y_5765_;
v___y_5749_ = v_thms_5763_;
v___y_5750_ = v___y_5770_;
v___y_5751_ = v___y_5762_;
v___y_5752_ = v___y_5767_;
v___y_5753_ = v___y_5771_;
v___y_5754_ = v___x_5773_;
goto v___jp_5740_;
}
else
{
lean_object* v_val_5774_; lean_object* v___x_5776_; uint8_t v_isShared_5777_; uint8_t v_isSharedCheck_5781_; 
v_val_5774_ = lean_ctor_get(v___x_5772_, 0);
v_isSharedCheck_5781_ = !lean_is_exclusive(v___x_5772_);
if (v_isSharedCheck_5781_ == 0)
{
v___x_5776_ = v___x_5772_;
v_isShared_5777_ = v_isSharedCheck_5781_;
goto v_resetjp_5775_;
}
else
{
lean_inc(v_val_5774_);
lean_dec(v___x_5772_);
v___x_5776_ = lean_box(0);
v_isShared_5777_ = v_isSharedCheck_5781_;
goto v_resetjp_5775_;
}
v_resetjp_5775_:
{
lean_object* v___x_5779_; 
if (v_isShared_5777_ == 0)
{
v___x_5779_ = v___x_5776_;
goto v_reusejp_5778_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_val_5774_);
v___x_5779_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5778_;
}
v_reusejp_5778_:
{
v___y_5741_ = v___y_5764_;
v___y_5742_ = v___y_5758_;
v___y_5743_ = v___y_5759_;
v___y_5744_ = v___y_5769_;
v___y_5745_ = v___y_5761_;
v___y_5746_ = v___y_5766_;
v___y_5747_ = v___y_5768_;
v___y_5748_ = v___y_5765_;
v___y_5749_ = v_thms_5763_;
v___y_5750_ = v___y_5770_;
v___y_5751_ = v___y_5762_;
v___y_5752_ = v___y_5767_;
v___y_5753_ = v___y_5771_;
v___y_5754_ = v___x_5779_;
goto v___jp_5740_;
}
}
}
}
v___jp_5782_:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; uint8_t v___x_5798_; 
v___x_5794_ = lean_unsigned_to_nat(4u);
v___x_5795_ = l_Lean_Syntax_getArg(v_stx_5334_, v___x_5794_);
v___x_5796_ = lean_unsigned_to_nat(5u);
v___x_5797_ = l_Lean_Syntax_getArg(v_stx_5334_, v___x_5796_);
v___x_5798_ = l_Lean_Syntax_isNone(v___x_5797_);
if (v___x_5798_ == 0)
{
uint8_t v___x_5799_; 
lean_inc(v___x_5797_);
v___x_5799_ = l_Lean_Syntax_matchesNull(v___x_5797_, v___y_5783_);
if (v___x_5799_ == 0)
{
lean_object* v___x_5800_; 
lean_dec(v___x_5797_);
lean_dec(v___x_5795_);
lean_dec(v_u_5785_);
lean_dec(v___y_5784_);
lean_dec(v_tk_5605_);
lean_dec(v___x_5472_);
lean_dec(v_cfg_5470_);
lean_dec_ref(v___x_5342_);
lean_dec_ref(v___f_5341_);
lean_dec_ref(v___f_5340_);
lean_dec_ref(v___f_5339_);
lean_dec_ref(v___x_5337_);
lean_dec_ref(v___x_5336_);
lean_dec_ref(v___x_5335_);
v___x_5800_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg();
return v___x_5800_;
}
else
{
lean_object* v___x_5801_; lean_object* v___x_5802_; uint8_t v___x_5803_; 
v___x_5801_ = l_Lean_Syntax_getArg(v___x_5797_, v___x_5469_);
v___x_5802_ = l_Lean_Syntax_getArg(v___x_5797_, v___x_5716_);
lean_dec(v___x_5797_);
v___x_5803_ = l_Lean_Syntax_isNone(v___x_5802_);
if (v___x_5803_ == 0)
{
uint8_t v___x_5804_; 
lean_inc(v___x_5802_);
v___x_5804_ = l_Lean_Syntax_matchesNull(v___x_5802_, v___y_5783_);
if (v___x_5804_ == 0)
{
lean_object* v___x_5805_; 
lean_dec(v___x_5802_);
lean_dec(v___x_5801_);
lean_dec(v___x_5795_);
lean_dec(v_u_5785_);
lean_dec(v___y_5784_);
lean_dec(v_tk_5605_);
lean_dec(v___x_5472_);
lean_dec(v_cfg_5470_);
lean_dec_ref(v___x_5342_);
lean_dec_ref(v___f_5341_);
lean_dec_ref(v___f_5340_);
lean_dec_ref(v___f_5339_);
lean_dec_ref(v___x_5337_);
lean_dec_ref(v___x_5336_);
lean_dec_ref(v___x_5335_);
v___x_5805_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg();
return v___x_5805_;
}
else
{
lean_object* v___x_5806_; lean_object* v_thms_5807_; lean_object* v___x_5808_; 
v___x_5806_ = l_Lean_Syntax_getArg(v___x_5802_, v___x_5469_);
lean_dec(v___x_5802_);
v_thms_5807_ = l_Lean_Syntax_getArgs(v___x_5806_);
lean_dec(v___x_5806_);
v___x_5808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5808_, 0, v_thms_5807_);
v___y_5758_ = v_u_5785_;
v___y_5759_ = v___x_5796_;
v___y_5760_ = v___x_5801_;
v___y_5761_ = v___x_5795_;
v___y_5762_ = v___y_5784_;
v_thms_5763_ = v___x_5808_;
v___y_5764_ = v___y_5786_;
v___y_5765_ = v___y_5787_;
v___y_5766_ = v___y_5788_;
v___y_5767_ = v___y_5789_;
v___y_5768_ = v___y_5790_;
v___y_5769_ = v___y_5791_;
v___y_5770_ = v___y_5792_;
v___y_5771_ = v___y_5793_;
goto v___jp_5757_;
}
}
else
{
lean_object* v___x_5809_; 
lean_dec(v___x_5802_);
v___x_5809_ = lean_box(0);
v___y_5758_ = v_u_5785_;
v___y_5759_ = v___x_5796_;
v___y_5760_ = v___x_5801_;
v___y_5761_ = v___x_5795_;
v___y_5762_ = v___y_5784_;
v_thms_5763_ = v___x_5809_;
v___y_5764_ = v___y_5786_;
v___y_5765_ = v___y_5787_;
v___y_5766_ = v___y_5788_;
v___y_5767_ = v___y_5789_;
v___y_5768_ = v___y_5790_;
v___y_5769_ = v___y_5791_;
v___y_5770_ = v___y_5792_;
v___y_5771_ = v___y_5793_;
goto v___jp_5757_;
}
}
}
else
{
lean_object* v___x_5810_; 
lean_dec(v___x_5797_);
v___x_5810_ = lean_box(0);
v___y_5718_ = v_u_5785_;
v___y_5719_ = v___x_5796_;
v___y_5720_ = v___x_5795_;
v___y_5721_ = v___y_5784_;
v_sa_5722_ = v___x_5810_;
v_thms_5723_ = v___x_5810_;
v___y_5724_ = v___y_5786_;
v___y_5725_ = v___y_5787_;
v___y_5726_ = v___y_5788_;
v___y_5727_ = v___y_5789_;
v___y_5728_ = v___y_5790_;
v___y_5729_ = v___y_5791_;
v___y_5730_ = v___y_5792_;
v___y_5731_ = v___y_5793_;
goto v___jp_5717_;
}
}
v___jp_5811_:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; uint8_t v___x_5823_; 
v___x_5821_ = lean_unsigned_to_nat(3u);
v___x_5822_ = l_Lean_Syntax_getArg(v_stx_5334_, v___x_5821_);
v___x_5823_ = l_Lean_Syntax_isNone(v___x_5822_);
if (v___x_5823_ == 0)
{
uint8_t v___x_5824_; 
lean_inc(v___x_5822_);
v___x_5824_ = l_Lean_Syntax_matchesNull(v___x_5822_, v___x_5716_);
if (v___x_5824_ == 0)
{
lean_object* v___x_5825_; 
lean_dec(v___x_5822_);
lean_dec(v_lems_5812_);
lean_dec(v_tk_5605_);
lean_dec(v___x_5472_);
lean_dec(v_cfg_5470_);
lean_dec_ref(v___x_5342_);
lean_dec_ref(v___f_5341_);
lean_dec_ref(v___f_5340_);
lean_dec_ref(v___f_5339_);
lean_dec_ref(v___x_5337_);
lean_dec_ref(v___x_5336_);
lean_dec_ref(v___x_5335_);
v___x_5825_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__0___redArg();
return v___x_5825_;
}
else
{
lean_object* v_u_5826_; lean_object* v___x_5827_; 
v_u_5826_ = l_Lean_Syntax_getArg(v___x_5822_, v___x_5469_);
lean_dec(v___x_5822_);
v___x_5827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5827_, 0, v_u_5826_);
v___y_5783_ = v___x_5821_;
v___y_5784_ = v_lems_5812_;
v_u_5785_ = v___x_5827_;
v___y_5786_ = v___y_5813_;
v___y_5787_ = v___y_5814_;
v___y_5788_ = v___y_5815_;
v___y_5789_ = v___y_5816_;
v___y_5790_ = v___y_5817_;
v___y_5791_ = v___y_5818_;
v___y_5792_ = v___y_5819_;
v___y_5793_ = v___y_5820_;
goto v___jp_5782_;
}
}
else
{
lean_object* v___x_5828_; 
lean_dec(v___x_5822_);
v___x_5828_ = lean_box(0);
v___y_5783_ = v___x_5821_;
v___y_5784_ = v_lems_5812_;
v_u_5785_ = v___x_5828_;
v___y_5786_ = v___y_5813_;
v___y_5787_ = v___y_5814_;
v___y_5788_ = v___y_5815_;
v___y_5789_ = v___y_5816_;
v___y_5790_ = v___y_5817_;
v___y_5791_ = v___y_5818_;
v___y_5792_ = v___y_5819_;
v___y_5793_ = v___y_5820_;
goto v___jp_5782_;
}
}
}
}
v___jp_5352_:
{
lean_object* v___x_5363_; 
v___x_5363_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5356_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
if (lean_obj_tag(v___x_5363_) == 0)
{
lean_object* v_a_5364_; uint8_t v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5376_; 
v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
lean_inc(v_a_5364_);
lean_dec_ref_known(v___x_5363_, 1);
v___x_5365_ = 0;
v___x_5366_ = lean_unsigned_to_nat(9u);
v___x_5367_ = lean_unsigned_to_nat(8u);
v___x_5368_ = lean_unsigned_to_nat(1000u);
v___x_5369_ = lean_unsigned_to_nat(100000u);
v___x_5370_ = lean_unsigned_to_nat(1024u);
v___x_5371_ = lean_unsigned_to_nat(1048576u);
v___x_5372_ = lean_unsigned_to_nat(10u);
v___x_5373_ = lean_unsigned_to_nat(50u);
v___x_5374_ = lean_box(0);
v___x_5375_ = lean_alloc_ctor(0, 13, 32);
lean_ctor_set(v___x_5375_, 0, v___x_5366_);
lean_ctor_set(v___x_5375_, 1, v___y_5353_);
lean_ctor_set(v___x_5375_, 2, v___x_5367_);
lean_ctor_set(v___x_5375_, 3, v___x_5367_);
lean_ctor_set(v___x_5375_, 4, v___x_5368_);
lean_ctor_set(v___x_5375_, 5, v___x_5368_);
lean_ctor_set(v___x_5375_, 6, v___x_5369_);
lean_ctor_set(v___x_5375_, 7, v___x_5370_);
lean_ctor_set(v___x_5375_, 8, v___x_5368_);
lean_ctor_set(v___x_5375_, 9, v___x_5371_);
lean_ctor_set(v___x_5375_, 10, v___x_5372_);
lean_ctor_set(v___x_5375_, 11, v___x_5373_);
lean_ctor_set(v___x_5375_, 12, v___x_5374_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 1, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 2, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 3, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 4, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 5, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 6, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 7, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 8, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 9, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 10, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 11, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 12, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 13, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 14, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 15, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 16, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 17, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 18, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 19, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 20, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 21, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 22, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 23, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 24, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 25, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 26, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 27, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 28, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 29, v___x_5365_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 30, v___x_5338_);
lean_ctor_set_uint8(v___x_5375_, sizeof(void*)*13 + 31, v___x_5338_);
v___x_5376_ = l_Lean_Meta_Grind_mkDefaultParams(v___x_5375_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
if (lean_obj_tag(v___x_5376_) == 0)
{
lean_object* v_a_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; 
v_a_5377_ = lean_ctor_get(v___x_5376_, 0);
lean_inc(v_a_5377_);
lean_dec_ref_known(v___x_5376_, 1);
v___x_5378_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Grind_evalGrindTactic___boxed), 10, 1);
lean_closure_set(v___x_5378_, 0, v_step_5354_);
v___x_5379_ = l_Lean_Elab_Tactic_Grind_GrindTacticM_runAtGoal___redArg(v_a_5364_, v_a_5377_, v___x_5378_, v___x_5338_, v___y_5355_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
if (lean_obj_tag(v___x_5379_) == 0)
{
lean_object* v_a_5380_; lean_object* v_snd_5381_; lean_object* v_goals_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; 
v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
lean_inc(v_a_5380_);
lean_dec_ref_known(v___x_5379_, 1);
v_snd_5381_ = lean_ctor_get(v_a_5380_, 1);
lean_inc(v_snd_5381_);
lean_dec(v_a_5380_);
v_goals_5382_ = lean_ctor_get(v_snd_5381_, 2);
lean_inc(v_goals_5382_);
lean_dec(v_snd_5381_);
v___x_5383_ = lean_box(0);
v___x_5384_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Do_Internal_elabVCGen_spec__1(v_goals_5382_, v___x_5383_);
v___x_5385_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5384_, v___y_5356_, v___y_5359_, v___y_5360_, v___y_5361_, v___y_5362_);
return v___x_5385_;
}
else
{
lean_object* v_a_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5393_; 
v_a_5386_ = lean_ctor_get(v___x_5379_, 0);
v_isSharedCheck_5393_ = !lean_is_exclusive(v___x_5379_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5388_ = v___x_5379_;
v_isShared_5389_ = v_isSharedCheck_5393_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_a_5386_);
lean_dec(v___x_5379_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5393_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v___x_5391_; 
if (v_isShared_5389_ == 0)
{
v___x_5391_ = v___x_5388_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_a_5386_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
}
else
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5401_; 
lean_dec(v_a_5364_);
lean_dec(v_step_5354_);
v_a_5394_ = lean_ctor_get(v___x_5376_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5376_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___x_5376_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5376_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5399_; 
if (v_isShared_5397_ == 0)
{
v___x_5399_ = v___x_5396_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_a_5394_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5409_; 
lean_dec(v_step_5354_);
lean_dec(v___y_5353_);
v_a_5402_ = lean_ctor_get(v___x_5363_, 0);
v_isSharedCheck_5409_ = !lean_is_exclusive(v___x_5363_);
if (v_isSharedCheck_5409_ == 0)
{
v___x_5404_ = v___x_5363_;
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_a_5402_);
lean_dec(v___x_5363_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5409_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5407_; 
if (v_isShared_5405_ == 0)
{
v___x_5407_ = v___x_5404_;
goto v_reusejp_5406_;
}
else
{
lean_object* v_reuseFailAlloc_5408_; 
v_reuseFailAlloc_5408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5402_);
v___x_5407_ = v_reuseFailAlloc_5408_;
goto v_reusejp_5406_;
}
v_reusejp_5406_:
{
return v___x_5407_;
}
}
}
}
v___jp_5410_:
{
lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___x_5434_; 
v___x_5432_ = l_Array_append___redArg(v___y_5420_, v___y_5431_);
lean_dec_ref(v___y_5431_);
lean_inc(v___y_5422_);
lean_inc_n(v___y_5423_, 2);
v___x_5433_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5433_, 0, v___y_5423_);
lean_ctor_set(v___x_5433_, 1, v___y_5422_);
lean_ctor_set(v___x_5433_, 2, v___x_5432_);
v___x_5434_ = l_Lean_Syntax_node6(v___y_5423_, v___y_5428_, v___y_5413_, v___y_5429_, v___y_5414_, v___y_5430_, v___y_5418_, v___x_5433_);
if (lean_obj_tag(v___y_5417_) == 0)
{
lean_dec(v___y_5423_);
lean_dec_ref(v___y_5411_);
lean_dec_ref(v___x_5337_);
lean_dec_ref(v___x_5336_);
lean_dec_ref(v___x_5335_);
v___y_5353_ = v___y_5412_;
v_step_5354_ = v___x_5434_;
v___y_5355_ = v___y_5425_;
v___y_5356_ = v___y_5421_;
v___y_5357_ = v___y_5424_;
v___y_5358_ = v___y_5416_;
v___y_5359_ = v___y_5415_;
v___y_5360_ = v___y_5419_;
v___y_5361_ = v___y_5427_;
v___y_5362_ = v___y_5426_;
goto v___jp_5352_;
}
else
{
lean_object* v_val_5435_; lean_object* v___x_5436_; lean_object* v___x_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; 
v_val_5435_ = lean_ctor_get(v___y_5417_, 0);
lean_inc(v_val_5435_);
lean_dec_ref_known(v___y_5417_, 1);
v___x_5436_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__0));
v___x_5437_ = l_Lean_Name_mkStr5(v___x_5335_, v___x_5336_, v___x_5337_, v___y_5411_, v___x_5436_);
v___x_5438_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___closed__1));
lean_inc(v___y_5423_);
v___x_5439_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_5439_, 0, v___y_5423_);
lean_ctor_set(v___x_5439_, 1, v___x_5438_);
v___x_5440_ = l_Lean_Syntax_node3(v___y_5423_, v___x_5437_, v___x_5434_, v___x_5439_, v_val_5435_);
v___y_5353_ = v___y_5412_;
v_step_5354_ = v___x_5440_;
v___y_5355_ = v___y_5425_;
v___y_5356_ = v___y_5421_;
v___y_5357_ = v___y_5424_;
v___y_5358_ = v___y_5416_;
v___y_5359_ = v___y_5415_;
v___y_5360_ = v___y_5419_;
v___y_5361_ = v___y_5427_;
v___y_5362_ = v___y_5426_;
goto v___jp_5352_;
}
}
v___jp_5441_:
{
lean_object* v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5467_; 
lean_inc_ref(v___y_5453_);
v___x_5465_ = l_Array_append___redArg(v___y_5453_, v___y_5464_);
lean_dec_ref(v___y_5464_);
lean_inc(v___y_5455_);
lean_inc(v___y_5456_);
v___x_5466_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5466_, 0, v___y_5456_);
lean_ctor_set(v___x_5466_, 1, v___y_5455_);
lean_ctor_set(v___x_5466_, 2, v___x_5465_);
v___x_5467_ = l_Array_mkArray3___redArg(v___y_5445_, v___y_5450_, v___x_5466_);
v___y_5411_ = v___y_5442_;
v___y_5412_ = v___y_5443_;
v___y_5413_ = v___y_5444_;
v___y_5414_ = v___y_5446_;
v___y_5415_ = v___y_5447_;
v___y_5416_ = v___y_5448_;
v___y_5417_ = v___y_5449_;
v___y_5418_ = v___y_5451_;
v___y_5419_ = v___y_5452_;
v___y_5420_ = v___y_5453_;
v___y_5421_ = v___y_5454_;
v___y_5422_ = v___y_5455_;
v___y_5423_ = v___y_5456_;
v___y_5424_ = v___y_5457_;
v___y_5425_ = v___y_5458_;
v___y_5426_ = v___y_5460_;
v___y_5427_ = v___y_5459_;
v___y_5428_ = v___y_5462_;
v___y_5429_ = v___y_5461_;
v___y_5430_ = v___y_5463_;
v___y_5431_ = v___x_5467_;
goto v___jp_5410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___boxed(lean_object** _args){
lean_object* v___x_5838_ = _args[0];
lean_object* v_stx_5839_ = _args[1];
lean_object* v___x_5840_ = _args[2];
lean_object* v___x_5841_ = _args[3];
lean_object* v___x_5842_ = _args[4];
lean_object* v___x_5843_ = _args[5];
lean_object* v___f_5844_ = _args[6];
lean_object* v___f_5845_ = _args[7];
lean_object* v___f_5846_ = _args[8];
lean_object* v___x_5847_ = _args[9];
lean_object* v___y_5848_ = _args[10];
lean_object* v___y_5849_ = _args[11];
lean_object* v___y_5850_ = _args[12];
lean_object* v___y_5851_ = _args[13];
lean_object* v___y_5852_ = _args[14];
lean_object* v___y_5853_ = _args[15];
lean_object* v___y_5854_ = _args[16];
lean_object* v___y_5855_ = _args[17];
lean_object* v___y_5856_ = _args[18];
_start:
{
uint8_t v___x_11685__boxed_5857_; uint8_t v___x_11689__boxed_5858_; lean_object* v_res_5859_; 
v___x_11685__boxed_5857_ = lean_unbox(v___x_5838_);
v___x_11689__boxed_5858_ = lean_unbox(v___x_5843_);
v_res_5859_ = l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3(v___x_11685__boxed_5857_, v_stx_5839_, v___x_5840_, v___x_5841_, v___x_5842_, v___x_11689__boxed_5858_, v___f_5844_, v___f_5845_, v___f_5846_, v___x_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_);
lean_dec(v___y_5855_);
lean_dec_ref(v___y_5854_);
lean_dec(v___y_5853_);
lean_dec_ref(v___y_5852_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
lean_dec(v_stx_5839_);
return v_res_5859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen(lean_object* v_stx_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_, lean_object* v_a_5873_, lean_object* v_a_5874_, lean_object* v_a_5875_, lean_object* v_a_5876_){
_start:
{
lean_object* v___f_5878_; lean_object* v___f_5879_; lean_object* v___f_5880_; lean_object* v___x_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; uint8_t v___x_5886_; uint8_t v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___y_5890_; lean_object* v___x_5891_; 
v___f_5878_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__0));
v___f_5879_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__1));
v___f_5880_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__2));
v___x_5881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__0));
v___x_5882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__1));
v___x_5883_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Tactic_Do_Internal_VCGen_mkContext_spec__4___closed__2));
v___x_5884_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1___closed__1));
v___x_5885_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3));
lean_inc(v_stx_5868_);
v___x_5886_ = l_Lean_Syntax_isOfKind(v_stx_5868_, v___x_5885_);
v___x_5887_ = 1;
v___x_5888_ = lean_box(v___x_5886_);
v___x_5889_ = lean_box(v___x_5887_);
v___y_5890_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___lam__3___boxed), 19, 10);
lean_closure_set(v___y_5890_, 0, v___x_5888_);
lean_closure_set(v___y_5890_, 1, v_stx_5868_);
lean_closure_set(v___y_5890_, 2, v___x_5881_);
lean_closure_set(v___y_5890_, 3, v___x_5882_);
lean_closure_set(v___y_5890_, 4, v___x_5883_);
lean_closure_set(v___y_5890_, 5, v___x_5889_);
lean_closure_set(v___y_5890_, 6, v___f_5879_);
lean_closure_set(v___y_5890_, 7, v___f_5880_);
lean_closure_set(v___y_5890_, 8, v___f_5878_);
lean_closure_set(v___y_5890_, 9, v___x_5884_);
v___x_5891_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_5890_, v_a_5869_, v_a_5870_, v_a_5871_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_, v_a_5876_);
return v___x_5891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_elabVCGen___boxed(lean_object* v_stx_5892_, lean_object* v_a_5893_, lean_object* v_a_5894_, lean_object* v_a_5895_, lean_object* v_a_5896_, lean_object* v_a_5897_, lean_object* v_a_5898_, lean_object* v_a_5899_, lean_object* v_a_5900_, lean_object* v_a_5901_){
_start:
{
lean_object* v_res_5902_; 
v_res_5902_ = l_Lean_Elab_Tactic_Do_Internal_elabVCGen(v_stx_5892_, v_a_5893_, v_a_5894_, v_a_5895_, v_a_5896_, v_a_5897_, v_a_5898_, v_a_5899_, v_a_5900_);
lean_dec(v_a_5900_);
lean_dec_ref(v_a_5899_);
lean_dec(v_a_5898_);
lean_dec_ref(v_a_5897_);
lean_dec(v_a_5896_);
lean_dec_ref(v_a_5895_);
lean_dec(v_a_5894_);
lean_dec_ref(v_a_5893_);
return v_res_5902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1(){
_start:
{
lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; 
v___x_5912_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_5913_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___closed__3));
v___x_5914_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1));
v___x_5915_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_elabVCGen___boxed), 10, 0);
v___x_5916_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5912_, v___x_5913_, v___x_5914_, v___x_5915_);
return v___x_5916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___boxed(lean_object* v_a_5917_){
_start:
{
lean_object* v_res_5918_; 
v_res_5918_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1();
return v_res_5918_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen_docString__3(){
_start:
{
lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; 
v___x_5921_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1___closed__1));
v___x_5922_ = ((lean_object*)(l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen_docString__3___closed__0));
v___x_5923_ = l_Lean_addBuiltinDocString(v___x_5921_, v___x_5922_);
return v___x_5923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen_docString__3___boxed(lean_object* v_a_5924_){
_start:
{
lean_object* v_res_5925_; 
v_res_5925_ = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen_docString__3();
return v_res_5925_;
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
lean_object* runtime_initialize_Lean_Meta_Sym_ProofInstInfo(uint8_t builtin);
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
res = runtime_initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen___regBuiltin___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_evalSymVCGen_docString__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_Do_Internal_VCGen_Frontend_0__Lean_Elab_Tactic_Do_Internal_elabVCGen___regBuiltin_Lean_Elab_Tactic_Do_Internal_elabVCGen_docString__3();
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
lean_object* initialize_Lean_Meta_Sym_ProofInstInfo(uint8_t builtin);
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
res = initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
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
