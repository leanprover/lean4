// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Main
// Imports: public import Lean.Elab.PreDefinition.WF.PackMutual public import Lean.Elab.PreDefinition.WF.FloatRecApp public import Lean.Elab.PreDefinition.WF.Rel public import Lean.Elab.PreDefinition.WF.Fix public import Lean.Elab.PreDefinition.WF.Unfold public import Lean.Elab.PreDefinition.WF.Preprocess public import Lean.Elab.PreDefinition.WF.GuessLex
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Elab_WF_floatRecApp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_guessLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getFixedParamPerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_copyExtraModUses(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "well-founded recursion cannot be used, `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not take any (non-fixed) arguments"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_wfRecursion___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Elab_wfRecursion___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_wfRecursion___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_wfRecursion___lam__2___closed__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "marking functions defined by well-founded recursion as `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` is not effective"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 67, 225, 118, 155, 2, 197, 97)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "semireducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__4_value),LEAN_SCALAR_PTR_LITERAL(106, 254, 211, 230, 8, 182, 79, 36)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wfRel: "};
static const lean_object* l_Lean_Elab_wfRecursion___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "wfRecursion: expected unary function type: "};
static const lean_object* l_Lean_Elab_wfRecursion___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___lam__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__0_value;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__1_value;
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_wfRecursion___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_wfRecursion___closed__0_value),LEAN_SCALAR_PTR_LITERAL(127, 238, 145, 63, 173, 125, 183, 95)}};
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_wfRecursion___closed__2_value_aux_1),((lean_object*)&l_Lean_Elab_wfRecursion___closed__1_value),LEAN_SCALAR_PTR_LITERAL(235, 76, 232, 241, 91, 21, 77, 227)}};
static const lean_object* l_Lean_Elab_wfRecursion___closed__2 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__2_value;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ">> "};
static const lean_object* l_Lean_Elab_wfRecursion___closed__3 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__3_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__4;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " :=\n"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__5 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__5_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__6;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unaryPreDefProcessed:"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__7 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__7_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__8;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unaryPreDef:"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__9 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__9_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___closed__10;
static const lean_ctor_object l_Lean_Elab_wfRecursion___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Elab_wfRecursion___boxed__const__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "PreDefinition"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 172, 242, 185, 134, 214, 81, 182)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WF"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 60, 146, 67, 170, 35, 9, 50)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Main"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(142, 191, 24, 173, 99, 110, 250, 159)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(183, 176, 152, 199, 88, 244, 126, 231)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(74, 192, 220, 42, 201, 36, 231, 139)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 8, 70, 241, 95, 177, 39, 230)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(165, 164, 65, 123, 204, 166, 116, 237)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(24, 212, 71, 249, 113, 26, 236, 1)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 192, 221, 228, 155, 175, 93, 246)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 119, 48, 4, 113, 111, 251, 171)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 104, 40, 162, 247, 89, 56, 248)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(128, 159, 143, 175, 93, 190, 135, 30)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(5, 178, 65, 214, 219, 44, 29, 26)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1197449596) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(114, 70, 68, 25, 255, 132, 81, 38)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 173, 23, 241, 152, 14, 79, 23)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(93, 207, 166, 163, 30, 74, 122, 49)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 76, 225, 120, 116, 96, 87, 123)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0(lean_object* v_k_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v_b_4_, lean_object* v_c_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
lean_inc(v___y_9_);
lean_inc_ref(v___y_8_);
lean_inc(v___y_7_);
lean_inc_ref(v___y_6_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_11_ = lean_apply_9(v_k_1_, v_b_4_, v_c_5_, v___y_2_, v___y_3_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0___boxed(lean_object* v_k_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v_b_15_, lean_object* v_c_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0(v_k_12_, v___y_13_, v___y_14_, v_b_15_, v_c_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_20_);
lean_dec_ref(v___y_19_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg(lean_object* v_type_23_, lean_object* v_maxFVars_x3f_24_, lean_object* v_k_25_, uint8_t v_cleanupAnnotations_26_, uint8_t v_whnfType_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v___f_35_; lean_object* v___x_36_; 
lean_inc(v___y_29_);
lean_inc_ref(v___y_28_);
v___f_35_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_35_, 0, v_k_25_);
lean_closure_set(v___f_35_, 1, v___y_28_);
lean_closure_set(v___f_35_, 2, v___y_29_);
v___x_36_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_23_, v_maxFVars_x3f_24_, v___f_35_, v_cleanupAnnotations_26_, v_whnfType_27_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
if (lean_obj_tag(v___x_36_) == 0)
{
return v___x_36_;
}
else
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_36_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_36_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_type_45_, lean_object* v_maxFVars_x3f_46_, lean_object* v_k_47_, lean_object* v_cleanupAnnotations_48_, lean_object* v_whnfType_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_57_; uint8_t v_whnfType_boxed_58_; lean_object* v_res_59_; 
v_cleanupAnnotations_boxed_57_ = lean_unbox(v_cleanupAnnotations_48_);
v_whnfType_boxed_58_ = lean_unbox(v_whnfType_49_);
v_res_59_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_type_45_, v_maxFVars_x3f_46_, v_k_47_, v_cleanupAnnotations_boxed_57_, v_whnfType_boxed_58_, v___y_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16(lean_object* v_00_u03b1_60_, lean_object* v_type_61_, lean_object* v_maxFVars_x3f_62_, lean_object* v_k_63_, uint8_t v_cleanupAnnotations_64_, uint8_t v_whnfType_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_type_61_, v_maxFVars_x3f_62_, v_k_63_, v_cleanupAnnotations_64_, v_whnfType_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_00_u03b1_74_, lean_object* v_type_75_, lean_object* v_maxFVars_x3f_76_, lean_object* v_k_77_, lean_object* v_cleanupAnnotations_78_, lean_object* v_whnfType_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_87_; uint8_t v_whnfType_boxed_88_; lean_object* v_res_89_; 
v_cleanupAnnotations_boxed_87_ = lean_unbox(v_cleanupAnnotations_78_);
v_whnfType_boxed_88_ = lean_unbox(v_whnfType_79_);
v_res_89_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16(v_00_u03b1_74_, v_type_75_, v_maxFVars_x3f_76_, v_k_77_, v_cleanupAnnotations_boxed_87_, v_whnfType_boxed_88_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_);
lean_dec(v___y_85_);
lean_dec_ref(v___y_84_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
lean_dec(v___y_81_);
lean_dec_ref(v___y_80_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object* v_as_90_, size_t v_sz_91_, size_t v_i_92_, lean_object* v_b_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
uint8_t v___x_97_; 
v___x_97_ = lean_usize_dec_lt(v_i_92_, v_sz_91_);
if (v___x_97_ == 0)
{
lean_object* v___x_98_; 
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v_b_93_);
return v___x_98_;
}
else
{
lean_object* v___x_99_; lean_object* v_a_100_; lean_object* v___x_101_; 
v___x_99_ = lean_box(0);
v_a_100_ = lean_array_uget_borrowed(v_as_90_, v_i_92_);
lean_inc(v_a_100_);
v___x_101_ = l_Lean_Elab_addAsAxiom___redArg(v_a_100_, v___y_94_, v___y_95_);
if (lean_obj_tag(v___x_101_) == 0)
{
size_t v___x_102_; size_t v___x_103_; 
lean_dec_ref_known(v___x_101_, 1);
v___x_102_ = ((size_t)1ULL);
v___x_103_ = lean_usize_add(v_i_92_, v___x_102_);
v_i_92_ = v___x_103_;
v_b_93_ = v___x_99_;
goto _start;
}
else
{
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object* v_as_105_, lean_object* v_sz_106_, lean_object* v_i_107_, lean_object* v_b_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
size_t v_sz_boxed_112_; size_t v_i_boxed_113_; lean_object* v_res_114_; 
v_sz_boxed_112_ = lean_unbox_usize(v_sz_106_);
lean_dec(v_sz_106_);
v_i_boxed_113_ = lean_unbox_usize(v_i_107_);
lean_dec(v_i_107_);
v_res_114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_as_105_, v_sz_boxed_112_, v_i_boxed_113_, v_b_108_, v___y_109_, v___y_110_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
lean_dec_ref(v_as_105_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(lean_object* v_a_115_, size_t v_sz_116_, size_t v_i_117_, lean_object* v_bs_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
uint8_t v___x_124_; 
v___x_124_ = lean_usize_dec_lt(v_i_117_, v_sz_116_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
lean_dec_ref(v_a_115_);
v___x_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_125_, 0, v_bs_118_);
return v___x_125_;
}
else
{
lean_object* v_v_126_; lean_object* v___x_127_; lean_object* v_bs_x27_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_v_126_ = lean_array_uget(v_bs_118_, v_i_117_);
v___x_127_ = lean_unsigned_to_nat(0u);
v_bs_x27_128_ = lean_array_uset(v_bs_118_, v_i_117_, v___x_127_);
v___x_129_ = lean_usize_to_nat(v_i_117_);
lean_inc_ref(v_a_115_);
v___x_130_ = l_Lean_Elab_WF_varyingVarNames(v_a_115_, v___x_129_, v_v_126_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; size_t v___x_132_; size_t v___x_133_; lean_object* v___x_134_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 1);
v___x_132_ = ((size_t)1ULL);
v___x_133_ = lean_usize_add(v_i_117_, v___x_132_);
v___x_134_ = lean_array_uset(v_bs_x27_128_, v_i_117_, v_a_131_);
v_i_117_ = v___x_133_;
v_bs_118_ = v___x_134_;
goto _start;
}
else
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_143_; 
lean_dec_ref(v_bs_x27_128_);
lean_dec_ref(v_a_115_);
v_a_136_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_143_ == 0)
{
v___x_138_ = v___x_130_;
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v___x_130_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_143_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_141_; 
if (v_isShared_139_ == 0)
{
v___x_141_ = v___x_138_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_a_136_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg___boxed(lean_object* v_a_144_, lean_object* v_sz_145_, lean_object* v_i_146_, lean_object* v_bs_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
size_t v_sz_boxed_153_; size_t v_i_boxed_154_; lean_object* v_res_155_; 
v_sz_boxed_153_ = lean_unbox_usize(v_sz_145_);
lean_dec(v_sz_145_);
v_i_boxed_154_ = lean_unbox_usize(v_i_146_);
lean_dec(v_i_146_);
v_res_155_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_144_, v_sz_boxed_153_, v_i_boxed_154_, v_bs_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_155_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_box(1);
v___x_157_ = l_Lean_MessageData_ofFormat(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__3(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__2));
v___x_162_ = l_Lean_MessageData_ofFormat(v___x_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
return v_x_163_;
}
else
{
lean_object* v_head_165_; lean_object* v_tail_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_188_; 
v_head_165_ = lean_ctor_get(v_x_164_, 0);
v_tail_166_ = lean_ctor_get(v_x_164_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_x_164_);
if (v_isSharedCheck_188_ == 0)
{
v___x_168_ = v_x_164_;
v_isShared_169_ = v_isSharedCheck_188_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_tail_166_);
lean_inc(v_head_165_);
lean_dec(v_x_164_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_188_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_before_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_186_; 
v_before_170_ = lean_ctor_get(v_head_165_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v_head_165_);
if (v_isSharedCheck_186_ == 0)
{
lean_object* v_unused_187_; 
v_unused_187_ = lean_ctor_get(v_head_165_, 1);
lean_dec(v_unused_187_);
v___x_172_ = v_head_165_;
v_isShared_173_ = v_isSharedCheck_186_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_before_170_);
lean_dec(v_head_165_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_186_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_173_ == 0)
{
lean_ctor_set_tag(v___x_172_, 7);
lean_ctor_set(v___x_172_, 1, v___x_174_);
lean_ctor_set(v___x_172_, 0, v_x_163_);
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_x_163_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v___x_174_);
v___x_176_ = v_reuseFailAlloc_185_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__3);
if (v_isShared_169_ == 0)
{
lean_ctor_set_tag(v___x_168_, 7);
lean_ctor_set(v___x_168_, 1, v___x_177_);
lean_ctor_set(v___x_168_, 0, v___x_176_);
v___x_179_ = v___x_168_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_176_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_177_);
v___x_179_ = v_reuseFailAlloc_184_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_180_ = l_Lean_MessageData_ofSyntax(v_before_170_);
v___x_181_ = l_Lean_indentD(v___x_180_);
v___x_182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_179_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v_x_163_ = v___x_182_;
v_x_164_ = v_tail_166_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__3(lean_object* v_opts_189_, lean_object* v_opt_190_){
_start:
{
lean_object* v_name_191_; lean_object* v_defValue_192_; lean_object* v_map_193_; lean_object* v___x_194_; 
v_name_191_ = lean_ctor_get(v_opt_190_, 0);
v_defValue_192_ = lean_ctor_get(v_opt_190_, 1);
v_map_193_ = lean_ctor_get(v_opts_189_, 0);
v___x_194_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_193_, v_name_191_);
if (lean_obj_tag(v___x_194_) == 0)
{
uint8_t v___x_195_; 
v___x_195_ = lean_unbox(v_defValue_192_);
return v___x_195_;
}
else
{
lean_object* v_val_196_; 
v_val_196_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_val_196_);
lean_dec_ref_known(v___x_194_, 1);
if (lean_obj_tag(v_val_196_) == 1)
{
uint8_t v_v_197_; 
v_v_197_ = lean_ctor_get_uint8(v_val_196_, 0);
lean_dec_ref_known(v_val_196_, 0);
return v_v_197_;
}
else
{
uint8_t v___x_198_; 
lean_dec(v_val_196_);
v___x_198_ = lean_unbox(v_defValue_192_);
return v___x_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__3___boxed(lean_object* v_opts_199_, lean_object* v_opt_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__3(v_opts_199_, v_opt_200_);
lean_dec_ref(v_opt_200_);
lean_dec_ref(v_opts_199_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1));
v___x_207_ = l_Lean_MessageData_ofFormat(v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object* v_msgData_208_, lean_object* v_macroStack_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v___x_212_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_210_);
v___x_213_ = l_Lean_Elab_pp_macroStack;
v___x_214_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__3(v___x_212_, v___x_213_);
lean_dec_ref(v___x_212_);
if (v___x_214_ == 0)
{
lean_object* v___x_215_; 
lean_dec(v_macroStack_209_);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v_msgData_208_);
return v___x_215_;
}
else
{
if (lean_obj_tag(v_macroStack_209_) == 0)
{
lean_object* v___x_216_; 
v___x_216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_216_, 0, v_msgData_208_);
return v___x_216_;
}
else
{
lean_object* v_head_217_; lean_object* v_after_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_233_; 
v_head_217_ = lean_ctor_get(v_macroStack_209_, 0);
lean_inc(v_head_217_);
v_after_218_ = lean_ctor_get(v_head_217_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_head_217_);
if (v_isSharedCheck_233_ == 0)
{
lean_object* v_unused_234_; 
v_unused_234_ = lean_ctor_get(v_head_217_, 0);
lean_dec(v_unused_234_);
v___x_220_ = v_head_217_;
v_isShared_221_ = v_isSharedCheck_233_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_after_218_);
lean_dec(v_head_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_233_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_222_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___closed__0);
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 7);
lean_ctor_set(v___x_220_, 1, v___x_222_);
lean_ctor_set(v___x_220_, 0, v_msgData_208_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_msgData_208_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_222_);
v___x_224_ = v_reuseFailAlloc_232_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v_msgData_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_225_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = l_Lean_MessageData_ofSyntax(v_after_218_);
v___x_228_ = l_Lean_indentD(v___x_227_);
v_msgData_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_229_, 0, v___x_226_);
lean_ctor_set(v_msgData_229_, 1, v___x_228_);
v___x_230_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_msgData_229_, v_macroStack_209_);
v___x_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_235_, lean_object* v_macroStack_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_235_, v_macroStack_236_, v___y_237_);
lean_dec_ref(v___y_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object* v_msgData_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; lean_object* v_env_247_; uint8_t v___x_248_; lean_object* v_env_249_; lean_object* v___x_250_; lean_object* v_toCold_251_; lean_object* v_mctx_252_; lean_object* v_lctx_253_; lean_object* v_options_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_246_ = lean_st_ref_get(v___y_244_);
v_env_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc_ref(v_env_247_);
lean_dec(v___x_246_);
v___x_248_ = 0;
v_env_249_ = l_Lean_Environment_setRecordingDeps(v_env_247_, v___x_248_);
v___x_250_ = lean_st_ref_get(v___y_242_);
v_toCold_251_ = lean_ctor_get(v___y_243_, 0);
v_mctx_252_ = lean_ctor_get(v___x_250_, 0);
lean_inc_ref(v_mctx_252_);
lean_dec(v___x_250_);
v_lctx_253_ = lean_ctor_get(v___y_241_, 2);
v_options_254_ = lean_ctor_get(v_toCold_251_, 2);
lean_inc_ref(v_options_254_);
lean_inc_ref(v_lctx_253_);
v___x_255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_255_, 0, v_env_249_);
lean_ctor_set(v___x_255_, 1, v_mctx_252_);
lean_ctor_set(v___x_255_, 2, v_lctx_253_);
lean_ctor_set(v___x_255_, 3, v_options_254_);
v___x_256_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v_msgData_240_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object* v_msgData_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_ref_273_; lean_object* v_macroStack_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_a_277_; lean_object* v___x_278_; lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_ref_273_ = lean_ctor_get(v___y_270_, 2);
v_macroStack_274_ = lean_ctor_get(v___y_266_, 1);
v___x_275_ = l_Lean_Elab_getBetterRef(v_ref_273_, v_macroStack_274_);
v___x_276_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_265_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
v_a_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_276_);
lean_inc(v_macroStack_274_);
v___x_278_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_277_, v_macroStack_274_, v___y_270_);
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_287_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_275_);
lean_ctor_set(v___x_283_, 1, v_a_279_);
if (v_isShared_282_ == 0)
{
lean_ctor_set_tag(v___x_281_, 1);
lean_ctor_set(v___x_281_, 0, v___x_283_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* v_msg_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_296_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0));
v___x_299_ = l_Lean_stringToMessageData(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2));
v___x_302_ = l_Lean_stringToMessageData(v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(lean_object* v_as_303_, size_t v_sz_304_, size_t v_i_305_, lean_object* v_b_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v_a_315_; uint8_t v___x_319_; 
v___x_319_ = lean_usize_dec_lt(v_i_305_, v_sz_304_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v_b_306_);
return v___x_320_;
}
else
{
lean_object* v_array_321_; lean_object* v_start_322_; lean_object* v_stop_323_; uint8_t v___x_324_; 
v_array_321_ = lean_ctor_get(v_b_306_, 0);
v_start_322_ = lean_ctor_get(v_b_306_, 1);
v_stop_323_ = lean_ctor_get(v_b_306_, 2);
v___x_324_ = lean_nat_dec_lt(v_start_322_, v_stop_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_b_306_);
return v___x_325_;
}
else
{
lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_354_; 
lean_inc(v_stop_323_);
lean_inc(v_start_322_);
lean_inc_ref(v_array_321_);
v_isSharedCheck_354_ = !lean_is_exclusive(v_b_306_);
if (v_isSharedCheck_354_ == 0)
{
lean_object* v_unused_355_; lean_object* v_unused_356_; lean_object* v_unused_357_; 
v_unused_355_ = lean_ctor_get(v_b_306_, 2);
lean_dec(v_unused_355_);
v_unused_356_ = lean_ctor_get(v_b_306_, 1);
lean_dec(v_unused_356_);
v_unused_357_ = lean_ctor_get(v_b_306_, 0);
lean_dec(v_unused_357_);
v___x_327_ = v_b_306_;
v_isShared_328_ = v_isSharedCheck_354_;
goto v_resetjp_326_;
}
else
{
lean_dec(v_b_306_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_354_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_a_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_334_; 
v_a_329_ = lean_array_uget_borrowed(v_as_303_, v_i_305_);
v___x_330_ = lean_array_fget(v_array_321_, v_start_322_);
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_add(v_start_322_, v___x_331_);
lean_dec(v_start_322_);
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 1, v___x_332_);
v___x_334_ = v___x_327_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_array_321_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v___x_332_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_stop_323_);
v___x_334_ = v_reuseFailAlloc_353_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_335_ = lean_array_get_size(v_a_329_);
v___x_336_ = lean_unsigned_to_nat(0u);
v___x_337_ = lean_nat_dec_eq(v___x_335_, v___x_336_);
if (v___x_337_ == 0)
{
lean_dec(v___x_330_);
v_a_315_ = v___x_334_;
goto v___jp_314_;
}
else
{
lean_object* v_declName_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_declName_338_ = lean_ctor_get(v___x_330_, 3);
lean_inc(v_declName_338_);
lean_dec(v___x_330_);
v___x_339_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1);
v___x_340_ = l_Lean_MessageData_ofName(v_declName_338_);
v___x_341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3);
v___x_343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_343_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_dec_ref_known(v___x_344_, 1);
v_a_315_ = v___x_334_;
goto v___jp_314_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec_ref(v___x_334_);
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_344_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
}
}
}
}
v___jp_314_:
{
size_t v___x_316_; size_t v___x_317_; 
v___x_316_ = ((size_t)1ULL);
v___x_317_ = lean_usize_add(v_i_305_, v___x_316_);
v_i_305_ = v___x_317_;
v_b_306_ = v_a_315_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object* v_as_358_, lean_object* v_sz_359_, lean_object* v_i_360_, lean_object* v_b_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_){
_start:
{
size_t v_sz_boxed_369_; size_t v_i_boxed_370_; lean_object* v_res_371_; 
v_sz_boxed_369_ = lean_unbox_usize(v_sz_359_);
lean_dec(v_sz_359_);
v_i_boxed_370_ = lean_unbox_usize(v_i_360_);
lean_dec(v_i_360_);
v_res_371_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_as_358_, v_sz_boxed_369_, v_i_boxed_370_, v_b_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec_ref(v_as_358_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(size_t v_sz_372_, size_t v_i_373_, lean_object* v_bs_374_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = lean_usize_dec_lt(v_i_373_, v_sz_372_);
if (v___x_375_ == 0)
{
return v_bs_374_;
}
else
{
lean_object* v_v_376_; lean_object* v_declName_377_; lean_object* v___x_378_; lean_object* v_bs_x27_379_; size_t v___x_380_; size_t v___x_381_; lean_object* v___x_382_; 
v_v_376_ = lean_array_uget_borrowed(v_bs_374_, v_i_373_);
v_declName_377_ = lean_ctor_get(v_v_376_, 3);
lean_inc(v_declName_377_);
v___x_378_ = lean_unsigned_to_nat(0u);
v_bs_x27_379_ = lean_array_uset(v_bs_374_, v_i_373_, v___x_378_);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_add(v_i_373_, v___x_380_);
v___x_382_ = lean_array_uset(v_bs_x27_379_, v_i_373_, v_declName_377_);
v_i_373_ = v___x_381_;
v_bs_374_ = v___x_382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_sz_384_, lean_object* v_i_385_, lean_object* v_bs_386_){
_start:
{
size_t v_sz_boxed_387_; size_t v_i_boxed_388_; lean_object* v_res_389_; 
v_sz_boxed_387_ = lean_unbox_usize(v_sz_384_);
lean_dec(v_sz_384_);
v_i_boxed_388_ = lean_unbox_usize(v_i_385_);
lean_dec(v_i_385_);
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_boxed_387_, v_i_boxed_388_, v_bs_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_a_390_, lean_object* v___x_391_, size_t v_sz_392_, size_t v_i_393_, lean_object* v_bs_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
uint8_t v___x_398_; 
v___x_398_ = lean_usize_dec_lt(v_i_393_, v_sz_392_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
lean_dec(v___x_391_);
lean_dec_ref(v_a_390_);
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v_bs_394_);
return v___x_399_;
}
else
{
lean_object* v_v_400_; lean_object* v_ref_401_; uint8_t v_kind_402_; lean_object* v_levelParams_403_; lean_object* v_modifiers_404_; lean_object* v_declName_405_; lean_object* v_binders_406_; lean_object* v_numSectionVars_407_; lean_object* v_type_408_; lean_object* v_value_409_; lean_object* v_termination_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_436_; 
v_v_400_ = lean_array_uget(v_bs_394_, v_i_393_);
v_ref_401_ = lean_ctor_get(v_v_400_, 0);
v_kind_402_ = lean_ctor_get_uint8(v_v_400_, sizeof(void*)*9);
v_levelParams_403_ = lean_ctor_get(v_v_400_, 1);
v_modifiers_404_ = lean_ctor_get(v_v_400_, 2);
v_declName_405_ = lean_ctor_get(v_v_400_, 3);
v_binders_406_ = lean_ctor_get(v_v_400_, 4);
v_numSectionVars_407_ = lean_ctor_get(v_v_400_, 5);
v_type_408_ = lean_ctor_get(v_v_400_, 6);
v_value_409_ = lean_ctor_get(v_v_400_, 7);
v_termination_410_ = lean_ctor_get(v_v_400_, 8);
v_isSharedCheck_436_ = !lean_is_exclusive(v_v_400_);
if (v_isSharedCheck_436_ == 0)
{
v___x_412_ = v_v_400_;
v_isShared_413_ = v_isSharedCheck_436_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_termination_410_);
lean_inc(v_value_409_);
lean_inc(v_type_408_);
lean_inc(v_numSectionVars_407_);
lean_inc(v_binders_406_);
lean_inc(v_declName_405_);
lean_inc(v_modifiers_404_);
lean_inc(v_levelParams_403_);
lean_inc(v_ref_401_);
lean_dec(v_v_400_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_436_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
size_t v_sz_414_; lean_object* v___x_415_; lean_object* v_bs_x27_416_; size_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_sz_414_ = lean_array_size(v_a_390_);
v___x_415_ = lean_unsigned_to_nat(0u);
v_bs_x27_416_ = lean_array_uset(v_bs_394_, v_i_393_, v___x_415_);
v___x_417_ = ((size_t)0ULL);
lean_inc_ref(v_a_390_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_414_, v___x_417_, v_a_390_);
lean_inc(v___x_391_);
v___x_419_ = l_Lean_Meta_unfoldIfArgIsAppOf(v___x_418_, v___x_391_, v_value_409_, v___y_395_, v___y_396_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_a_420_);
lean_dec_ref_known(v___x_419_, 1);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 7, v_a_420_);
v___x_422_ = v___x_412_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_ref_401_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_levelParams_403_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_modifiers_404_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_declName_405_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v_binders_406_);
lean_ctor_set(v_reuseFailAlloc_427_, 5, v_numSectionVars_407_);
lean_ctor_set(v_reuseFailAlloc_427_, 6, v_type_408_);
lean_ctor_set(v_reuseFailAlloc_427_, 7, v_a_420_);
lean_ctor_set(v_reuseFailAlloc_427_, 8, v_termination_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*9, v_kind_402_);
v___x_422_ = v_reuseFailAlloc_427_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
size_t v___x_423_; size_t v___x_424_; lean_object* v___x_425_; 
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_add(v_i_393_, v___x_423_);
v___x_425_ = lean_array_uset(v_bs_x27_416_, v_i_393_, v___x_422_);
v_i_393_ = v___x_424_;
v_bs_394_ = v___x_425_;
goto _start;
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_435_; 
lean_dec_ref(v_bs_x27_416_);
lean_del_object(v___x_412_);
lean_dec_ref(v_termination_410_);
lean_dec_ref(v_type_408_);
lean_dec(v_numSectionVars_407_);
lean_dec(v_binders_406_);
lean_dec(v_declName_405_);
lean_dec_ref(v_modifiers_404_);
lean_dec(v_levelParams_403_);
lean_dec(v_ref_401_);
lean_dec(v___x_391_);
lean_dec_ref(v_a_390_);
v_a_428_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_435_ == 0)
{
v___x_430_ = v___x_419_;
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_419_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_435_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_433_; 
if (v_isShared_431_ == 0)
{
v___x_433_ = v___x_430_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_428_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_a_437_, lean_object* v___x_438_, lean_object* v_sz_439_, lean_object* v_i_440_, lean_object* v_bs_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
size_t v_sz_boxed_445_; size_t v_i_boxed_446_; lean_object* v_res_447_; 
v_sz_boxed_445_ = lean_unbox_usize(v_sz_439_);
lean_dec(v_sz_439_);
v_i_boxed_446_ = lean_unbox_usize(v_i_440_);
lean_dec(v_i_440_);
v_res_447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_437_, v___x_438_, v_sz_boxed_445_, v_i_boxed_446_, v_bs_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* v_a_448_, size_t v_sz_449_, size_t v___x_450_, lean_object* v___x_451_, lean_object* v___x_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_448_, v_sz_449_, v___x_450_, v___x_451_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_object* v___x_461_; 
lean_dec_ref_known(v___x_460_, 1);
lean_inc_ref(v_a_448_);
v___x_461_ = l_Lean_Elab_getFixedParamPerms(v_a_448_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc_n(v_a_462_, 2);
lean_dec_ref_known(v___x_461_, 1);
lean_inc_ref(v_a_448_);
v___x_463_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_462_, v_sz_449_, v___x_450_, v_a_448_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; size_t v_sz_468_; lean_object* v___x_469_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v___x_465_ = lean_unsigned_to_nat(0u);
v___x_466_ = lean_array_get_size(v_a_448_);
lean_inc_ref(v_a_448_);
v___x_467_ = l_Array_toSubarray___redArg(v_a_448_, v___x_465_, v___x_466_);
v_sz_468_ = lean_array_size(v_a_464_);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_a_464_, v_sz_468_, v___x_450_, v___x_467_, v___y_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v___x_470_; lean_object* v_numSectionVars_471_; lean_object* v___x_472_; 
lean_dec_ref_known(v___x_469_, 1);
v___x_470_ = lean_array_get_borrowed(v___x_452_, v_a_448_, v___x_465_);
v_numSectionVars_471_ = lean_ctor_get(v___x_470_, 5);
lean_inc(v_numSectionVars_471_);
lean_inc_ref(v_a_448_);
v___x_472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_448_, v_numSectionVars_471_, v_sz_449_, v___x_450_, v_a_448_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref_known(v___x_472_, 1);
lean_inc(v_a_464_);
lean_inc(v_a_462_);
v___x_474_ = l_Lean_Elab_WF_packMutual(v_a_462_, v_a_464_, v_a_473_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_484_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_484_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_484_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_484_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v_a_464_);
lean_ctor_set(v___x_479_, 1, v_a_475_);
v___x_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_480_, 0, v_a_462_);
lean_ctor_set(v___x_480_, 1, v___x_479_);
if (v_isShared_478_ == 0)
{
lean_ctor_set(v___x_477_, 0, v___x_480_);
v___x_482_ = v___x_477_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
lean_dec(v_a_464_);
lean_dec(v_a_462_);
v_a_485_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_474_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_474_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
lean_dec(v_a_464_);
lean_dec(v_a_462_);
v_a_493_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_472_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_472_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec(v_a_464_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_448_);
v_a_501_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_469_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_469_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_a_462_);
lean_dec_ref(v_a_448_);
v_a_509_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_463_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_463_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_a_448_);
v_a_517_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_461_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_461_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
else
{
lean_object* v_a_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_532_; 
lean_dec_ref(v_a_448_);
v_a_525_ = lean_ctor_get(v___x_460_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_460_);
if (v_isSharedCheck_532_ == 0)
{
v___x_527_ = v___x_460_;
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_a_525_);
lean_dec(v___x_460_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_532_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_530_; 
if (v_isShared_528_ == 0)
{
v___x_530_ = v___x_527_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_a_525_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object* v_a_533_, lean_object* v_sz_534_, lean_object* v___x_535_, lean_object* v___x_536_, lean_object* v___x_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
size_t v_sz_boxed_545_; size_t v___x_44892__boxed_546_; lean_object* v_res_547_; 
v_sz_boxed_545_ = lean_unbox_usize(v_sz_534_);
lean_dec(v_sz_534_);
v___x_44892__boxed_546_ = lean_unbox_usize(v___x_535_);
lean_dec(v___x_535_);
v_res_547_ = l_Lean_Elab_wfRecursion___lam__0(v_a_533_, v_sz_boxed_545_, v___x_44892__boxed_546_, v___x_536_, v___x_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v___x_537_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* v_snd_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; 
lean_inc_ref(v_snd_548_);
v___x_556_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_548_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_ref_557_; uint8_t v_kind_558_; lean_object* v_levelParams_559_; lean_object* v_modifiers_560_; lean_object* v_declName_561_; lean_object* v_binders_562_; lean_object* v_numSectionVars_563_; lean_object* v_type_564_; lean_object* v_value_565_; lean_object* v_termination_566_; lean_object* v___x_568_; uint8_t v_isShared_569_; uint8_t v_isSharedCheck_592_; 
lean_dec_ref_known(v___x_556_, 1);
v_ref_557_ = lean_ctor_get(v_snd_548_, 0);
v_kind_558_ = lean_ctor_get_uint8(v_snd_548_, sizeof(void*)*9);
v_levelParams_559_ = lean_ctor_get(v_snd_548_, 1);
v_modifiers_560_ = lean_ctor_get(v_snd_548_, 2);
v_declName_561_ = lean_ctor_get(v_snd_548_, 3);
v_binders_562_ = lean_ctor_get(v_snd_548_, 4);
v_numSectionVars_563_ = lean_ctor_get(v_snd_548_, 5);
v_type_564_ = lean_ctor_get(v_snd_548_, 6);
v_value_565_ = lean_ctor_get(v_snd_548_, 7);
v_termination_566_ = lean_ctor_get(v_snd_548_, 8);
v_isSharedCheck_592_ = !lean_is_exclusive(v_snd_548_);
if (v_isSharedCheck_592_ == 0)
{
v___x_568_ = v_snd_548_;
v_isShared_569_ = v_isSharedCheck_592_;
goto v_resetjp_567_;
}
else
{
lean_inc(v_termination_566_);
lean_inc(v_value_565_);
lean_inc(v_type_564_);
lean_inc(v_numSectionVars_563_);
lean_inc(v_binders_562_);
lean_inc(v_declName_561_);
lean_inc(v_modifiers_560_);
lean_inc(v_levelParams_559_);
lean_inc(v_ref_557_);
lean_dec(v_snd_548_);
v___x_568_ = lean_box(0);
v_isShared_569_ = v_isSharedCheck_592_;
goto v_resetjp_567_;
}
v_resetjp_567_:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_Elab_WF_preprocess(v_value_565_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_583_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_583_ == 0)
{
v___x_573_ = v___x_570_;
v_isShared_574_ = v_isSharedCheck_583_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_570_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_583_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v_expr_575_; lean_object* v___x_577_; 
v_expr_575_ = lean_ctor_get(v_a_571_, 0);
lean_inc_ref(v_expr_575_);
if (v_isShared_569_ == 0)
{
lean_ctor_set(v___x_568_, 7, v_expr_575_);
v___x_577_ = v___x_568_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_ref_557_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_levelParams_559_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_modifiers_560_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_declName_561_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v_binders_562_);
lean_ctor_set(v_reuseFailAlloc_582_, 5, v_numSectionVars_563_);
lean_ctor_set(v_reuseFailAlloc_582_, 6, v_type_564_);
lean_ctor_set(v_reuseFailAlloc_582_, 7, v_expr_575_);
lean_ctor_set(v_reuseFailAlloc_582_, 8, v_termination_566_);
lean_ctor_set_uint8(v_reuseFailAlloc_582_, sizeof(void*)*9, v_kind_558_);
v___x_577_ = v_reuseFailAlloc_582_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v_a_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 0, v___x_578_);
v___x_580_ = v___x_573_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_del_object(v___x_568_);
lean_dec_ref(v_termination_566_);
lean_dec_ref(v_type_564_);
lean_dec(v_numSectionVars_563_);
lean_dec(v_binders_562_);
lean_dec(v_declName_561_);
lean_dec_ref(v_modifiers_560_);
lean_dec(v_levelParams_559_);
lean_dec(v_ref_557_);
v_a_584_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_570_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_570_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec_ref(v_snd_548_);
v_a_593_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_556_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_556_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* v_snd_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Elab_wfRecursion___lam__1(v_snd_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* v___x_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_toCold_621_; lean_object* v_options_622_; uint8_t v_hasTrace_623_; 
v_toCold_621_ = lean_ctor_get(v___y_618_, 0);
v_options_622_ = lean_ctor_get(v_toCold_621_, 2);
v_hasTrace_623_ = lean_ctor_get_uint8(v_options_622_, sizeof(void*)*1);
if (v_hasTrace_623_ == 0)
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v___x_613_);
v___x_624_ = lean_box(v_hasTrace_623_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
else
{
lean_object* v_inheritedTraceOptions_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v_inheritedTraceOptions_626_ = lean_ctor_get(v_toCold_621_, 11);
v___x_627_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__1));
v___x_628_ = l_Lean_Name_append(v___x_627_, v___x_613_);
v___x_629_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_626_, v_options_622_, v___x_628_);
lean_dec(v___x_628_);
v___x_630_ = lean_box(v___x_629_);
v___x_631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
return v___x_631_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object* v___x_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Elab_wfRecursion___lam__2(v___x_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_640_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0(void){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_641_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__1(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0);
v___x_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__1);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object* v___dummy_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg();
return v_res_647_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_648_; double v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = lean_float_of_nat(v___x_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object* v_cls_653_, lean_object* v_msg_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v_ref_660_; lean_object* v___x_661_; lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_707_; 
v_ref_660_ = lean_ctor_get(v___y_657_, 2);
v___x_661_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_);
v_a_662_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_707_ == 0)
{
v___x_664_ = v___x_661_;
v_isShared_665_ = v_isSharedCheck_707_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_661_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_707_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_666_; lean_object* v_traceState_667_; lean_object* v_env_668_; lean_object* v_nextMacroScope_669_; lean_object* v_ngen_670_; lean_object* v_auxDeclNGen_671_; lean_object* v_cache_672_; lean_object* v_recordedDeps_673_; lean_object* v_messages_674_; lean_object* v_infoState_675_; lean_object* v_snapshotTasks_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_706_; 
v___x_666_ = lean_st_ref_take(v___y_658_);
v_traceState_667_ = lean_ctor_get(v___x_666_, 4);
v_env_668_ = lean_ctor_get(v___x_666_, 0);
v_nextMacroScope_669_ = lean_ctor_get(v___x_666_, 1);
v_ngen_670_ = lean_ctor_get(v___x_666_, 2);
v_auxDeclNGen_671_ = lean_ctor_get(v___x_666_, 3);
v_cache_672_ = lean_ctor_get(v___x_666_, 5);
v_recordedDeps_673_ = lean_ctor_get(v___x_666_, 6);
v_messages_674_ = lean_ctor_get(v___x_666_, 7);
v_infoState_675_ = lean_ctor_get(v___x_666_, 8);
v_snapshotTasks_676_ = lean_ctor_get(v___x_666_, 9);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_666_);
if (v_isSharedCheck_706_ == 0)
{
v___x_678_ = v___x_666_;
v_isShared_679_ = v_isSharedCheck_706_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_snapshotTasks_676_);
lean_inc(v_infoState_675_);
lean_inc(v_messages_674_);
lean_inc(v_recordedDeps_673_);
lean_inc(v_cache_672_);
lean_inc(v_traceState_667_);
lean_inc(v_auxDeclNGen_671_);
lean_inc(v_ngen_670_);
lean_inc(v_nextMacroScope_669_);
lean_inc(v_env_668_);
lean_dec(v___x_666_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_706_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
uint64_t v_tid_680_; lean_object* v_traces_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_705_; 
v_tid_680_ = lean_ctor_get_uint64(v_traceState_667_, sizeof(void*)*1);
v_traces_681_ = lean_ctor_get(v_traceState_667_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_traceState_667_);
if (v_isSharedCheck_705_ == 0)
{
v___x_683_ = v_traceState_667_;
v_isShared_684_ = v_isSharedCheck_705_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_traces_681_);
lean_dec(v_traceState_667_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_705_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; lean_object* v___x_686_; double v___x_687_; uint8_t v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_685_ = lean_box(0);
v___x_686_ = lean_box(0);
v___x_687_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0);
v___x_688_ = 0;
v___x_689_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__1));
v___x_690_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_690_, 0, v_cls_653_);
lean_ctor_set(v___x_690_, 1, v___x_686_);
lean_ctor_set(v___x_690_, 2, v___x_689_);
lean_ctor_set_float(v___x_690_, sizeof(void*)*3, v___x_687_);
lean_ctor_set_float(v___x_690_, sizeof(void*)*3 + 8, v___x_687_);
lean_ctor_set_uint8(v___x_690_, sizeof(void*)*3 + 16, v___x_688_);
v___x_691_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__2));
v___x_692_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_692_, 0, v___x_690_);
lean_ctor_set(v___x_692_, 1, v_a_662_);
lean_ctor_set(v___x_692_, 2, v___x_691_);
lean_inc(v_ref_660_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v_ref_660_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___x_694_ = l_Lean_PersistentArray_push___redArg(v_traces_681_, v___x_693_);
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v___x_694_);
v___x_696_ = v___x_683_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_694_);
lean_ctor_set_uint64(v_reuseFailAlloc_704_, sizeof(void*)*1, v_tid_680_);
v___x_696_ = v_reuseFailAlloc_704_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_698_; 
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 4, v___x_696_);
v___x_698_ = v___x_678_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_env_668_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_nextMacroScope_669_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_ngen_670_);
lean_ctor_set(v_reuseFailAlloc_703_, 3, v_auxDeclNGen_671_);
lean_ctor_set(v_reuseFailAlloc_703_, 4, v___x_696_);
lean_ctor_set(v_reuseFailAlloc_703_, 5, v_cache_672_);
lean_ctor_set(v_reuseFailAlloc_703_, 6, v_recordedDeps_673_);
lean_ctor_set(v_reuseFailAlloc_703_, 7, v_messages_674_);
lean_ctor_set(v_reuseFailAlloc_703_, 8, v_infoState_675_);
lean_ctor_set(v_reuseFailAlloc_703_, 9, v_snapshotTasks_676_);
v___x_698_ = v_reuseFailAlloc_703_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = lean_st_ref_put(v___y_658_, v___x_698_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_685_);
v___x_701_ = v___x_664_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v___x_685_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object* v_cls_708_, lean_object* v_msg_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_cls_708_, v_msg_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
return v_res_715_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0(uint8_t v_suppressElabErrors_723_, lean_object* v_x_724_){
_start:
{
if (lean_obj_tag(v_x_724_) == 1)
{
lean_object* v_pre_725_; 
v_pre_725_ = lean_ctor_get(v_x_724_, 0);
switch(lean_obj_tag(v_pre_725_))
{
case 1:
{
lean_object* v_pre_726_; 
v_pre_726_ = lean_ctor_get(v_pre_725_, 0);
switch(lean_obj_tag(v_pre_726_))
{
case 0:
{
lean_object* v_str_727_; lean_object* v_str_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_str_727_ = lean_ctor_get(v_x_724_, 1);
v_str_728_ = lean_ctor_get(v_pre_725_, 1);
v___x_729_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__0));
v___x_730_ = lean_string_dec_eq(v_str_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__1));
v___x_732_ = lean_string_dec_eq(v_str_728_, v___x_731_);
if (v___x_732_ == 0)
{
return v___x_732_;
}
else
{
lean_object* v___x_733_; uint8_t v___x_734_; 
v___x_733_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__2));
v___x_734_ = lean_string_dec_eq(v_str_727_, v___x_733_);
if (v___x_734_ == 0)
{
return v___x_734_;
}
else
{
return v_suppressElabErrors_723_;
}
}
}
else
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__3));
v___x_736_ = lean_string_dec_eq(v_str_727_, v___x_735_);
if (v___x_736_ == 0)
{
return v___x_736_;
}
else
{
return v_suppressElabErrors_723_;
}
}
}
case 1:
{
lean_object* v_pre_737_; 
v_pre_737_ = lean_ctor_get(v_pre_726_, 0);
if (lean_obj_tag(v_pre_737_) == 0)
{
lean_object* v_str_738_; lean_object* v_str_739_; lean_object* v_str_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_str_738_ = lean_ctor_get(v_x_724_, 1);
v_str_739_ = lean_ctor_get(v_pre_725_, 1);
v_str_740_ = lean_ctor_get(v_pre_726_, 1);
v___x_741_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__4));
v___x_742_ = lean_string_dec_eq(v_str_740_, v___x_741_);
if (v___x_742_ == 0)
{
return v___x_742_;
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_743_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__5));
v___x_744_ = lean_string_dec_eq(v_str_739_, v___x_743_);
if (v___x_744_ == 0)
{
return v___x_744_;
}
else
{
lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_745_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___closed__6));
v___x_746_ = lean_string_dec_eq(v_str_738_, v___x_745_);
if (v___x_746_ == 0)
{
return v___x_746_;
}
else
{
return v_suppressElabErrors_723_;
}
}
}
}
else
{
uint8_t v___x_747_; 
v___x_747_ = 0;
return v___x_747_;
}
}
default: 
{
uint8_t v___x_748_; 
v___x_748_ = 0;
return v___x_748_;
}
}
}
case 0:
{
lean_object* v_str_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_str_749_ = lean_ctor_get(v_x_724_, 1);
v___x_750_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__0));
v___x_751_ = lean_string_dec_eq(v_str_749_, v___x_750_);
if (v___x_751_ == 0)
{
return v___x_751_;
}
else
{
return v_suppressElabErrors_723_;
}
}
default: 
{
uint8_t v___x_752_; 
v___x_752_ = 0;
return v___x_752_;
}
}
}
else
{
uint8_t v___x_753_; 
v___x_753_ = 0;
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_754_, lean_object* v_x_755_){
_start:
{
uint8_t v_suppressElabErrors_boxed_756_; uint8_t v_res_757_; lean_object* v_r_758_; 
v_suppressElabErrors_boxed_756_ = lean_unbox(v_suppressElabErrors_754_);
v_res_757_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0(v_suppressElabErrors_boxed_756_, v_x_755_);
lean_dec(v_x_755_);
v_r_758_ = lean_box(v_res_757_);
return v_r_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg(lean_object* v_ref_759_, lean_object* v_msgData_760_, uint8_t v_severity_761_, uint8_t v_isSilent_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___y_769_; lean_object* v___y_770_; uint8_t v___y_771_; uint8_t v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v_toCold_776_; lean_object* v___y_777_; lean_object* v___y_806_; lean_object* v___y_807_; uint8_t v___y_808_; lean_object* v___y_809_; uint8_t v___y_810_; uint8_t v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; uint8_t v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; uint8_t v___y_836_; uint8_t v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; uint8_t v___y_843_; uint8_t v___y_844_; uint8_t v___x_854_; uint8_t v___y_856_; uint8_t v___x_862_; 
v___x_854_ = 2;
v___x_862_ = l_Lean_instBEqMessageSeverity_beq(v_severity_761_, v___x_854_);
if (v___x_862_ == 0)
{
v___y_856_ = v___x_862_;
goto v___jp_855_;
}
else
{
uint8_t v___x_863_; 
lean_inc_ref(v_msgData_760_);
v___x_863_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_760_);
if (v___x_863_ == 0)
{
v___y_856_ = v___x_863_;
goto v___jp_855_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec_ref(v_msgData_760_);
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
}
v___jp_768_:
{
lean_object* v_currNamespace_778_; lean_object* v_openDecls_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_env_784_; lean_object* v_nextMacroScope_785_; lean_object* v_ngen_786_; lean_object* v_auxDeclNGen_787_; lean_object* v_traceState_788_; lean_object* v_cache_789_; lean_object* v_recordedDeps_790_; lean_object* v_messages_791_; lean_object* v_infoState_792_; lean_object* v_snapshotTasks_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_804_; 
v_currNamespace_778_ = lean_ctor_get(v_toCold_776_, 4);
v_openDecls_779_ = lean_ctor_get(v_toCold_776_, 5);
lean_inc(v_openDecls_779_);
lean_inc(v_currNamespace_778_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v_currNamespace_778_);
lean_ctor_set(v___x_780_, 1, v_openDecls_779_);
v___x_781_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___y_775_);
lean_inc_ref(v___y_769_);
lean_inc_ref(v___y_774_);
v___x_782_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_782_, 0, v___y_774_);
lean_ctor_set(v___x_782_, 1, v___y_773_);
lean_ctor_set(v___x_782_, 2, v___y_770_);
lean_ctor_set(v___x_782_, 3, v___y_769_);
lean_ctor_set(v___x_782_, 4, v___x_781_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*5, v___y_771_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*5 + 1, v___y_772_);
lean_ctor_set_uint8(v___x_782_, sizeof(void*)*5 + 2, v_isSilent_762_);
v___x_783_ = lean_st_ref_take(v___y_777_);
v_env_784_ = lean_ctor_get(v___x_783_, 0);
v_nextMacroScope_785_ = lean_ctor_get(v___x_783_, 1);
v_ngen_786_ = lean_ctor_get(v___x_783_, 2);
v_auxDeclNGen_787_ = lean_ctor_get(v___x_783_, 3);
v_traceState_788_ = lean_ctor_get(v___x_783_, 4);
v_cache_789_ = lean_ctor_get(v___x_783_, 5);
v_recordedDeps_790_ = lean_ctor_get(v___x_783_, 6);
v_messages_791_ = lean_ctor_get(v___x_783_, 7);
v_infoState_792_ = lean_ctor_get(v___x_783_, 8);
v_snapshotTasks_793_ = lean_ctor_get(v___x_783_, 9);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_804_ == 0)
{
v___x_795_ = v___x_783_;
v_isShared_796_ = v_isSharedCheck_804_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_snapshotTasks_793_);
lean_inc(v_infoState_792_);
lean_inc(v_messages_791_);
lean_inc(v_recordedDeps_790_);
lean_inc(v_cache_789_);
lean_inc(v_traceState_788_);
lean_inc(v_auxDeclNGen_787_);
lean_inc(v_ngen_786_);
lean_inc(v_nextMacroScope_785_);
lean_inc(v_env_784_);
lean_dec(v___x_783_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_804_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_797_ = lean_box(0);
v___x_798_ = l_Lean_MessageLog_add(v___x_782_, v_messages_791_);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 7, v___x_798_);
v___x_800_ = v___x_795_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_env_784_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_nextMacroScope_785_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_ngen_786_);
lean_ctor_set(v_reuseFailAlloc_803_, 3, v_auxDeclNGen_787_);
lean_ctor_set(v_reuseFailAlloc_803_, 4, v_traceState_788_);
lean_ctor_set(v_reuseFailAlloc_803_, 5, v_cache_789_);
lean_ctor_set(v_reuseFailAlloc_803_, 6, v_recordedDeps_790_);
lean_ctor_set(v_reuseFailAlloc_803_, 7, v___x_798_);
lean_ctor_set(v_reuseFailAlloc_803_, 8, v_infoState_792_);
lean_ctor_set(v_reuseFailAlloc_803_, 9, v_snapshotTasks_793_);
v___x_800_ = v_reuseFailAlloc_803_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_st_ref_put(v___y_777_, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_797_);
return v___x_802_;
}
}
}
v___jp_805_:
{
lean_object* v_fileName_814_; lean_object* v_fileMap_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_831_; 
v_fileName_814_ = lean_ctor_get(v___y_809_, 0);
v_fileMap_815_ = lean_ctor_get(v___y_809_, 1);
v___x_816_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_760_);
v___x_817_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_816_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
v_a_818_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_831_ == 0)
{
v___x_820_ = v___x_817_;
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_817_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_831_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_inc_ref_n(v_fileMap_815_, 2);
v___x_822_ = l_Lean_FileMap_toPosition(v_fileMap_815_, v___y_812_);
lean_dec(v___y_812_);
v___x_823_ = l_Lean_FileMap_toPosition(v_fileMap_815_, v___y_813_);
lean_dec(v___y_813_);
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
v___x_825_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__1));
if (v___y_808_ == 0)
{
lean_del_object(v___x_820_);
lean_dec_ref(v___y_807_);
v___y_769_ = v___x_825_;
v___y_770_ = v___x_824_;
v___y_771_ = v___y_810_;
v___y_772_ = v___y_811_;
v___y_773_ = v___x_822_;
v___y_774_ = v_fileName_814_;
v___y_775_ = v_a_818_;
v_toCold_776_ = v___y_806_;
v___y_777_ = v___y_766_;
goto v___jp_768_;
}
else
{
uint8_t v___x_826_; 
lean_inc(v_a_818_);
v___x_826_ = l_Lean_MessageData_hasTag(v___y_807_, v_a_818_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec_ref_known(v___x_824_, 1);
lean_dec_ref(v___x_822_);
lean_dec(v_a_818_);
v___x_827_ = lean_box(0);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 0, v___x_827_);
v___x_829_ = v___x_820_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
lean_del_object(v___x_820_);
v___y_769_ = v___x_825_;
v___y_770_ = v___x_824_;
v___y_771_ = v___y_810_;
v___y_772_ = v___y_811_;
v___y_773_ = v___x_822_;
v___y_774_ = v_fileName_814_;
v___y_775_ = v_a_818_;
v_toCold_776_ = v___y_806_;
v___y_777_ = v___y_766_;
goto v___jp_768_;
}
}
}
}
v___jp_832_:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Syntax_getTailPos_x3f(v___y_838_, v___y_836_);
lean_dec(v___y_838_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_inc(v___y_839_);
v___y_806_ = v___y_834_;
v___y_807_ = v___y_835_;
v___y_808_ = v___y_833_;
v___y_809_ = v___y_834_;
v___y_810_ = v___y_836_;
v___y_811_ = v___y_837_;
v___y_812_ = v___y_839_;
v___y_813_ = v___y_839_;
goto v___jp_805_;
}
else
{
lean_object* v_val_841_; 
v_val_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc(v_val_841_);
lean_dec_ref_known(v___x_840_, 1);
v___y_806_ = v___y_834_;
v___y_807_ = v___y_835_;
v___y_808_ = v___y_833_;
v___y_809_ = v___y_834_;
v___y_810_ = v___y_836_;
v___y_811_ = v___y_837_;
v___y_812_ = v___y_839_;
v___y_813_ = v_val_841_;
goto v___jp_805_;
}
}
v___jp_842_:
{
lean_object* v_toCold_845_; lean_object* v_ref_846_; uint8_t v_suppressElabErrors_847_; lean_object* v___x_848_; lean_object* v___f_849_; lean_object* v_ref_850_; lean_object* v___x_851_; 
v_toCold_845_ = lean_ctor_get(v___y_765_, 0);
v_ref_846_ = lean_ctor_get(v___y_765_, 2);
v_suppressElabErrors_847_ = lean_ctor_get_uint8(v___y_765_, sizeof(void*)*3 + 2);
v___x_848_ = lean_box(v_suppressElabErrors_847_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_849_, 0, v___x_848_);
v_ref_850_ = l_Lean_replaceRef(v_ref_759_, v_ref_846_);
v___x_851_ = l_Lean_Syntax_getPos_x3f(v_ref_850_, v___y_843_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_852_; 
v___x_852_ = lean_unsigned_to_nat(0u);
v___y_833_ = v_suppressElabErrors_847_;
v___y_834_ = v_toCold_845_;
v___y_835_ = v___f_849_;
v___y_836_ = v___y_843_;
v___y_837_ = v___y_844_;
v___y_838_ = v_ref_850_;
v___y_839_ = v___x_852_;
goto v___jp_832_;
}
else
{
lean_object* v_val_853_; 
v_val_853_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_val_853_);
lean_dec_ref_known(v___x_851_, 1);
v___y_833_ = v_suppressElabErrors_847_;
v___y_834_ = v_toCold_845_;
v___y_835_ = v___f_849_;
v___y_836_ = v___y_843_;
v___y_837_ = v___y_844_;
v___y_838_ = v_ref_850_;
v___y_839_ = v_val_853_;
goto v___jp_832_;
}
}
v___jp_855_:
{
uint8_t v___x_857_; uint8_t v___x_858_; 
v___x_857_ = 1;
v___x_858_ = l_Lean_instBEqMessageSeverity_beq(v_severity_761_, v___x_857_);
if (v___x_858_ == 0)
{
v___y_843_ = v___y_856_;
v___y_844_ = v_severity_761_;
goto v___jp_842_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_859_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_765_);
v___x_860_ = l_Lean_warningAsError;
v___x_861_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__3(v___x_859_, v___x_860_);
lean_dec_ref(v___x_859_);
if (v___x_861_ == 0)
{
v___y_843_ = v___y_856_;
v___y_844_ = v_severity_761_;
goto v___jp_842_;
}
else
{
v___y_843_ = v___y_856_;
v___y_844_ = v___x_854_;
goto v___jp_842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg___boxed(lean_object* v_ref_866_, lean_object* v_msgData_867_, lean_object* v_severity_868_, lean_object* v_isSilent_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
uint8_t v_severity_boxed_875_; uint8_t v_isSilent_boxed_876_; lean_object* v_res_877_; 
v_severity_boxed_875_ = lean_unbox(v_severity_868_);
v_isSilent_boxed_876_ = lean_unbox(v_isSilent_869_);
v_res_877_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg(v_ref_866_, v_msgData_867_, v_severity_boxed_875_, v_isSilent_boxed_876_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v_ref_866_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v_ref_878_, lean_object* v_msgData_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
uint8_t v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; 
v___x_887_ = 1;
v___x_888_ = 0;
v___x_889_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg(v_ref_878_, v_msgData_879_, v___x_887_, v___x_888_, v___y_882_, v___y_883_, v___y_884_, v___y_885_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v_ref_890_, lean_object* v_msgData_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12(v_ref_890_, v_msgData_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v_ref_890_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v___x_908_, lean_object* v_as_909_, size_t v_i_910_, size_t v_stop_911_, lean_object* v_b_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_a_921_; uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_eq(v_i_910_, v_stop_911_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v_name_927_; lean_object* v_stx_928_; uint8_t v___y_930_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_926_ = lean_array_uget_borrowed(v_as_909_, v_i_910_);
v_name_927_ = lean_ctor_get(v___x_926_, 0);
v_stx_928_ = lean_ctor_get(v___x_926_, 1);
v___x_940_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__3));
v___x_941_ = lean_name_eq(v_name_927_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__5));
v___x_943_ = lean_name_eq(v_name_927_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
v___x_944_ = lean_box(0);
v_a_921_ = v___x_944_;
goto v___jp_920_;
}
else
{
v___y_930_ = v___x_943_;
goto v___jp_929_;
}
}
else
{
lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_945_ = lean_unsigned_to_nat(0u);
v___x_946_ = lean_nat_dec_lt(v___x_945_, v___x_908_);
v___y_930_ = v___x_946_;
goto v___jp_929_;
}
v___jp_929_:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_931_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__0));
lean_inc(v_name_927_);
v___x_932_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_927_, v___y_930_);
v___x_933_ = lean_string_append(v___x_931_, v___x_932_);
lean_dec_ref(v___x_932_);
v___x_934_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__1));
v___x_935_ = lean_string_append(v___x_933_, v___x_934_);
v___x_936_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
v___x_937_ = l_Lean_MessageData_ofFormat(v___x_936_);
v___x_938_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12(v_stx_928_, v___x_937_, v___y_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
if (lean_obj_tag(v___x_938_) == 0)
{
lean_object* v_a_939_; 
v_a_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc(v_a_939_);
lean_dec_ref_known(v___x_938_, 1);
v_a_921_ = v_a_939_;
goto v___jp_920_;
}
else
{
return v___x_938_;
}
}
}
else
{
lean_object* v___x_947_; 
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_b_912_);
return v___x_947_;
}
v___jp_920_:
{
size_t v___x_922_; size_t v___x_923_; 
v___x_922_ = ((size_t)1ULL);
v___x_923_ = lean_usize_add(v_i_910_, v___x_922_);
v_i_910_ = v___x_923_;
v_b_912_ = v_a_921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v___x_948_, lean_object* v_as_949_, lean_object* v_i_950_, lean_object* v_stop_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
size_t v_i_boxed_960_; size_t v_stop_boxed_961_; lean_object* v_res_962_; 
v_i_boxed_960_ = lean_unbox_usize(v_i_950_);
lean_dec(v_i_950_);
v_stop_boxed_961_ = lean_unbox_usize(v_stop_951_);
lean_dec(v_stop_951_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_948_, v_as_949_, v_i_boxed_960_, v_stop_boxed_961_, v_b_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec_ref(v___y_957_);
lean_dec(v___y_956_);
lean_dec_ref(v___y_955_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v_as_949_);
lean_dec(v___x_948_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v___x_963_, lean_object* v_as_964_, size_t v_i_965_, size_t v_stop_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_a_976_; uint8_t v___x_980_; 
v___x_980_ = lean_usize_dec_eq(v_i_965_, v_stop_966_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; lean_object* v_modifiers_982_; lean_object* v_attrs_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_981_ = lean_array_uget_borrowed(v_as_964_, v_i_965_);
v_modifiers_982_ = lean_ctor_get(v___x_981_, 2);
v_attrs_983_ = lean_ctor_get(v_modifiers_982_, 2);
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_array_get_size(v_attrs_983_);
v___x_986_ = lean_box(0);
v___x_987_ = lean_nat_dec_lt(v___x_984_, v___x_985_);
if (v___x_987_ == 0)
{
v_a_976_ = v___x_986_;
goto v___jp_975_;
}
else
{
size_t v___x_988_; size_t v___x_989_; lean_object* v___x_990_; 
v___x_988_ = ((size_t)0ULL);
v___x_989_ = lean_usize_of_nat(v___x_985_);
v___x_990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_963_, v_attrs_983_, v___x_988_, v___x_989_, v___x_986_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v_a_976_ = v_a_991_;
goto v___jp_975_;
}
else
{
return v___x_990_;
}
}
}
else
{
lean_object* v___x_992_; 
v___x_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_992_, 0, v_b_967_);
return v___x_992_;
}
v___jp_975_:
{
size_t v___x_977_; size_t v___x_978_; 
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_add(v_i_965_, v___x_977_);
v_i_965_ = v___x_978_;
v_b_967_ = v_a_976_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v___x_993_, lean_object* v_as_994_, lean_object* v_i_995_, lean_object* v_stop_996_, lean_object* v_b_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
size_t v_i_boxed_1005_; size_t v_stop_boxed_1006_; lean_object* v_res_1007_; 
v_i_boxed_1005_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_stop_boxed_1006_ = lean_unbox_usize(v_stop_996_);
lean_dec(v_stop_996_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14(v___x_993_, v_as_994_, v_i_boxed_1005_, v_stop_boxed_1006_, v_b_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_);
lean_dec(v___y_1003_);
lean_dec_ref(v___y_1002_);
lean_dec(v___y_1001_);
lean_dec_ref(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec_ref(v_as_994_);
lean_dec(v___x_993_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t v_sz_1008_, size_t v_i_1009_, lean_object* v_bs_1010_){
_start:
{
uint8_t v___x_1011_; 
v___x_1011_ = lean_usize_dec_lt(v_i_1009_, v_sz_1008_);
if (v___x_1011_ == 0)
{
return v_bs_1010_;
}
else
{
lean_object* v_v_1012_; lean_object* v_termination_1013_; lean_object* v_decreasingBy_x3f_1014_; lean_object* v___x_1015_; lean_object* v_bs_x27_1016_; size_t v___x_1017_; size_t v___x_1018_; lean_object* v___x_1019_; 
v_v_1012_ = lean_array_uget_borrowed(v_bs_1010_, v_i_1009_);
v_termination_1013_ = lean_ctor_get(v_v_1012_, 8);
v_decreasingBy_x3f_1014_ = lean_ctor_get(v_termination_1013_, 4);
lean_inc(v_decreasingBy_x3f_1014_);
v___x_1015_ = lean_unsigned_to_nat(0u);
v_bs_x27_1016_ = lean_array_uset(v_bs_1010_, v_i_1009_, v___x_1015_);
v___x_1017_ = ((size_t)1ULL);
v___x_1018_ = lean_usize_add(v_i_1009_, v___x_1017_);
v___x_1019_ = lean_array_uset(v_bs_x27_1016_, v_i_1009_, v_decreasingBy_x3f_1014_);
v_i_1009_ = v___x_1018_;
v_bs_1010_ = v___x_1019_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_sz_1021_, lean_object* v_i_1022_, lean_object* v_bs_1023_){
_start:
{
size_t v_sz_boxed_1024_; size_t v_i_boxed_1025_; lean_object* v_res_1026_; 
v_sz_boxed_1024_ = lean_unbox_usize(v_sz_1021_);
lean_dec(v_sz_1021_);
v_i_boxed_1025_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_res_1026_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_1024_, v_i_boxed_1025_, v_bs_1023_);
return v_res_1026_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0);
v___x_1028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg();
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0);
v___x_1034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
lean_ctor_set(v___x_1034_, 2, v___x_1032_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1035_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
v___x_1036_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0);
v___x_1037_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
v___x_1038_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___x_1036_);
lean_ctor_set(v___x_1038_, 2, v___x_1036_);
lean_ctor_set(v___x_1038_, 3, v___x_1036_);
lean_ctor_set(v___x_1038_, 4, v___x_1036_);
lean_ctor_set(v___x_1038_, 5, v___x_1036_);
lean_ctor_set(v___x_1038_, 6, v___x_1036_);
lean_ctor_set(v___x_1038_, 7, v___x_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(lean_object* v_env_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v___x_1043_; lean_object* v_nextMacroScope_1044_; lean_object* v_ngen_1045_; lean_object* v_auxDeclNGen_1046_; lean_object* v_traceState_1047_; lean_object* v_recordedDeps_1048_; lean_object* v_messages_1049_; lean_object* v_infoState_1050_; lean_object* v_snapshotTasks_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1077_; 
v___x_1043_ = lean_st_ref_take(v___y_1041_);
v_nextMacroScope_1044_ = lean_ctor_get(v___x_1043_, 1);
v_ngen_1045_ = lean_ctor_get(v___x_1043_, 2);
v_auxDeclNGen_1046_ = lean_ctor_get(v___x_1043_, 3);
v_traceState_1047_ = lean_ctor_get(v___x_1043_, 4);
v_recordedDeps_1048_ = lean_ctor_get(v___x_1043_, 6);
v_messages_1049_ = lean_ctor_get(v___x_1043_, 7);
v_infoState_1050_ = lean_ctor_get(v___x_1043_, 8);
v_snapshotTasks_1051_ = lean_ctor_get(v___x_1043_, 9);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1077_ == 0)
{
lean_object* v_unused_1078_; lean_object* v_unused_1079_; 
v_unused_1078_ = lean_ctor_get(v___x_1043_, 5);
lean_dec(v_unused_1078_);
v_unused_1079_ = lean_ctor_get(v___x_1043_, 0);
lean_dec(v_unused_1079_);
v___x_1053_ = v___x_1043_;
v_isShared_1054_ = v_isSharedCheck_1077_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_snapshotTasks_1051_);
lean_inc(v_infoState_1050_);
lean_inc(v_messages_1049_);
lean_inc(v_recordedDeps_1048_);
lean_inc(v_traceState_1047_);
lean_inc(v_auxDeclNGen_1046_);
lean_inc(v_ngen_1045_);
lean_inc(v_nextMacroScope_1044_);
lean_dec(v___x_1043_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1077_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 5, v___x_1055_);
lean_ctor_set(v___x_1053_, 0, v_env_1039_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_env_1039_);
lean_ctor_set(v_reuseFailAlloc_1076_, 1, v_nextMacroScope_1044_);
lean_ctor_set(v_reuseFailAlloc_1076_, 2, v_ngen_1045_);
lean_ctor_set(v_reuseFailAlloc_1076_, 3, v_auxDeclNGen_1046_);
lean_ctor_set(v_reuseFailAlloc_1076_, 4, v_traceState_1047_);
lean_ctor_set(v_reuseFailAlloc_1076_, 5, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1076_, 6, v_recordedDeps_1048_);
lean_ctor_set(v_reuseFailAlloc_1076_, 7, v_messages_1049_);
lean_ctor_set(v_reuseFailAlloc_1076_, 8, v_infoState_1050_);
lean_ctor_set(v_reuseFailAlloc_1076_, 9, v_snapshotTasks_1051_);
v___x_1057_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v_mctx_1060_; lean_object* v_zetaDeltaFVarIds_1061_; lean_object* v_postponed_1062_; lean_object* v_diag_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1074_; 
v___x_1058_ = lean_st_ref_put(v___y_1041_, v___x_1057_);
v___x_1059_ = lean_st_ref_take(v___y_1040_);
v_mctx_1060_ = lean_ctor_get(v___x_1059_, 0);
v_zetaDeltaFVarIds_1061_ = lean_ctor_get(v___x_1059_, 2);
v_postponed_1062_ = lean_ctor_get(v___x_1059_, 3);
v_diag_1063_ = lean_ctor_get(v___x_1059_, 4);
v_isSharedCheck_1074_ = !lean_is_exclusive(v___x_1059_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; 
v_unused_1075_ = lean_ctor_get(v___x_1059_, 1);
lean_dec(v_unused_1075_);
v___x_1065_ = v___x_1059_;
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_diag_1063_);
lean_inc(v_postponed_1062_);
lean_inc(v_zetaDeltaFVarIds_1061_);
lean_inc(v_mctx_1060_);
lean_dec(v___x_1059_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1074_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1070_; 
v___x_1067_ = lean_box(0);
v___x_1068_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 1, v___x_1068_);
v___x_1070_ = v___x_1065_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_mctx_1060_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_zetaDeltaFVarIds_1061_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_postponed_1062_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v_diag_1063_);
v___x_1070_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_st_ref_put(v___y_1040_, v___x_1070_);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1067_);
return v___x_1072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object* v_env_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec(v___y_1081_);
return v_res_1084_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1087_ = l_Lean_stringToMessageData(v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object* v_snd_1088_, size_t v_sz_1089_, size_t v___x_1090_, lean_object* v_a_1091_, lean_object* v_fst_1092_, lean_object* v_fixedArgs_1093_, lean_object* v_fst_1094_, lean_object* v___x_1095_, lean_object* v___x_1096_, lean_object* v___x_1097_, lean_object* v_wfRel_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v___y_1107_; lean_object* v___y_1108_; lean_object* v___y_1109_; lean_object* v___y_1110_; lean_object* v___y_1111_; lean_object* v___y_1112_; lean_object* v___y_1113_; lean_object* v_a_1114_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v_toCold_1245_; lean_object* v_options_1246_; uint8_t v_hasTrace_1247_; 
v_toCold_1245_ = lean_ctor_get(v___y_1103_, 0);
v_options_1246_ = lean_ctor_get(v_toCold_1245_, 2);
v_hasTrace_1247_ = lean_ctor_get_uint8(v_options_1246_, sizeof(void*)*1);
if (v_hasTrace_1247_ == 0)
{
lean_dec(v___x_1097_);
v___y_1216_ = v___y_1099_;
v___y_1217_ = v___y_1100_;
v___y_1218_ = v___y_1101_;
v___y_1219_ = v___y_1102_;
v___y_1220_ = v___y_1103_;
v___y_1221_ = v___y_1104_;
goto v___jp_1215_;
}
else
{
lean_object* v_inheritedTraceOptions_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; uint8_t v___x_1251_; 
v_inheritedTraceOptions_1248_ = lean_ctor_get(v_toCold_1245_, 11);
v___x_1249_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__1));
lean_inc(v___x_1097_);
v___x_1250_ = l_Lean_Name_append(v___x_1249_, v___x_1097_);
v___x_1251_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1248_, v_options_1246_, v___x_1250_);
lean_dec(v___x_1250_);
if (v___x_1251_ == 0)
{
lean_dec(v___x_1097_);
v___y_1216_ = v___y_1099_;
v___y_1217_ = v___y_1100_;
v___y_1218_ = v___y_1101_;
v___y_1219_ = v___y_1102_;
v___y_1220_ = v___y_1103_;
v___y_1221_ = v___y_1104_;
goto v___jp_1215_;
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1252_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
lean_inc_ref(v_wfRel_1098_);
v___x_1253_ = l_Lean_MessageData_ofExpr(v_wfRel_1098_);
v___x_1254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1252_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v___x_1097_, v___x_1254_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1255_) == 0)
{
lean_dec_ref_known(v___x_1255_, 1);
v___y_1216_ = v___y_1099_;
v___y_1217_ = v___y_1100_;
v___y_1218_ = v___y_1101_;
v___y_1219_ = v___y_1102_;
v___y_1220_ = v___y_1103_;
v___y_1221_ = v___y_1104_;
goto v___jp_1215_;
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
lean_dec_ref(v_wfRel_1098_);
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_fst_1094_);
lean_dec_ref(v_fixedArgs_1093_);
lean_dec_ref(v_fst_1092_);
lean_dec_ref(v_a_1091_);
lean_dec_ref(v_snd_1088_);
v_a_1256_ = lean_ctor_get(v___x_1255_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1255_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1255_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1255_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
v___jp_1106_:
{
lean_object* v___x_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1122_; 
v___x_1115_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1112_, v___y_1110_, v___y_1113_);
v_isSharedCheck_1122_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1122_ == 0)
{
lean_object* v_unused_1123_; 
v_unused_1123_ = lean_ctor_get(v___x_1115_, 0);
lean_dec(v_unused_1123_);
v___x_1117_ = v___x_1115_;
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
else
{
lean_dec(v___x_1115_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1122_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v___x_1120_; 
if (v_isShared_1118_ == 0)
{
lean_ctor_set_tag(v___x_1117_, 1);
lean_ctor_set(v___x_1117_, 0, v_a_1114_);
v___x_1120_ = v___x_1117_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1114_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
v___jp_1124_:
{
lean_object* v___x_1131_; lean_object* v_env_1132_; lean_object* v___x_1133_; 
v___x_1131_ = lean_st_ref_get(v___y_1130_);
v_env_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc_ref(v_env_1132_);
lean_dec(v___x_1131_);
v___x_1133_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1088_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec_ref_known(v___x_1133_, 1);
v___x_1134_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1089_, v___x_1090_, v_a_1091_);
lean_inc_ref(v_fst_1092_);
v___x_1135_ = l_Lean_Elab_WF_mkFix(v_fst_1092_, v_fixedArgs_1093_, v_fst_1094_, v_wfRel_1098_, v___x_1095_, v___x_1134_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; lean_object* v___x_1137_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
v___x_1137_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1136_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; lean_object* v_env_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = lean_st_ref_get(v___y_1130_);
v_env_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc_ref_n(v_env_1140_, 2);
lean_dec(v___x_1139_);
v___x_1141_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1132_, v___y_1128_, v___y_1130_);
lean_dec_ref(v___x_1141_);
v___x_1142_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1140_, v_a_1138_, v___y_1129_, v___y_1130_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1203_; 
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1203_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1203_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; lean_object* v_env_1148_; lean_object* v_nextMacroScope_1149_; lean_object* v_ngen_1150_; lean_object* v_auxDeclNGen_1151_; lean_object* v_traceState_1152_; lean_object* v_recordedDeps_1153_; lean_object* v_messages_1154_; lean_object* v_infoState_1155_; lean_object* v_snapshotTasks_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1201_; 
v___x_1147_ = lean_st_ref_take(v___y_1130_);
v_env_1148_ = lean_ctor_get(v___x_1147_, 0);
v_nextMacroScope_1149_ = lean_ctor_get(v___x_1147_, 1);
v_ngen_1150_ = lean_ctor_get(v___x_1147_, 2);
v_auxDeclNGen_1151_ = lean_ctor_get(v___x_1147_, 3);
v_traceState_1152_ = lean_ctor_get(v___x_1147_, 4);
v_recordedDeps_1153_ = lean_ctor_get(v___x_1147_, 6);
v_messages_1154_ = lean_ctor_get(v___x_1147_, 7);
v_infoState_1155_ = lean_ctor_get(v___x_1147_, 8);
v_snapshotTasks_1156_ = lean_ctor_get(v___x_1147_, 9);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1147_, 5);
lean_dec(v_unused_1202_);
v___x_1158_ = v___x_1147_;
v_isShared_1159_ = v_isSharedCheck_1201_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_snapshotTasks_1156_);
lean_inc(v_infoState_1155_);
lean_inc(v_messages_1154_);
lean_inc(v_recordedDeps_1153_);
lean_inc(v_traceState_1152_);
lean_inc(v_auxDeclNGen_1151_);
lean_inc(v_ngen_1150_);
lean_inc(v_nextMacroScope_1149_);
lean_inc(v_env_1148_);
lean_dec(v___x_1147_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1201_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1160_ = l_Lean_copyExtraModUses(v_env_1140_, v_env_1148_);
v___x_1161_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 5, v___x_1161_);
lean_ctor_set(v___x_1158_, 0, v___x_1160_);
v___x_1163_ = v___x_1158_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_nextMacroScope_1149_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_ngen_1150_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_auxDeclNGen_1151_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_traceState_1152_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1200_, 6, v_recordedDeps_1153_);
lean_ctor_set(v_reuseFailAlloc_1200_, 7, v_messages_1154_);
lean_ctor_set(v_reuseFailAlloc_1200_, 8, v_infoState_1155_);
lean_ctor_set(v_reuseFailAlloc_1200_, 9, v_snapshotTasks_1156_);
v___x_1163_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v_mctx_1166_; lean_object* v_zetaDeltaFVarIds_1167_; lean_object* v_postponed_1168_; lean_object* v_diag_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1198_; 
v___x_1164_ = lean_st_ref_put(v___y_1130_, v___x_1163_);
v___x_1165_ = lean_st_ref_take(v___y_1128_);
v_mctx_1166_ = lean_ctor_get(v___x_1165_, 0);
v_zetaDeltaFVarIds_1167_ = lean_ctor_get(v___x_1165_, 2);
v_postponed_1168_ = lean_ctor_get(v___x_1165_, 3);
v_diag_1169_ = lean_ctor_get(v___x_1165_, 4);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v___x_1165_, 1);
lean_dec(v_unused_1199_);
v___x_1171_ = v___x_1165_;
v_isShared_1172_ = v_isSharedCheck_1198_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_diag_1169_);
lean_inc(v_postponed_1168_);
lean_inc(v_zetaDeltaFVarIds_1167_);
lean_inc(v_mctx_1166_);
lean_dec(v___x_1165_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1198_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v___x_1175_; 
v___x_1173_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 1, v___x_1173_);
v___x_1175_ = v___x_1171_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_mctx_1166_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_zetaDeltaFVarIds_1167_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_postponed_1168_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_diag_1169_);
v___x_1175_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; lean_object* v_ref_1177_; uint8_t v_kind_1178_; lean_object* v_levelParams_1179_; lean_object* v_modifiers_1180_; lean_object* v_declName_1181_; lean_object* v_binders_1182_; lean_object* v_numSectionVars_1183_; lean_object* v_type_1184_; lean_object* v_termination_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1195_; 
v___x_1176_ = lean_st_ref_put(v___y_1128_, v___x_1175_);
v_ref_1177_ = lean_ctor_get(v_fst_1092_, 0);
v_kind_1178_ = lean_ctor_get_uint8(v_fst_1092_, sizeof(void*)*9);
v_levelParams_1179_ = lean_ctor_get(v_fst_1092_, 1);
v_modifiers_1180_ = lean_ctor_get(v_fst_1092_, 2);
v_declName_1181_ = lean_ctor_get(v_fst_1092_, 3);
v_binders_1182_ = lean_ctor_get(v_fst_1092_, 4);
v_numSectionVars_1183_ = lean_ctor_get(v_fst_1092_, 5);
v_type_1184_ = lean_ctor_get(v_fst_1092_, 6);
v_termination_1185_ = lean_ctor_get(v_fst_1092_, 8);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_fst_1092_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_fst_1092_, 7);
lean_dec(v_unused_1196_);
v___x_1187_ = v_fst_1092_;
v_isShared_1188_ = v_isSharedCheck_1195_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_termination_1185_);
lean_inc(v_type_1184_);
lean_inc(v_numSectionVars_1183_);
lean_inc(v_binders_1182_);
lean_inc(v_declName_1181_);
lean_inc(v_modifiers_1180_);
lean_inc(v_levelParams_1179_);
lean_inc(v_ref_1177_);
lean_dec(v_fst_1092_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1195_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1190_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 7, v_a_1143_);
v___x_1190_ = v___x_1187_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_ref_1177_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_levelParams_1179_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_modifiers_1180_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_declName_1181_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v_binders_1182_);
lean_ctor_set(v_reuseFailAlloc_1194_, 5, v_numSectionVars_1183_);
lean_ctor_set(v_reuseFailAlloc_1194_, 6, v_type_1184_);
lean_ctor_set(v_reuseFailAlloc_1194_, 7, v_a_1143_);
lean_ctor_set(v_reuseFailAlloc_1194_, 8, v_termination_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1194_, sizeof(void*)*9, v_kind_1178_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1190_);
v___x_1192_ = v___x_1145_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
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
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec_ref(v_env_1140_);
lean_dec_ref(v_fst_1092_);
v_a_1204_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1142_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1142_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; 
lean_dec_ref(v_fst_1092_);
v_a_1212_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1137_, 1);
v___y_1107_ = v___y_1127_;
v___y_1108_ = v___y_1125_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___y_1128_;
v___y_1111_ = v___y_1126_;
v___y_1112_ = v_env_1132_;
v___y_1113_ = v___y_1130_;
v_a_1114_ = v_a_1212_;
goto v___jp_1106_;
}
}
else
{
lean_object* v_a_1213_; 
lean_dec_ref(v_fst_1092_);
v_a_1213_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1135_, 1);
v___y_1107_ = v___y_1127_;
v___y_1108_ = v___y_1125_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___y_1128_;
v___y_1111_ = v___y_1126_;
v___y_1112_ = v_env_1132_;
v___y_1113_ = v___y_1130_;
v_a_1114_ = v_a_1213_;
goto v___jp_1106_;
}
}
else
{
lean_object* v_a_1214_; 
lean_dec_ref(v_wfRel_1098_);
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_fst_1094_);
lean_dec_ref(v_fixedArgs_1093_);
lean_dec_ref(v_fst_1092_);
lean_dec_ref(v_a_1091_);
v_a_1214_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1133_, 1);
v___y_1107_ = v___y_1127_;
v___y_1108_ = v___y_1125_;
v___y_1109_ = v___y_1129_;
v___y_1110_ = v___y_1128_;
v___y_1111_ = v___y_1126_;
v___y_1112_ = v_env_1132_;
v___y_1113_ = v___y_1130_;
v_a_1114_ = v_a_1214_;
goto v___jp_1106_;
}
}
v___jp_1215_:
{
lean_object* v___x_1222_; 
lean_inc_ref(v_wfRel_1098_);
v___x_1222_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1098_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1222_) == 0)
{
lean_object* v_a_1223_; 
v_a_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_a_1223_);
lean_dec_ref_known(v___x_1222_, 1);
if (lean_obj_tag(v_a_1223_) == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = lean_array_get_size(v_a_1091_);
v___x_1226_ = lean_nat_dec_lt(v___x_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
v___y_1125_ = v___y_1216_;
v___y_1126_ = v___y_1217_;
v___y_1127_ = v___y_1218_;
v___y_1128_ = v___y_1219_;
v___y_1129_ = v___y_1220_;
v___y_1130_ = v___y_1221_;
goto v___jp_1124_;
}
else
{
size_t v___x_1227_; lean_object* v___x_1228_; 
v___x_1227_ = lean_usize_of_nat(v___x_1225_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14(v___x_1225_, v_a_1091_, v___x_1090_, v___x_1227_, v___x_1096_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_dec_ref_known(v___x_1228_, 1);
v___y_1125_ = v___y_1216_;
v___y_1126_ = v___y_1217_;
v___y_1127_ = v___y_1218_;
v___y_1128_ = v___y_1219_;
v___y_1129_ = v___y_1220_;
v___y_1130_ = v___y_1221_;
goto v___jp_1124_;
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v_wfRel_1098_);
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_fst_1094_);
lean_dec_ref(v_fixedArgs_1093_);
lean_dec_ref(v_fst_1092_);
lean_dec_ref(v_a_1091_);
lean_dec_ref(v_snd_1088_);
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
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
}
else
{
lean_dec_ref_known(v_a_1223_, 1);
v___y_1125_ = v___y_1216_;
v___y_1126_ = v___y_1217_;
v___y_1127_ = v___y_1218_;
v___y_1128_ = v___y_1219_;
v___y_1129_ = v___y_1220_;
v___y_1130_ = v___y_1221_;
goto v___jp_1124_;
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec_ref(v_wfRel_1098_);
lean_dec_ref(v___x_1095_);
lean_dec_ref(v_fst_1094_);
lean_dec_ref(v_fixedArgs_1093_);
lean_dec_ref(v_fst_1092_);
lean_dec_ref(v_a_1091_);
lean_dec_ref(v_snd_1088_);
v_a_1237_ = lean_ctor_get(v___x_1222_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1222_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1222_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args){
lean_object* v_snd_1264_ = _args[0];
lean_object* v_sz_1265_ = _args[1];
lean_object* v___x_1266_ = _args[2];
lean_object* v_a_1267_ = _args[3];
lean_object* v_fst_1268_ = _args[4];
lean_object* v_fixedArgs_1269_ = _args[5];
lean_object* v_fst_1270_ = _args[6];
lean_object* v___x_1271_ = _args[7];
lean_object* v___x_1272_ = _args[8];
lean_object* v___x_1273_ = _args[9];
lean_object* v_wfRel_1274_ = _args[10];
lean_object* v___y_1275_ = _args[11];
lean_object* v___y_1276_ = _args[12];
lean_object* v___y_1277_ = _args[13];
lean_object* v___y_1278_ = _args[14];
lean_object* v___y_1279_ = _args[15];
lean_object* v___y_1280_ = _args[16];
lean_object* v___y_1281_ = _args[17];
_start:
{
size_t v_sz_boxed_1282_; size_t v___x_45919__boxed_1283_; lean_object* v_res_1284_; 
v_sz_boxed_1282_ = lean_unbox_usize(v_sz_1265_);
lean_dec(v_sz_1265_);
v___x_45919__boxed_1283_ = lean_unbox_usize(v___x_1266_);
lean_dec(v___x_1266_);
v_res_1284_ = l_Lean_Elab_wfRecursion___lam__3(v_snd_1264_, v_sz_boxed_1282_, v___x_45919__boxed_1283_, v_a_1267_, v_fst_1268_, v_fixedArgs_1269_, v_fst_1270_, v___x_1271_, v___x_1272_, v___x_1273_, v_wfRel_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
return v_res_1284_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__4___closed__0));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t v_sz_1288_, size_t v___x_1289_, lean_object* v_a_1290_, lean_object* v_snd_1291_, lean_object* v_fst_1292_, lean_object* v_fst_1293_, lean_object* v___x_1294_, lean_object* v___x_1295_, lean_object* v_declName_1296_, lean_object* v_fst_1297_, lean_object* v_wf_1298_, lean_object* v_fixedArgs_1299_, lean_object* v_type_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_Meta_whnfForall(v_type_1300_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; uint8_t v___x_1323_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v___x_1323_ = l_Lean_Expr_isForall(v_a_1309_);
if (v___x_1323_ == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_dec_ref(v_fixedArgs_1299_);
lean_dec_ref(v_wf_1298_);
lean_dec_ref(v_fst_1297_);
lean_dec(v_declName_1296_);
lean_dec(v___x_1295_);
lean_dec_ref(v_fst_1293_);
lean_dec_ref(v_fst_1292_);
lean_dec_ref(v_snd_1291_);
lean_dec_ref(v_a_1290_);
v___x_1324_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__4___closed__1, &l_Lean_Elab_wfRecursion___lam__4___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__4___closed__1);
v___x_1325_ = l_Lean_MessageData_ofExpr(v_a_1309_);
v___x_1326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1324_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1326_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
v_a_1328_ = lean_ctor_get(v___x_1327_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1327_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1327_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
v___y_1311_ = v___y_1301_;
v___y_1312_ = v___y_1302_;
v___y_1313_ = v___y_1303_;
v___y_1314_ = v___y_1304_;
v___y_1315_ = v___y_1305_;
v___y_1316_ = v___y_1306_;
goto v___jp_1310_;
}
v___jp_1310_:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___f_1321_; lean_object* v___x_1322_; 
v___x_1317_ = l_Lean_Expr_bindingDomain_x21(v_a_1309_);
lean_dec(v_a_1309_);
lean_inc_ref(v_a_1290_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_1288_, v___x_1289_, v_a_1290_);
v___x_1319_ = lean_box_usize(v_sz_1288_);
v___x_1320_ = lean_box_usize(v___x_1289_);
lean_inc_ref(v___x_1318_);
lean_inc_ref(v_fst_1293_);
lean_inc_ref(v_fixedArgs_1299_);
v___f_1321_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 18, 10);
lean_closure_set(v___f_1321_, 0, v_snd_1291_);
lean_closure_set(v___f_1321_, 1, v___x_1319_);
lean_closure_set(v___f_1321_, 2, v___x_1320_);
lean_closure_set(v___f_1321_, 3, v_a_1290_);
lean_closure_set(v___f_1321_, 4, v_fst_1292_);
lean_closure_set(v___f_1321_, 5, v_fixedArgs_1299_);
lean_closure_set(v___f_1321_, 6, v_fst_1293_);
lean_closure_set(v___f_1321_, 7, v___x_1318_);
lean_closure_set(v___f_1321_, 8, v___x_1294_);
lean_closure_set(v___f_1321_, 9, v___x_1295_);
v___x_1322_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1318_, v_declName_1296_, v_fst_1297_, v_fixedArgs_1299_, v_fst_1293_, v___x_1317_, v_wf_1298_, v___f_1321_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1322_;
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v_fixedArgs_1299_);
lean_dec_ref(v_wf_1298_);
lean_dec_ref(v_fst_1297_);
lean_dec(v_declName_1296_);
lean_dec(v___x_1295_);
lean_dec_ref(v_fst_1293_);
lean_dec_ref(v_fst_1292_);
lean_dec_ref(v_snd_1291_);
lean_dec_ref(v_a_1290_);
v_a_1336_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1308_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1308_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object** _args){
lean_object* v_sz_1344_ = _args[0];
lean_object* v___x_1345_ = _args[1];
lean_object* v_a_1346_ = _args[2];
lean_object* v_snd_1347_ = _args[3];
lean_object* v_fst_1348_ = _args[4];
lean_object* v_fst_1349_ = _args[5];
lean_object* v___x_1350_ = _args[6];
lean_object* v___x_1351_ = _args[7];
lean_object* v_declName_1352_ = _args[8];
lean_object* v_fst_1353_ = _args[9];
lean_object* v_wf_1354_ = _args[10];
lean_object* v_fixedArgs_1355_ = _args[11];
lean_object* v_type_1356_ = _args[12];
lean_object* v___y_1357_ = _args[13];
lean_object* v___y_1358_ = _args[14];
lean_object* v___y_1359_ = _args[15];
lean_object* v___y_1360_ = _args[16];
lean_object* v___y_1361_ = _args[17];
lean_object* v___y_1362_ = _args[18];
lean_object* v___y_1363_ = _args[19];
_start:
{
size_t v_sz_boxed_1364_; size_t v___x_46240__boxed_1365_; lean_object* v_res_1366_; 
v_sz_boxed_1364_ = lean_unbox_usize(v_sz_1344_);
lean_dec(v_sz_1344_);
v___x_46240__boxed_1365_ = lean_unbox_usize(v___x_1345_);
lean_dec(v___x_1345_);
v_res_1366_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_boxed_1364_, v___x_46240__boxed_1365_, v_a_1346_, v_snd_1347_, v_fst_1348_, v_fst_1349_, v___x_1350_, v___x_1351_, v_declName_1352_, v_fst_1353_, v_wf_1354_, v_fixedArgs_1355_, v_type_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object* v_a_1367_, lean_object* v_fst_1368_, lean_object* v_fst_1369_, lean_object* v_fst_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v___x_1378_; 
v___x_1378_ = l_Lean_Elab_WF_guessLex(v_a_1367_, v_fst_1368_, v_fst_1369_, v_fst_1370_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object* v_a_1379_, lean_object* v_fst_1380_, lean_object* v_fst_1381_, lean_object* v_fst_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1379_, v_fst_1380_, v_fst_1381_, v_fst_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg___lam__0(lean_object* v___y_1391_, uint8_t v_isExporting_1392_, lean_object* v___x_1393_, lean_object* v___y_1394_, lean_object* v___x_1395_, lean_object* v_a_x3f_1396_){
_start:
{
lean_object* v___x_1398_; lean_object* v_env_1399_; lean_object* v_nextMacroScope_1400_; lean_object* v_ngen_1401_; lean_object* v_auxDeclNGen_1402_; lean_object* v_traceState_1403_; lean_object* v_recordedDeps_1404_; lean_object* v_messages_1405_; lean_object* v_infoState_1406_; lean_object* v_snapshotTasks_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1432_; 
v___x_1398_ = lean_st_ref_take(v___y_1391_);
v_env_1399_ = lean_ctor_get(v___x_1398_, 0);
v_nextMacroScope_1400_ = lean_ctor_get(v___x_1398_, 1);
v_ngen_1401_ = lean_ctor_get(v___x_1398_, 2);
v_auxDeclNGen_1402_ = lean_ctor_get(v___x_1398_, 3);
v_traceState_1403_ = lean_ctor_get(v___x_1398_, 4);
v_recordedDeps_1404_ = lean_ctor_get(v___x_1398_, 6);
v_messages_1405_ = lean_ctor_get(v___x_1398_, 7);
v_infoState_1406_ = lean_ctor_get(v___x_1398_, 8);
v_snapshotTasks_1407_ = lean_ctor_get(v___x_1398_, 9);
v_isSharedCheck_1432_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1432_ == 0)
{
lean_object* v_unused_1433_; 
v_unused_1433_ = lean_ctor_get(v___x_1398_, 5);
lean_dec(v_unused_1433_);
v___x_1409_ = v___x_1398_;
v_isShared_1410_ = v_isSharedCheck_1432_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_snapshotTasks_1407_);
lean_inc(v_infoState_1406_);
lean_inc(v_messages_1405_);
lean_inc(v_recordedDeps_1404_);
lean_inc(v_traceState_1403_);
lean_inc(v_auxDeclNGen_1402_);
lean_inc(v_ngen_1401_);
lean_inc(v_nextMacroScope_1400_);
lean_inc(v_env_1399_);
lean_dec(v___x_1398_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1432_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
v___x_1411_ = l_Lean_Environment_setExporting(v_env_1399_, v_isExporting_1392_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set(v___x_1409_, 5, v___x_1393_);
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1411_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_nextMacroScope_1400_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_ngen_1401_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_auxDeclNGen_1402_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_traceState_1403_);
lean_ctor_set(v_reuseFailAlloc_1431_, 5, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1431_, 6, v_recordedDeps_1404_);
lean_ctor_set(v_reuseFailAlloc_1431_, 7, v_messages_1405_);
lean_ctor_set(v_reuseFailAlloc_1431_, 8, v_infoState_1406_);
lean_ctor_set(v_reuseFailAlloc_1431_, 9, v_snapshotTasks_1407_);
v___x_1413_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_mctx_1416_; lean_object* v_zetaDeltaFVarIds_1417_; lean_object* v_postponed_1418_; lean_object* v_diag_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1429_; 
v___x_1414_ = lean_st_ref_put(v___y_1391_, v___x_1413_);
v___x_1415_ = lean_st_ref_take(v___y_1394_);
v_mctx_1416_ = lean_ctor_get(v___x_1415_, 0);
v_zetaDeltaFVarIds_1417_ = lean_ctor_get(v___x_1415_, 2);
v_postponed_1418_ = lean_ctor_get(v___x_1415_, 3);
v_diag_1419_ = lean_ctor_get(v___x_1415_, 4);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1415_, 1);
lean_dec(v_unused_1430_);
v___x_1421_ = v___x_1415_;
v_isShared_1422_ = v_isSharedCheck_1429_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_diag_1419_);
lean_inc(v_postponed_1418_);
lean_inc(v_zetaDeltaFVarIds_1417_);
lean_inc(v_mctx_1416_);
lean_dec(v___x_1415_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1429_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1425_; 
v___x_1423_ = lean_box(0);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v___x_1395_);
v___x_1425_ = v___x_1421_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_mctx_1416_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_zetaDeltaFVarIds_1417_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_postponed_1418_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_diag_1419_);
v___x_1425_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = lean_st_ref_put(v___y_1394_, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1423_);
return v___x_1427_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg___lam__0___boxed(lean_object* v___y_1434_, lean_object* v_isExporting_1435_, lean_object* v___x_1436_, lean_object* v___y_1437_, lean_object* v___x_1438_, lean_object* v_a_x3f_1439_, lean_object* v___y_1440_){
_start:
{
uint8_t v_isExporting_boxed_1441_; lean_object* v_res_1442_; 
v_isExporting_boxed_1441_ = lean_unbox(v_isExporting_1435_);
v_res_1442_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg___lam__0(v___y_1434_, v_isExporting_boxed_1441_, v___x_1436_, v___y_1437_, v___x_1438_, v_a_x3f_1439_);
lean_dec(v_a_x3f_1439_);
lean_dec(v___y_1437_);
lean_dec(v___y_1434_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg(lean_object* v_x_1443_, uint8_t v_isExporting_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___x_1452_; lean_object* v_env_1453_; lean_object* v___x_1454_; uint8_t v_isModule_1455_; 
v___x_1452_ = lean_st_ref_get(v___y_1450_);
v_env_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc_ref(v_env_1453_);
lean_dec(v___x_1452_);
v___x_1454_ = l_Lean_Environment_header(v_env_1453_);
v_isModule_1455_ = lean_ctor_get_uint8(v___x_1454_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1454_);
if (v_isModule_1455_ == 0)
{
lean_object* v___x_1456_; 
lean_dec_ref(v_env_1453_);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
v___x_1456_ = lean_apply_7(v_x_1443_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1456_;
}
else
{
uint8_t v_isExporting_1457_; 
v_isExporting_1457_ = lean_ctor_get_uint8(v_env_1453_, sizeof(void*)*13);
lean_dec_ref(v_env_1453_);
if (v_isExporting_1444_ == 0)
{
if (v_isExporting_1457_ == 0)
{
lean_object* v___x_1524_; 
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
v___x_1524_ = lean_apply_7(v_x_1443_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1524_;
}
else
{
goto v___jp_1458_;
}
}
else
{
if (v_isExporting_1457_ == 0)
{
goto v___jp_1458_;
}
else
{
lean_object* v___x_1525_; 
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
v___x_1525_ = lean_apply_7(v_x_1443_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
return v___x_1525_;
}
}
v___jp_1458_:
{
lean_object* v___x_1459_; lean_object* v_env_1460_; lean_object* v_nextMacroScope_1461_; lean_object* v_ngen_1462_; lean_object* v_auxDeclNGen_1463_; lean_object* v_traceState_1464_; lean_object* v_recordedDeps_1465_; lean_object* v_messages_1466_; lean_object* v_infoState_1467_; lean_object* v_snapshotTasks_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1522_; 
v___x_1459_ = lean_st_ref_take(v___y_1450_);
v_env_1460_ = lean_ctor_get(v___x_1459_, 0);
v_nextMacroScope_1461_ = lean_ctor_get(v___x_1459_, 1);
v_ngen_1462_ = lean_ctor_get(v___x_1459_, 2);
v_auxDeclNGen_1463_ = lean_ctor_get(v___x_1459_, 3);
v_traceState_1464_ = lean_ctor_get(v___x_1459_, 4);
v_recordedDeps_1465_ = lean_ctor_get(v___x_1459_, 6);
v_messages_1466_ = lean_ctor_get(v___x_1459_, 7);
v_infoState_1467_ = lean_ctor_get(v___x_1459_, 8);
v_snapshotTasks_1468_ = lean_ctor_get(v___x_1459_, 9);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1459_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v___x_1459_, 5);
lean_dec(v_unused_1523_);
v___x_1470_ = v___x_1459_;
v_isShared_1471_ = v_isSharedCheck_1522_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_snapshotTasks_1468_);
lean_inc(v_infoState_1467_);
lean_inc(v_messages_1466_);
lean_inc(v_recordedDeps_1465_);
lean_inc(v_traceState_1464_);
lean_inc(v_auxDeclNGen_1463_);
lean_inc(v_ngen_1462_);
lean_inc(v_nextMacroScope_1461_);
lean_inc(v_env_1460_);
lean_dec(v___x_1459_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1522_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1475_; 
v___x_1472_ = l_Lean_Environment_setExporting(v_env_1460_, v_isExporting_1444_);
v___x_1473_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 5, v___x_1473_);
lean_ctor_set(v___x_1470_, 0, v___x_1472_);
v___x_1475_ = v___x_1470_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_nextMacroScope_1461_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_ngen_1462_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_auxDeclNGen_1463_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_traceState_1464_);
lean_ctor_set(v_reuseFailAlloc_1521_, 5, v___x_1473_);
lean_ctor_set(v_reuseFailAlloc_1521_, 6, v_recordedDeps_1465_);
lean_ctor_set(v_reuseFailAlloc_1521_, 7, v_messages_1466_);
lean_ctor_set(v_reuseFailAlloc_1521_, 8, v_infoState_1467_);
lean_ctor_set(v_reuseFailAlloc_1521_, 9, v_snapshotTasks_1468_);
v___x_1475_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v_mctx_1478_; lean_object* v_zetaDeltaFVarIds_1479_; lean_object* v_postponed_1480_; lean_object* v_diag_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1519_; 
v___x_1476_ = lean_st_ref_put(v___y_1450_, v___x_1475_);
v___x_1477_ = lean_st_ref_take(v___y_1448_);
v_mctx_1478_ = lean_ctor_get(v___x_1477_, 0);
v_zetaDeltaFVarIds_1479_ = lean_ctor_get(v___x_1477_, 2);
v_postponed_1480_ = lean_ctor_get(v___x_1477_, 3);
v_diag_1481_ = lean_ctor_get(v___x_1477_, 4);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1477_);
if (v_isSharedCheck_1519_ == 0)
{
lean_object* v_unused_1520_; 
v_unused_1520_ = lean_ctor_get(v___x_1477_, 1);
lean_dec(v_unused_1520_);
v___x_1483_ = v___x_1477_;
v_isShared_1484_ = v_isSharedCheck_1519_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_diag_1481_);
lean_inc(v_postponed_1480_);
lean_inc(v_zetaDeltaFVarIds_1479_);
lean_inc(v_mctx_1478_);
lean_dec(v___x_1477_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1519_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1485_; lean_object* v___x_1487_; 
v___x_1485_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__4);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 1, v___x_1485_);
v___x_1487_ = v___x_1483_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_mctx_1478_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1485_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_zetaDeltaFVarIds_1479_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_postponed_1480_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_diag_1481_);
v___x_1487_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
lean_object* v___x_1488_; lean_object* v_r_1489_; 
v___x_1488_ = lean_st_ref_put(v___y_1448_, v___x_1487_);
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
v_r_1489_ = lean_apply_7(v_x_1443_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, lean_box(0));
if (lean_obj_tag(v_r_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1506_; 
v_a_1490_ = lean_ctor_get(v_r_1489_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_r_1489_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1492_ = v_r_1489_;
v_isShared_1493_ = v_isSharedCheck_1506_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v_r_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1506_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
lean_inc(v_a_1490_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 1);
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1503_; 
v___x_1496_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg___lam__0(v___y_1450_, v_isExporting_1457_, v___x_1473_, v___y_1448_, v___x_1485_, v___x_1495_);
lean_dec_ref(v___x_1495_);
v_isSharedCheck_1503_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; 
v_unused_1504_ = lean_ctor_get(v___x_1496_, 0);
lean_dec(v_unused_1504_);
v___x_1498_ = v___x_1496_;
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
else
{
lean_dec(v___x_1496_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1503_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1501_; 
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 0, v_a_1490_);
v___x_1501_ = v___x_1498_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1490_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
else
{
lean_object* v_a_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1516_; 
v_a_1507_ = lean_ctor_get(v_r_1489_, 0);
lean_inc(v_a_1507_);
lean_dec_ref_known(v_r_1489_, 1);
v___x_1508_ = lean_box(0);
v___x_1509_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg___lam__0(v___y_1450_, v_isExporting_1457_, v___x_1473_, v___y_1448_, v___x_1485_, v___x_1508_);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v___x_1509_, 0);
lean_dec(v_unused_1517_);
v___x_1511_ = v___x_1509_;
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
else
{
lean_dec(v___x_1509_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1516_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1514_; 
if (v_isShared_1512_ == 0)
{
lean_ctor_set_tag(v___x_1511_, 1);
lean_ctor_set(v___x_1511_, 0, v_a_1507_);
v___x_1514_ = v___x_1511_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_a_1507_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
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
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg___boxed(lean_object* v_x_1526_, lean_object* v_isExporting_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
uint8_t v_isExporting_boxed_1535_; lean_object* v_res_1536_; 
v_isExporting_boxed_1535_ = lean_unbox(v_isExporting_1527_);
v_res_1536_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg(v_x_1526_, v_isExporting_boxed_1535_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg(lean_object* v_x_1537_, uint8_t v_when_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
if (v_when_1538_ == 0)
{
lean_object* v___x_1546_; 
lean_inc(v___y_1544_);
lean_inc_ref(v___y_1543_);
lean_inc(v___y_1542_);
lean_inc_ref(v___y_1541_);
lean_inc(v___y_1540_);
lean_inc_ref(v___y_1539_);
v___x_1546_ = lean_apply_7(v_x_1537_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, lean_box(0));
return v___x_1546_;
}
else
{
uint8_t v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = 0;
v___x_1548_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg(v_x_1537_, v___x_1547_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
return v___x_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg___boxed(lean_object* v_x_1549_, lean_object* v_when_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v_when_boxed_1558_; lean_object* v_res_1559_; 
v_when_boxed_1558_ = lean_unbox(v_when_1550_);
v_res_1559_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg(v_x_1549_, v_when_boxed_1558_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(lean_object* v_env_1560_, lean_object* v_x_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; lean_object* v_env_1570_; lean_object* v_a_1572_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1569_ = lean_st_ref_get(v___y_1567_);
v_env_1570_ = lean_ctor_get(v___x_1569_, 0);
lean_inc_ref(v_env_1570_);
lean_dec(v___x_1569_);
v___x_1582_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1560_, v___y_1565_, v___y_1567_);
lean_dec_ref(v___x_1582_);
lean_inc(v___y_1567_);
lean_inc_ref(v___y_1566_);
lean_inc(v___y_1565_);
lean_inc_ref(v___y_1564_);
lean_inc(v___y_1563_);
lean_inc_ref(v___y_1562_);
v___x_1583_ = lean_apply_7(v_x_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, lean_box(0));
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v___x_1583_, 1);
v___x_1585_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1570_, v___y_1565_, v___y_1567_);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v___x_1585_, 0);
lean_dec(v_unused_1593_);
v___x_1587_ = v___x_1585_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_dec(v___x_1585_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v_a_1584_);
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1584_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
else
{
lean_object* v_a_1594_; 
v_a_1594_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v___x_1583_, 1);
v_a_1572_ = v_a_1594_;
goto v___jp_1571_;
}
v___jp_1571_:
{
lean_object* v___x_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v___x_1573_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1570_, v___y_1565_, v___y_1567_);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1573_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v___x_1573_, 0);
lean_dec(v_unused_1581_);
v___x_1575_ = v___x_1573_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_dec(v___x_1573_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 1);
lean_ctor_set(v___x_1575_, 0, v_a_1572_);
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1572_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg___boxed(lean_object* v_env_1595_, lean_object* v_x_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_1595_, v_x_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v___x_1605_, lean_object* v_as_1606_, size_t v_sz_1607_, size_t v_i_1608_, lean_object* v_b_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v_a_1616_; uint8_t v___x_1620_; 
v___x_1620_ = lean_usize_dec_lt(v_i_1608_, v_sz_1607_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; 
lean_dec(v___x_1605_);
v___x_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1621_, 0, v_b_1609_);
return v___x_1621_;
}
else
{
lean_object* v_a_1622_; uint8_t v_kind_1623_; lean_object* v_declName_1624_; lean_object* v_type_1625_; lean_object* v___x_1626_; uint8_t v___x_1627_; 
v_a_1622_ = lean_array_uget_borrowed(v_as_1606_, v_i_1608_);
v_kind_1623_ = lean_ctor_get_uint8(v_a_1622_, sizeof(void*)*9);
v_declName_1624_ = lean_ctor_get(v_a_1622_, 3);
v_type_1625_ = lean_ctor_get(v_a_1622_, 6);
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_name_eq(v_declName_1624_, v___x_1605_);
if (v___x_1627_ == 0)
{
uint8_t v___x_1628_; 
v___x_1628_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1623_);
if (v___x_1628_ == 0)
{
lean_object* v___x_1629_; 
lean_inc_ref(v_type_1625_);
v___x_1629_ = l_Lean_Meta_isProp(v_type_1625_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; uint8_t v___x_1631_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v___x_1629_, 1);
v___x_1631_ = lean_unbox(v_a_1630_);
lean_dec(v_a_1630_);
if (v___x_1631_ == 0)
{
lean_object* v___x_1632_; 
lean_inc(v___x_1605_);
lean_inc(v_a_1622_);
v___x_1632_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1622_, v___x_1605_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_dec_ref_known(v___x_1632_, 1);
v_a_1616_ = v___x_1626_;
goto v___jp_1615_;
}
else
{
lean_dec(v___x_1605_);
return v___x_1632_;
}
}
else
{
v_a_1616_ = v___x_1626_;
goto v___jp_1615_;
}
}
else
{
lean_object* v_a_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1640_; 
lean_dec(v___x_1605_);
v_a_1633_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1635_ = v___x_1629_;
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_a_1633_);
lean_dec(v___x_1629_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1640_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1638_; 
if (v_isShared_1636_ == 0)
{
v___x_1638_ = v___x_1635_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_a_1633_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
else
{
v_a_1616_ = v___x_1626_;
goto v___jp_1615_;
}
}
else
{
v_a_1616_ = v___x_1626_;
goto v___jp_1615_;
}
}
v___jp_1615_:
{
size_t v___x_1617_; size_t v___x_1618_; 
v___x_1617_ = ((size_t)1ULL);
v___x_1618_ = lean_usize_add(v_i_1608_, v___x_1617_);
v_i_1608_ = v___x_1618_;
v_b_1609_ = v_a_1616_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v___x_1641_, lean_object* v_as_1642_, lean_object* v_sz_1643_, lean_object* v_i_1644_, lean_object* v_b_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
size_t v_sz_boxed_1651_; size_t v_i_boxed_1652_; lean_object* v_res_1653_; 
v_sz_boxed_1651_ = lean_unbox_usize(v_sz_1643_);
lean_dec(v_sz_1643_);
v_i_boxed_1652_ = lean_unbox_usize(v_i_1644_);
lean_dec(v_i_1644_);
v_res_1653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___x_1641_, v_as_1642_, v_sz_boxed_1651_, v_i_boxed_1652_, v_b_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec_ref(v_as_1642_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(size_t v_sz_1654_, size_t v_i_1655_, lean_object* v_bs_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_usize_dec_lt(v_i_1655_, v_sz_1654_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_bs_1656_);
return v___x_1661_;
}
else
{
lean_object* v_v_1662_; lean_object* v_ref_1663_; uint8_t v_kind_1664_; lean_object* v_levelParams_1665_; lean_object* v_modifiers_1666_; lean_object* v_declName_1667_; lean_object* v_binders_1668_; lean_object* v_numSectionVars_1669_; lean_object* v_type_1670_; lean_object* v_value_1671_; lean_object* v_termination_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1695_; 
v_v_1662_ = lean_array_uget(v_bs_1656_, v_i_1655_);
v_ref_1663_ = lean_ctor_get(v_v_1662_, 0);
v_kind_1664_ = lean_ctor_get_uint8(v_v_1662_, sizeof(void*)*9);
v_levelParams_1665_ = lean_ctor_get(v_v_1662_, 1);
v_modifiers_1666_ = lean_ctor_get(v_v_1662_, 2);
v_declName_1667_ = lean_ctor_get(v_v_1662_, 3);
v_binders_1668_ = lean_ctor_get(v_v_1662_, 4);
v_numSectionVars_1669_ = lean_ctor_get(v_v_1662_, 5);
v_type_1670_ = lean_ctor_get(v_v_1662_, 6);
v_value_1671_ = lean_ctor_get(v_v_1662_, 7);
v_termination_1672_ = lean_ctor_get(v_v_1662_, 8);
v_isSharedCheck_1695_ = !lean_is_exclusive(v_v_1662_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1674_ = v_v_1662_;
v_isShared_1675_ = v_isSharedCheck_1695_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_termination_1672_);
lean_inc(v_value_1671_);
lean_inc(v_type_1670_);
lean_inc(v_numSectionVars_1669_);
lean_inc(v_binders_1668_);
lean_inc(v_declName_1667_);
lean_inc(v_modifiers_1666_);
lean_inc(v_levelParams_1665_);
lean_inc(v_ref_1663_);
lean_dec(v_v_1662_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1695_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1676_; lean_object* v_bs_x27_1677_; lean_object* v___x_1678_; 
v___x_1676_ = lean_unsigned_to_nat(0u);
v_bs_x27_1677_ = lean_array_uset(v_bs_1656_, v_i_1655_, v___x_1676_);
v___x_1678_ = l_Lean_Elab_WF_floatRecApp(v_value_1671_, v___y_1657_, v___y_1658_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v___x_1681_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1678_, 1);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 7, v_a_1679_);
v___x_1681_ = v___x_1674_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_ref_1663_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_levelParams_1665_);
lean_ctor_set(v_reuseFailAlloc_1686_, 2, v_modifiers_1666_);
lean_ctor_set(v_reuseFailAlloc_1686_, 3, v_declName_1667_);
lean_ctor_set(v_reuseFailAlloc_1686_, 4, v_binders_1668_);
lean_ctor_set(v_reuseFailAlloc_1686_, 5, v_numSectionVars_1669_);
lean_ctor_set(v_reuseFailAlloc_1686_, 6, v_type_1670_);
lean_ctor_set(v_reuseFailAlloc_1686_, 7, v_a_1679_);
lean_ctor_set(v_reuseFailAlloc_1686_, 8, v_termination_1672_);
lean_ctor_set_uint8(v_reuseFailAlloc_1686_, sizeof(void*)*9, v_kind_1664_);
v___x_1681_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
size_t v___x_1682_; size_t v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_add(v_i_1655_, v___x_1682_);
v___x_1684_ = lean_array_uset(v_bs_x27_1677_, v_i_1655_, v___x_1681_);
v_i_1655_ = v___x_1683_;
v_bs_1656_ = v___x_1684_;
goto _start;
}
}
else
{
lean_object* v_a_1687_; lean_object* v___x_1689_; uint8_t v_isShared_1690_; uint8_t v_isSharedCheck_1694_; 
lean_dec_ref(v_bs_x27_1677_);
lean_del_object(v___x_1674_);
lean_dec_ref(v_termination_1672_);
lean_dec_ref(v_type_1670_);
lean_dec(v_numSectionVars_1669_);
lean_dec(v_binders_1668_);
lean_dec(v_declName_1667_);
lean_dec_ref(v_modifiers_1666_);
lean_dec(v_levelParams_1665_);
lean_dec(v_ref_1663_);
v_a_1687_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1694_ == 0)
{
v___x_1689_ = v___x_1678_;
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
else
{
lean_inc(v_a_1687_);
lean_dec(v___x_1678_);
v___x_1689_ = lean_box(0);
v_isShared_1690_ = v_isSharedCheck_1694_;
goto v_resetjp_1688_;
}
v_resetjp_1688_:
{
lean_object* v___x_1692_; 
if (v_isShared_1690_ == 0)
{
v___x_1692_ = v___x_1689_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_a_1687_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* v_sz_1696_, lean_object* v_i_1697_, lean_object* v_bs_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
size_t v_sz_boxed_1702_; size_t v_i_boxed_1703_; lean_object* v_res_1704_; 
v_sz_boxed_1702_ = lean_unbox_usize(v_sz_1696_);
lean_dec(v_sz_1696_);
v_i_boxed_1703_ = lean_unbox_usize(v_i_1697_);
lean_dec(v_i_1697_);
v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_boxed_1702_, v_i_boxed_1703_, v_bs_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_1705_, size_t v_i_1706_, lean_object* v_bs_1707_){
_start:
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_usize_dec_lt(v_i_1706_, v_sz_1705_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1709_, 0, v_bs_1707_);
return v___x_1709_;
}
else
{
lean_object* v_v_1710_; 
v_v_1710_ = lean_array_uget_borrowed(v_bs_1707_, v_i_1706_);
if (lean_obj_tag(v_v_1710_) == 0)
{
lean_object* v___x_1711_; 
lean_dec_ref(v_bs_1707_);
v___x_1711_ = lean_box(0);
return v___x_1711_;
}
else
{
lean_object* v_val_1712_; lean_object* v___x_1713_; lean_object* v_bs_x27_1714_; size_t v___x_1715_; size_t v___x_1716_; lean_object* v___x_1717_; 
v_val_1712_ = lean_ctor_get(v_v_1710_, 0);
lean_inc(v_val_1712_);
v___x_1713_ = lean_unsigned_to_nat(0u);
v_bs_x27_1714_ = lean_array_uset(v_bs_1707_, v_i_1706_, v___x_1713_);
v___x_1715_ = ((size_t)1ULL);
v___x_1716_ = lean_usize_add(v_i_1706_, v___x_1715_);
v___x_1717_ = lean_array_uset(v_bs_x27_1714_, v_i_1706_, v_val_1712_);
v_i_1706_ = v___x_1716_;
v_bs_1707_ = v___x_1717_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_1719_, lean_object* v_i_1720_, lean_object* v_bs_1721_){
_start:
{
size_t v_sz_boxed_1722_; size_t v_i_boxed_1723_; lean_object* v_res_1724_; 
v_sz_boxed_1722_ = lean_unbox_usize(v_sz_1719_);
lean_dec(v_sz_1719_);
v_i_boxed_1723_ = lean_unbox_usize(v_i_1720_);
lean_dec(v_i_1720_);
v_res_1724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_1722_, v_i_boxed_1723_, v_bs_1721_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg(size_t v_sz_1725_, size_t v_i_1726_, lean_object* v_bs_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = lean_usize_dec_lt(v_i_1726_, v_sz_1725_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_bs_1727_);
return v___x_1734_;
}
else
{
uint8_t v___x_1735_; lean_object* v_v_1736_; lean_object* v___x_1737_; lean_object* v_bs_x27_1738_; lean_object* v___x_1739_; 
v___x_1735_ = 0;
v_v_1736_ = lean_array_uget(v_bs_1727_, v_i_1726_);
v___x_1737_ = lean_unsigned_to_nat(0u);
v_bs_x27_1738_ = lean_array_uset(v_bs_1727_, v_i_1726_, v___x_1737_);
v___x_1739_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1736_, v___x_1735_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
if (lean_obj_tag(v___x_1739_) == 0)
{
lean_object* v_a_1740_; size_t v___x_1741_; size_t v___x_1742_; lean_object* v___x_1743_; 
v_a_1740_ = lean_ctor_get(v___x_1739_, 0);
lean_inc(v_a_1740_);
lean_dec_ref_known(v___x_1739_, 1);
v___x_1741_ = ((size_t)1ULL);
v___x_1742_ = lean_usize_add(v_i_1726_, v___x_1741_);
v___x_1743_ = lean_array_uset(v_bs_x27_1738_, v_i_1726_, v_a_1740_);
v_i_1726_ = v___x_1742_;
v_bs_1727_ = v___x_1743_;
goto _start;
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec_ref(v_bs_x27_1738_);
v_a_1745_ = lean_ctor_get(v___x_1739_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1739_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1739_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1739_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v_sz_1753_, lean_object* v_i_1754_, lean_object* v_bs_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
size_t v_sz_boxed_1761_; size_t v_i_boxed_1762_; lean_object* v_res_1763_; 
v_sz_boxed_1761_ = lean_unbox_usize(v_sz_1753_);
lean_dec(v_sz_1753_);
v_i_boxed_1762_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg(v_sz_boxed_1761_, v_i_boxed_1762_, v_bs_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
lean_dec(v___y_1759_);
lean_dec_ref(v___y_1758_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
return v_res_1763_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1775_ = l_Lean_stringToMessageData(v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1777_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1778_ = l_Lean_stringToMessageData(v___x_1777_);
return v___x_1778_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1780_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1781_ = l_Lean_stringToMessageData(v___x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1784_, lean_object* v_preDefs_1785_, lean_object* v_termMeasure_x3fs_1786_, lean_object* v_a_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___x_1794_; size_t v_sz_1795_; size_t v___x_1796_; lean_object* v_termMeasures_x3f_1797_; size_t v_sz_1798_; lean_object* v___x_1799_; 
v___x_1794_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_sz_1795_ = lean_array_size(v_termMeasure_x3fs_1786_);
v___x_1796_ = ((size_t)0ULL);
v_termMeasures_x3f_1797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_1795_, v___x_1796_, v_termMeasure_x3fs_1786_);
v_sz_1798_ = lean_array_size(v_preDefs_1785_);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_1798_, v___x_1796_, v_preDefs_1785_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1801_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; size_t v_sz_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___f_1818_; lean_object* v___x_1819_; lean_object* v_env_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc_n(v_a_1800_, 2);
lean_dec_ref_known(v___x_1799_, 1);
v___x_1801_ = lean_box(0);
v_sz_1815_ = lean_array_size(v_a_1800_);
v___x_1816_ = lean_box_usize(v_sz_1815_);
v___x_1817_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
v___f_1818_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1818_, 0, v_a_1800_);
lean_closure_set(v___f_1818_, 1, v___x_1816_);
lean_closure_set(v___f_1818_, 2, v___x_1817_);
lean_closure_set(v___f_1818_, 3, v___x_1801_);
lean_closure_set(v___f_1818_, 4, v___x_1794_);
v___x_1819_ = lean_st_ref_get(v_a_1792_);
v_env_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc_ref(v_env_1820_);
lean_dec(v___x_1819_);
v___x_1821_ = l_Lean_Environment_unlockAsync(v_env_1820_);
v___x_1822_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1821_, v___f_1818_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v_snd_1824_; lean_object* v_fst_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_2010_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref_known(v___x_1822_, 1);
v_snd_1824_ = lean_ctor_get(v_a_1823_, 1);
v_fst_1825_ = lean_ctor_get(v_a_1823_, 0);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_a_1823_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1827_ = v_a_1823_;
v_isShared_1828_ = v_isSharedCheck_2010_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_snd_1824_);
lean_inc(v_fst_1825_);
lean_dec(v_a_1823_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_2010_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_fst_1829_; lean_object* v_snd_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_2009_; 
v_fst_1829_ = lean_ctor_get(v_snd_1824_, 0);
v_snd_1830_ = lean_ctor_get(v_snd_1824_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_snd_1824_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1832_ = v_snd_1824_;
v_isShared_1833_ = v_isSharedCheck_2009_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_snd_1830_);
lean_inc(v_fst_1829_);
lean_dec(v_snd_1824_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_2009_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___y_1835_; lean_object* v___y_1836_; uint8_t v___y_1837_; lean_object* v___y_1838_; lean_object* v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___f_1893_; lean_object* v___x_1894_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v_wf_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___x_2000_; lean_object* v_a_2001_; uint8_t v___x_2002_; 
lean_inc(v_snd_1830_);
v___f_1893_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__1___boxed), 8, 1);
lean_closure_set(v___f_1893_, 0, v_snd_1830_);
v___x_1894_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2000_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1894_, v_a_1787_, v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref(v___x_2000_);
v___x_2002_ = lean_unbox(v_a_2001_);
lean_dec(v_a_2001_);
if (v___x_2002_ == 0)
{
v___y_1963_ = v_a_1787_;
v___y_1964_ = v_a_1788_;
v___y_1965_ = v_a_1789_;
v___y_1966_ = v_a_1790_;
v___y_1967_ = v_a_1791_;
v___y_1968_ = v_a_1792_;
goto v___jp_1962_;
}
else
{
lean_object* v_value_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v_value_2003_ = lean_ctor_get(v_snd_1830_, 7);
v___x_2004_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2003_);
v___x_2005_ = l_Lean_MessageData_ofExpr(v_value_2003_);
v___x_2006_ = l_Lean_indentD(v___x_2005_);
v___x_2007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2004_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v___x_1894_, v___x_2007_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_dec_ref_known(v___x_2008_, 1);
v___y_1963_ = v_a_1787_;
v___y_1964_ = v_a_1788_;
v___y_1965_ = v_a_1789_;
v___y_1966_ = v_a_1790_;
v___y_1967_ = v_a_1791_;
v___y_1968_ = v_a_1792_;
goto v___jp_1962_;
}
else
{
lean_dec_ref(v___f_1893_);
lean_del_object(v___x_1832_);
lean_dec(v_snd_1830_);
lean_dec(v_fst_1829_);
lean_del_object(v___x_1827_);
lean_dec(v_fst_1825_);
lean_dec(v_a_1800_);
lean_dec(v_termMeasures_x3f_1797_);
lean_dec_ref(v_docCtx_1784_);
return v___x_2008_;
}
}
v___jp_1834_:
{
lean_object* v___x_1844_; 
lean_inc_ref(v___y_1836_);
lean_inc(v_a_1800_);
lean_inc(v_fst_1829_);
lean_inc(v_fst_1825_);
v___x_1844_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1825_, v_fst_1829_, v_a_1800_, v___y_1836_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_a_1845_; lean_object* v___x_1846_; 
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref_known(v___x_1844_, 1);
lean_inc_ref(v___y_1836_);
lean_inc(v_a_1800_);
lean_inc_ref(v_docCtx_1784_);
v___x_1846_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1784_, v_a_1800_, v_a_1845_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v_a_1845_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v___x_1847_; 
lean_dec_ref_known(v___x_1846_, 1);
lean_inc(v_a_1800_);
v___x_1847_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1784_, v_a_1800_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v___x_1848_; 
lean_dec_ref_known(v___x_1847_, 1);
v___x_1848_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1830_, v___y_1837_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg(v_sz_1815_, v___x_1796_, v_a_1800_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v_declName_1852_; lean_object* v___x_1853_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc_n(v_a_1851_, 2);
lean_dec_ref_known(v___x_1850_, 1);
v_declName_1852_ = lean_ctor_get(v___y_1836_, 3);
lean_inc_n(v_declName_1852_, 2);
lean_dec_ref(v___y_1836_);
v___x_1853_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1851_, v_declName_1852_, v_fst_1825_, v_fst_1829_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_declName_1854_; lean_object* v_type_1855_; lean_object* v___x_1856_; 
lean_dec_ref_known(v___x_1853_, 1);
v_declName_1854_ = lean_ctor_get(v_a_1849_, 3);
v_type_1855_ = lean_ctor_get(v_a_1849_, 6);
lean_inc(v_declName_1854_);
v___x_1856_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1854_, v___y_1843_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v___x_1857_; 
lean_dec_ref_known(v___x_1856_, 1);
lean_inc_ref(v_type_1855_);
v___x_1857_ = l_Lean_Meta_isProp(v_type_1855_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; uint8_t v___x_1859_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1857_, 1);
v___x_1859_ = lean_unbox(v_a_1858_);
lean_dec(v_a_1858_);
if (v___x_1859_ == 0)
{
lean_object* v___x_1860_; 
lean_inc(v_declName_1852_);
v___x_1860_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1849_, v_declName_1852_, v___y_1835_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_dec_ref_known(v___x_1860_, 1);
v___y_1803_ = v_declName_1852_;
v___y_1804_ = v_a_1851_;
v___y_1805_ = v___y_1838_;
v___y_1806_ = v___y_1839_;
v___y_1807_ = v___y_1840_;
v___y_1808_ = v___y_1841_;
v___y_1809_ = v___y_1842_;
v___y_1810_ = v___y_1843_;
goto v___jp_1802_;
}
else
{
lean_dec(v_declName_1852_);
lean_dec(v_a_1851_);
return v___x_1860_;
}
}
else
{
lean_dec(v_a_1849_);
lean_dec_ref(v___y_1835_);
v___y_1803_ = v_declName_1852_;
v___y_1804_ = v_a_1851_;
v___y_1805_ = v___y_1838_;
v___y_1806_ = v___y_1839_;
v___y_1807_ = v___y_1840_;
v___y_1808_ = v___y_1841_;
v___y_1809_ = v___y_1842_;
v___y_1810_ = v___y_1843_;
goto v___jp_1802_;
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec(v_declName_1852_);
lean_dec(v_a_1851_);
lean_dec(v_a_1849_);
lean_dec_ref(v___y_1835_);
v_a_1861_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1857_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1857_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_dec(v_declName_1852_);
lean_dec(v_a_1851_);
lean_dec(v_a_1849_);
lean_dec_ref(v___y_1835_);
return v___x_1856_;
}
}
else
{
lean_dec(v_declName_1852_);
lean_dec(v_a_1851_);
lean_dec(v_a_1849_);
lean_dec_ref(v___y_1835_);
return v___x_1853_;
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec(v_a_1849_);
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v_fst_1829_);
lean_dec(v_fst_1825_);
v_a_1869_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1850_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1850_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v_fst_1829_);
lean_dec(v_fst_1825_);
lean_dec(v_a_1800_);
v_a_1877_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___x_1848_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1848_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
else
{
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v_snd_1830_);
lean_dec(v_fst_1829_);
lean_dec(v_fst_1825_);
lean_dec(v_a_1800_);
return v___x_1847_;
}
}
else
{
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v_snd_1830_);
lean_dec(v_fst_1829_);
lean_dec(v_fst_1825_);
lean_dec(v_a_1800_);
lean_dec_ref(v_docCtx_1784_);
return v___x_1846_;
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec_ref(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v_snd_1830_);
lean_dec(v_fst_1829_);
lean_dec(v_fst_1825_);
lean_dec(v_a_1800_);
lean_dec_ref(v_docCtx_1784_);
v_a_1885_ = lean_ctor_get(v___x_1844_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1844_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1844_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1844_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
v___jp_1895_:
{
lean_object* v_declName_1905_; lean_object* v_type_1906_; lean_object* v_numFixed_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___f_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; lean_object* v___x_1913_; 
v_declName_1905_ = lean_ctor_get(v_snd_1830_, 3);
v_type_1906_ = lean_ctor_get(v_snd_1830_, 6);
v_numFixed_1907_ = lean_ctor_get(v_fst_1825_, 0);
v___x_1908_ = lean_box_usize(v_sz_1815_);
v___x_1909_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1825_);
lean_inc(v_declName_1905_);
lean_inc(v_fst_1829_);
lean_inc(v_snd_1830_);
lean_inc(v_a_1800_);
v___f_1910_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1910_, 0, v___x_1908_);
lean_closure_set(v___f_1910_, 1, v___x_1909_);
lean_closure_set(v___f_1910_, 2, v_a_1800_);
lean_closure_set(v___f_1910_, 3, v_snd_1830_);
lean_closure_set(v___f_1910_, 4, v___y_1896_);
lean_closure_set(v___f_1910_, 5, v_fst_1829_);
lean_closure_set(v___f_1910_, 6, v___x_1801_);
lean_closure_set(v___f_1910_, 7, v___x_1894_);
lean_closure_set(v___f_1910_, 8, v_declName_1905_);
lean_closure_set(v___f_1910_, 9, v_fst_1825_);
lean_closure_set(v___f_1910_, 10, v_wf_1898_);
lean_inc(v_numFixed_1907_);
v___x_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1911_, 0, v_numFixed_1907_);
v___x_1912_ = 0;
lean_inc_ref(v_type_1906_);
v___x_1913_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_type_1906_, v___x_1911_, v___f_1910_, v___x_1912_, v___x_1912_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; lean_object* v_a_1916_; uint8_t v___x_1917_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1894_, v___y_1899_, v___y_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
v___x_1917_ = lean_unbox(v_a_1916_);
lean_dec(v_a_1916_);
if (v___x_1917_ == 0)
{
lean_del_object(v___x_1832_);
lean_del_object(v___x_1827_);
v___y_1835_ = v___y_1897_;
v___y_1836_ = v_a_1914_;
v___y_1837_ = v___x_1912_;
v___y_1838_ = v___y_1899_;
v___y_1839_ = v___y_1900_;
v___y_1840_ = v___y_1901_;
v___y_1841_ = v___y_1902_;
v___y_1842_ = v___y_1903_;
v___y_1843_ = v___y_1904_;
goto v___jp_1834_;
}
else
{
lean_object* v_declName_1918_; lean_object* v_value_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v_declName_1918_ = lean_ctor_get(v_a_1914_, 3);
v_value_1919_ = lean_ctor_get(v_a_1914_, 7);
v___x_1920_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1918_);
v___x_1921_ = l_Lean_MessageData_ofName(v_declName_1918_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 7);
lean_ctor_set(v___x_1832_, 1, v___x_1921_);
lean_ctor_set(v___x_1832_, 0, v___x_1920_);
v___x_1923_ = v___x_1832_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1920_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1924_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1828_ == 0)
{
lean_ctor_set_tag(v___x_1827_, 7);
lean_ctor_set(v___x_1827_, 1, v___x_1924_);
lean_ctor_set(v___x_1827_, 0, v___x_1923_);
v___x_1926_ = v___x_1827_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
lean_inc_ref(v_value_1919_);
v___x_1927_ = l_Lean_MessageData_ofExpr(v_value_1919_);
v___x_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v___x_1894_, v___x_1928_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_dec_ref_known(v___x_1929_, 1);
v___y_1835_ = v___y_1897_;
v___y_1836_ = v_a_1914_;
v___y_1837_ = v___x_1912_;
v___y_1838_ = v___y_1899_;
v___y_1839_ = v___y_1900_;
v___y_1840_ = v___y_1901_;
v___y_1841_ = v___y_1902_;
v___y_1842_ = v___y_1903_;
v___y_1843_ = v___y_1904_;
goto v___jp_1834_;
}
else
{
lean_dec(v_a_1914_);
lean_dec_ref(v___y_1897_);
lean_dec(v_snd_1830_);
lean_dec(v_fst_1829_);
lean_dec(v_fst_1825_);
lean_dec(v_a_1800_);
lean_dec_ref(v_docCtx_1784_);
return v___x_1929_;
}
}
}
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v___y_1897_);
lean_del_object(v___x_1832_);
lean_dec(v_snd_1830_);
lean_dec(v_fst_1829_);
lean_del_object(v___x_1827_);
lean_dec(v_fst_1825_);
lean_dec(v_a_1800_);
lean_dec_ref(v_docCtx_1784_);
v_a_1932_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1913_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1913_);
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
v___jp_1940_:
{
if (lean_obj_tag(v_termMeasures_x3f_1797_) == 1)
{
lean_object* v_val_1950_; 
lean_dec_ref(v___y_1943_);
v_val_1950_ = lean_ctor_get(v_termMeasures_x3f_1797_, 0);
lean_inc(v_val_1950_);
lean_dec_ref_known(v_termMeasures_x3f_1797_, 1);
v___y_1896_ = v___y_1941_;
v___y_1897_ = v___y_1942_;
v_wf_1898_ = v_val_1950_;
v___y_1899_ = v___y_1944_;
v___y_1900_ = v___y_1945_;
v___y_1901_ = v___y_1946_;
v___y_1902_ = v___y_1947_;
v___y_1903_ = v___y_1948_;
v___y_1904_ = v___y_1949_;
goto v___jp_1895_;
}
else
{
uint8_t v___x_1951_; lean_object* v___x_1952_; 
lean_dec(v_termMeasures_x3f_1797_);
v___x_1951_ = 1;
v___x_1952_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg(v___y_1943_, v___x_1951_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___y_1896_ = v___y_1941_;
v___y_1897_ = v___y_1942_;
v_wf_1898_ = v_a_1953_;
v___y_1899_ = v___y_1944_;
v___y_1900_ = v___y_1945_;
v___y_1901_ = v___y_1946_;
v___y_1902_ = v___y_1947_;
v___y_1903_ = v___y_1948_;
v___y_1904_ = v___y_1949_;
goto v___jp_1895_;
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_del_object(v___x_1832_);
lean_dec(v_snd_1830_);
lean_dec(v_fst_1829_);
lean_del_object(v___x_1827_);
lean_dec(v_fst_1825_);
lean_dec(v_a_1800_);
lean_dec_ref(v_docCtx_1784_);
v_a_1954_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1952_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1952_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
v___jp_1962_:
{
lean_object* v___x_1969_; lean_object* v_env_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v___x_1969_ = lean_st_ref_get(v___y_1968_);
v_env_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc_ref(v_env_1970_);
lean_dec(v___x_1969_);
v___x_1971_ = l_Lean_Environment_unlockAsync(v_env_1970_);
v___x_1972_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1971_, v___f_1893_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v_fst_1974_; lean_object* v_snd_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1991_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
v_fst_1974_ = lean_ctor_get(v_a_1973_, 0);
v_snd_1975_ = lean_ctor_get(v_a_1973_, 1);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_a_1973_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1977_ = v_a_1973_;
v_isShared_1978_ = v_isSharedCheck_1991_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_snd_1975_);
lean_inc(v_fst_1974_);
lean_dec(v_a_1973_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1991_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___f_1979_; lean_object* v___x_1980_; lean_object* v_a_1981_; uint8_t v___x_1982_; 
lean_inc(v_fst_1829_);
lean_inc(v_fst_1825_);
lean_inc(v_fst_1974_);
lean_inc(v_a_1800_);
v___f_1979_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__5___boxed), 11, 4);
lean_closure_set(v___f_1979_, 0, v_a_1800_);
lean_closure_set(v___f_1979_, 1, v_fst_1974_);
lean_closure_set(v___f_1979_, 2, v_fst_1825_);
lean_closure_set(v___f_1979_, 3, v_fst_1829_);
v___x_1980_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1894_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref(v___x_1980_);
v___x_1982_ = lean_unbox(v_a_1981_);
lean_dec(v_a_1981_);
if (v___x_1982_ == 0)
{
lean_del_object(v___x_1977_);
v___y_1941_ = v_fst_1974_;
v___y_1942_ = v_snd_1975_;
v___y_1943_ = v___f_1979_;
v___y_1944_ = v___y_1963_;
v___y_1945_ = v___y_1964_;
v___y_1946_ = v___y_1965_;
v___y_1947_ = v___y_1966_;
v___y_1948_ = v___y_1967_;
v___y_1949_ = v___y_1968_;
goto v___jp_1940_;
}
else
{
lean_object* v_value_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v_value_1983_ = lean_ctor_get(v_snd_1830_, 7);
v___x_1984_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_1983_);
v___x_1985_ = l_Lean_MessageData_ofExpr(v_value_1983_);
v___x_1986_ = l_Lean_indentD(v___x_1985_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set_tag(v___x_1977_, 7);
lean_ctor_set(v___x_1977_, 1, v___x_1986_);
lean_ctor_set(v___x_1977_, 0, v___x_1984_);
v___x_1988_ = v___x_1977_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v___x_1986_);
v___x_1988_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v___x_1894_, v___x_1988_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_dec_ref_known(v___x_1989_, 1);
v___y_1941_ = v_fst_1974_;
v___y_1942_ = v_snd_1975_;
v___y_1943_ = v___f_1979_;
v___y_1944_ = v___y_1963_;
v___y_1945_ = v___y_1964_;
v___y_1946_ = v___y_1965_;
v___y_1947_ = v___y_1966_;
v___y_1948_ = v___y_1967_;
v___y_1949_ = v___y_1968_;
goto v___jp_1940_;
}
else
{
lean_dec_ref(v___f_1979_);
lean_dec(v_snd_1975_);
lean_dec(v_fst_1974_);
lean_del_object(v___x_1832_);
lean_dec(v_snd_1830_);
lean_dec(v_fst_1829_);
lean_del_object(v___x_1827_);
lean_dec(v_fst_1825_);
lean_dec(v_a_1800_);
lean_dec(v_termMeasures_x3f_1797_);
lean_dec_ref(v_docCtx_1784_);
return v___x_1989_;
}
}
}
}
}
else
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_1999_; 
lean_del_object(v___x_1832_);
lean_dec(v_snd_1830_);
lean_dec(v_fst_1829_);
lean_del_object(v___x_1827_);
lean_dec(v_fst_1825_);
lean_dec(v_a_1800_);
lean_dec(v_termMeasures_x3f_1797_);
lean_dec_ref(v_docCtx_1784_);
v_a_1992_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1999_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1999_ == 0)
{
v___x_1994_ = v___x_1972_;
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1972_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_1999_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
if (v_isShared_1995_ == 0)
{
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2018_; 
lean_dec(v_a_1800_);
lean_dec(v_termMeasures_x3f_1797_);
lean_dec_ref(v_docCtx_1784_);
v_a_2011_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_2018_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_2018_ == 0)
{
v___x_2013_ = v___x_1822_;
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_a_2011_);
lean_dec(v___x_1822_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2018_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___x_2016_; 
if (v_isShared_2014_ == 0)
{
v___x_2016_ = v___x_2013_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_a_2011_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
}
v___jp_1802_:
{
size_t v_sz_1811_; lean_object* v___x_1812_; 
v_sz_1811_ = lean_array_size(v___y_1804_);
lean_inc(v___y_1803_);
v___x_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_1803_, v___y_1804_, v_sz_1811_, v___x_1796_, v___x_1801_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1812_) == 0)
{
lean_object* v___x_1813_; 
lean_dec_ref_known(v___x_1812_, 1);
v___x_1813_ = l_Lean_enableRealizationsForConst(v___y_1803_, v___y_1809_, v___y_1810_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1814_; 
lean_dec_ref_known(v___x_1813_, 1);
v___x_1814_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_);
return v___x_1814_;
}
else
{
lean_dec_ref(v___y_1804_);
return v___x_1813_;
}
}
else
{
lean_dec_ref(v___y_1804_);
lean_dec(v___y_1803_);
return v___x_1812_;
}
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v_termMeasures_x3f_1797_);
lean_dec_ref(v_docCtx_1784_);
v_a_2019_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1799_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1799_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2027_, lean_object* v_preDefs_2028_, lean_object* v_termMeasure_x3fs_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_res_2037_; 
v_res_2037_ = l_Lean_Elab_wfRecursion(v_docCtx_2027_, v_preDefs_2028_, v_termMeasure_x3fs_2029_, v_a_2030_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
lean_dec(v_a_2035_);
lean_dec_ref(v_a_2034_);
lean_dec(v_a_2033_);
lean_dec_ref(v_a_2032_);
lean_dec(v_a_2031_);
lean_dec_ref(v_a_2030_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2038_, lean_object* v_msg_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_, v___y_2044_, v___y_2045_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2048_, lean_object* v_msg_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2048_, v_msg_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
lean_dec(v___y_2055_);
lean_dec_ref(v___y_2054_);
lean_dec(v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec_ref(v___y_2050_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(size_t v_sz_2058_, size_t v_i_2059_, lean_object* v_bs_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_2058_, v_i_2059_, v_bs_2060_, v___y_2065_, v___y_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_sz_2069_, lean_object* v_i_2070_, lean_object* v_bs_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
size_t v_sz_boxed_2079_; size_t v_i_boxed_2080_; lean_object* v_res_2081_; 
v_sz_boxed_2079_ = lean_unbox_usize(v_sz_2069_);
lean_dec(v_sz_2069_);
v_i_boxed_2080_ = lean_unbox_usize(v_i_2070_);
lean_dec(v_i_2070_);
v_res_2081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(v_sz_boxed_2079_, v_i_boxed_2080_, v_bs_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_as_2082_, size_t v_sz_2083_, size_t v_i_2084_, lean_object* v_b_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_as_2082_, v_sz_2083_, v_i_2084_, v_b_2085_, v___y_2090_, v___y_2091_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_as_2094_, lean_object* v_sz_2095_, lean_object* v_i_2096_, lean_object* v_b_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
size_t v_sz_boxed_2105_; size_t v_i_boxed_2106_; lean_object* v_res_2107_; 
v_sz_boxed_2105_ = lean_unbox_usize(v_sz_2095_);
lean_dec(v_sz_2095_);
v_i_boxed_2106_ = lean_unbox_usize(v_i_2096_);
lean_dec(v_i_2096_);
v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(v_as_2094_, v_sz_boxed_2105_, v_i_boxed_2106_, v_b_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec_ref(v_as_2094_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(lean_object* v_a_2108_, lean_object* v_as_2109_, size_t v_sz_2110_, size_t v_i_2111_, lean_object* v_bs_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_2108_, v_sz_2110_, v_i_2111_, v_bs_2112_, v___y_2115_, v___y_2116_, v___y_2117_, v___y_2118_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object* v_a_2121_, lean_object* v_as_2122_, lean_object* v_sz_2123_, lean_object* v_i_2124_, lean_object* v_bs_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
size_t v_sz_boxed_2133_; size_t v_i_boxed_2134_; lean_object* v_res_2135_; 
v_sz_boxed_2133_ = lean_unbox_usize(v_sz_2123_);
lean_dec(v_sz_2123_);
v_i_boxed_2134_ = lean_unbox_usize(v_i_2124_);
lean_dec(v_i_2124_);
v_res_2135_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(v_a_2121_, v_as_2122_, v_sz_boxed_2133_, v_i_boxed_2134_, v_bs_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec_ref(v_as_2122_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_a_2136_, lean_object* v___x_2137_, size_t v_sz_2138_, size_t v_i_2139_, lean_object* v_bs_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_2136_, v___x_2137_, v_sz_2138_, v_i_2139_, v_bs_2140_, v___y_2145_, v___y_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_a_2149_, lean_object* v___x_2150_, lean_object* v_sz_2151_, lean_object* v_i_2152_, lean_object* v_bs_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
size_t v_sz_boxed_2161_; size_t v_i_boxed_2162_; lean_object* v_res_2163_; 
v_sz_boxed_2161_ = lean_unbox_usize(v_sz_2151_);
lean_dec(v_sz_2151_);
v_i_boxed_2162_ = lean_unbox_usize(v_i_2152_);
lean_dec(v_i_2152_);
v_res_2163_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(v_a_2149_, v___x_2150_, v_sz_boxed_2161_, v_i_boxed_2162_, v_bs_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(lean_object* v_00_u03b1_2164_, lean_object* v_env_2165_, lean_object* v_x_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_2165_, v_x_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_00_u03b1_2175_, lean_object* v_env_2176_, lean_object* v_x_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(v_00_u03b1_2175_, v_env_2176_, v_x_2177_, v___y_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object* v_env_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_2186_, v___y_2190_, v___y_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object* v_env_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(v_env_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object* v_00_u03b2_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11___redArg(){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11___redArg___boxed(lean_object* v___dummy_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11___redArg();
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_Elab_wfRecursion_spec__11(lean_object* v_00_u03b2_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15(lean_object* v_cls_2212_, lean_object* v_msg_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_cls_2212_, v_msg_2213_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object* v_cls_2222_, lean_object* v_msg_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15(v_cls_2222_, v_msg_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17(size_t v_sz_2232_, size_t v_i_2233_, lean_object* v_bs_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg(v_sz_2232_, v_i_2233_, v_bs_2234_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object* v_sz_2243_, lean_object* v_i_2244_, lean_object* v_bs_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
size_t v_sz_boxed_2253_; size_t v_i_boxed_2254_; lean_object* v_res_2255_; 
v_sz_boxed_2253_ = lean_unbox_usize(v_sz_2243_);
lean_dec(v_sz_2243_);
v_i_boxed_2254_ = lean_unbox_usize(v_i_2244_);
lean_dec(v_i_2244_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17(v_sz_boxed_2253_, v_i_boxed_2254_, v_bs_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18(lean_object* v___x_2256_, lean_object* v_as_2257_, size_t v_sz_2258_, size_t v_i_2259_, lean_object* v_b_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___x_2256_, v_as_2257_, v_sz_2258_, v_i_2259_, v_b_2260_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object* v___x_2269_, lean_object* v_as_2270_, lean_object* v_sz_2271_, lean_object* v_i_2272_, lean_object* v_b_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
size_t v_sz_boxed_2281_; size_t v_i_boxed_2282_; lean_object* v_res_2283_; 
v_sz_boxed_2281_ = lean_unbox_usize(v_sz_2271_);
lean_dec(v_sz_2271_);
v_i_boxed_2282_ = lean_unbox_usize(v_i_2272_);
lean_dec(v_i_2272_);
v_res_2283_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18(v___x_2269_, v_as_2270_, v_sz_boxed_2281_, v_i_boxed_2282_, v_b_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v_as_2270_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19(lean_object* v_00_u03b1_2284_, lean_object* v_x_2285_, uint8_t v_when_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg(v_x_2285_, v_when_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___boxed(lean_object* v_00_u03b1_2295_, lean_object* v_x_2296_, lean_object* v_when_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v_when_boxed_2305_; lean_object* v_res_2306_; 
v_when_boxed_2305_ = lean_unbox(v_when_2297_);
v_res_2306_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19(v_00_u03b1_2295_, v_x_2296_, v_when_boxed_2305_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
lean_dec(v___y_2301_);
lean_dec_ref(v___y_2300_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2307_, lean_object* v_macroStack_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2307_, v_macroStack_2308_, v___y_2313_);
return v___x_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2317_, lean_object* v_macroStack_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2317_, v_macroStack_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15(lean_object* v_ref_2327_, lean_object* v_msgData_2328_, uint8_t v_severity_2329_, uint8_t v_isSilent_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___redArg(v_ref_2327_, v_msgData_2328_, v_severity_2329_, v_isSilent_2330_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15___boxed(lean_object* v_ref_2339_, lean_object* v_msgData_2340_, lean_object* v_severity_2341_, lean_object* v_isSilent_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
uint8_t v_severity_boxed_2350_; uint8_t v_isSilent_boxed_2351_; lean_object* v_res_2352_; 
v_severity_boxed_2350_ = lean_unbox(v_severity_2341_);
v_isSilent_boxed_2351_ = lean_unbox(v_isSilent_2342_);
v_res_2352_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__15(v_ref_2339_, v_msgData_2340_, v_severity_boxed_2350_, v_isSilent_boxed_2351_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
lean_dec(v_ref_2339_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23(lean_object* v_00_u03b1_2353_, lean_object* v_x_2354_, uint8_t v_isExporting_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___redArg(v_x_2354_, v_isExporting_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23___boxed(lean_object* v_00_u03b1_2364_, lean_object* v_x_2365_, lean_object* v_isExporting_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
uint8_t v_isExporting_boxed_2374_; lean_object* v_res_2375_; 
v_isExporting_boxed_2374_ = lean_unbox(v_isExporting_2366_);
v_res_2375_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__23(v_00_u03b1_2364_, v_x_2365_, v_isExporting_boxed_2374_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2446_; uint8_t v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2446_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2447_ = 0;
v___x_2448_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_));
v___x_2449_ = l_Lean_registerTraceClass(v___x_2446_, v___x_2447_, v___x_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object* v_a_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
return v_res_2451_;
}
}
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_GuessLex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin);
lean_object* initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_GuessLex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
}
#ifdef __cplusplus
}
#endif
