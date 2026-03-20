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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_WF_floatRecApp(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_addAsAxiom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getFixedParamPerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_copyExtraModUses(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_isNatLtWF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Elab_WF_guessLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6(lean_object*, lean_object*);
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
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "well-founded recursion cannot be used, `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not take any (non-fixed) arguments"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__11(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wfRel: "};
static const lean_object* l_Lean_Elab_wfRecursion___lam__2___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___lam__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "wfRecursion: expected unary function type: "};
static const lean_object* l_Lean_Elab_wfRecursion___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__0_value;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__1_value;
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 8, 70, 241, 95, 177, 39, 230)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 119, 48, 4, 113, 111, 251, 171)}};
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg(lean_object* v_cls_4_, lean_object* v___y_5_){
_start:
{
lean_object* v_options_7_; uint8_t v_hasTrace_8_; 
v_options_7_ = lean_ctor_get(v___y_5_, 2);
v_hasTrace_8_ = lean_ctor_get_uint8(v_options_7_, sizeof(void*)*1);
if (v_hasTrace_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_cls_4_);
v___x_9_ = lean_box(v_hasTrace_8_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_inheritedTraceOptions_11_; lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v_inheritedTraceOptions_11_ = lean_ctor_get(v___y_5_, 13);
v___x_12_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___closed__1));
v___x_13_ = l_Lean_Name_append(v___x_12_, v_cls_4_);
v___x_14_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_11_, v_options_7_, v___x_13_);
lean_dec(v___x_13_);
v___x_15_ = lean_box(v___x_14_);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___boxed(lean_object* v_cls_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_cls_17_, v___y_18_);
lean_dec_ref(v___y_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8(lean_object* v_cls_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_cls_21_, v___y_26_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_cls_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8(v_cls_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_, v___y_36_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
return v_res_38_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_39_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__0);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__1);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__1);
v___x_45_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_45_, 0, v___x_44_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
lean_ctor_set(v___x_45_, 2, v___x_44_);
lean_ctor_set(v___x_45_, 3, v___x_44_);
lean_ctor_set(v___x_45_, 4, v___x_44_);
lean_ctor_set(v___x_45_, 5, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg(lean_object* v_env_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v___x_50_; lean_object* v_nextMacroScope_51_; lean_object* v_ngen_52_; lean_object* v_auxDeclNGen_53_; lean_object* v_traceState_54_; lean_object* v_messages_55_; lean_object* v_infoState_56_; lean_object* v_snapshotTasks_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_83_; 
v___x_50_ = lean_st_ref_take(v___y_48_);
v_nextMacroScope_51_ = lean_ctor_get(v___x_50_, 1);
v_ngen_52_ = lean_ctor_get(v___x_50_, 2);
v_auxDeclNGen_53_ = lean_ctor_get(v___x_50_, 3);
v_traceState_54_ = lean_ctor_get(v___x_50_, 4);
v_messages_55_ = lean_ctor_get(v___x_50_, 6);
v_infoState_56_ = lean_ctor_get(v___x_50_, 7);
v_snapshotTasks_57_ = lean_ctor_get(v___x_50_, 8);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_50_);
if (v_isSharedCheck_83_ == 0)
{
lean_object* v_unused_84_; lean_object* v_unused_85_; 
v_unused_84_ = lean_ctor_get(v___x_50_, 5);
lean_dec(v_unused_84_);
v_unused_85_ = lean_ctor_get(v___x_50_, 0);
lean_dec(v_unused_85_);
v___x_59_ = v___x_50_;
v_isShared_60_ = v_isSharedCheck_83_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_snapshotTasks_57_);
lean_inc(v_infoState_56_);
lean_inc(v_messages_55_);
lean_inc(v_traceState_54_);
lean_inc(v_auxDeclNGen_53_);
lean_inc(v_ngen_52_);
lean_inc(v_nextMacroScope_51_);
lean_dec(v___x_50_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_83_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_61_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 5, v___x_61_);
lean_ctor_set(v___x_59_, 0, v_env_46_);
v___x_63_ = v___x_59_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_env_46_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_nextMacroScope_51_);
lean_ctor_set(v_reuseFailAlloc_82_, 2, v_ngen_52_);
lean_ctor_set(v_reuseFailAlloc_82_, 3, v_auxDeclNGen_53_);
lean_ctor_set(v_reuseFailAlloc_82_, 4, v_traceState_54_);
lean_ctor_set(v_reuseFailAlloc_82_, 5, v___x_61_);
lean_ctor_set(v_reuseFailAlloc_82_, 6, v_messages_55_);
lean_ctor_set(v_reuseFailAlloc_82_, 7, v_infoState_56_);
lean_ctor_set(v_reuseFailAlloc_82_, 8, v_snapshotTasks_57_);
v___x_63_ = v_reuseFailAlloc_82_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_mctx_66_; lean_object* v_zetaDeltaFVarIds_67_; lean_object* v_postponed_68_; lean_object* v_diag_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_80_; 
v___x_64_ = lean_st_ref_set(v___y_48_, v___x_63_);
v___x_65_ = lean_st_ref_take(v___y_47_);
v_mctx_66_ = lean_ctor_get(v___x_65_, 0);
v_zetaDeltaFVarIds_67_ = lean_ctor_get(v___x_65_, 2);
v_postponed_68_ = lean_ctor_get(v___x_65_, 3);
v_diag_69_ = lean_ctor_get(v___x_65_, 4);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_65_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v___x_65_, 1);
lean_dec(v_unused_81_);
v___x_71_ = v___x_65_;
v_isShared_72_ = v_isSharedCheck_80_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_diag_69_);
lean_inc(v_postponed_68_);
lean_inc(v_zetaDeltaFVarIds_67_);
lean_inc(v_mctx_66_);
lean_dec(v___x_65_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_80_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_73_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___x_73_);
v___x_75_ = v___x_71_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_mctx_66_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_79_, 2, v_zetaDeltaFVarIds_67_);
lean_ctor_set(v_reuseFailAlloc_79_, 3, v_postponed_68_);
lean_ctor_set(v_reuseFailAlloc_79_, 4, v_diag_69_);
v___x_75_ = v_reuseFailAlloc_79_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = lean_st_ref_set(v___y_47_, v___x_75_);
v___x_77_ = lean_box(0);
v___x_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___boxed(lean_object* v_env_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg(v_env_86_, v___y_87_, v___y_88_);
lean_dec(v___y_88_);
lean_dec(v___y_87_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10(lean_object* v_env_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg(v_env_91_, v___y_95_, v___y_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_env_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10(v_env_100_, v___y_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_101_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0(lean_object* v_k_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v_b_112_, lean_object* v_c_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = lean_apply_9(v_k_109_, v_b_112_, v_c_113_, v___y_110_, v___y_111_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, lean_box(0));
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0___boxed(lean_object* v_k_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v_b_123_, lean_object* v_c_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0(v_k_120_, v___y_121_, v___y_122_, v_b_123_, v_c_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg(lean_object* v_type_131_, lean_object* v_maxFVars_x3f_132_, lean_object* v_k_133_, uint8_t v_cleanupAnnotations_134_, uint8_t v_whnfType_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___f_143_; lean_object* v___x_144_; 
v___f_143_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_143_, 0, v_k_133_);
lean_closure_set(v___f_143_, 1, v___y_136_);
lean_closure_set(v___f_143_, 2, v___y_137_);
v___x_144_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_131_, v_maxFVars_x3f_132_, v___f_143_, v_cleanupAnnotations_134_, v_whnfType_135_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
if (lean_obj_tag(v___x_144_) == 0)
{
return v___x_144_;
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_type_153_, lean_object* v_maxFVars_x3f_154_, lean_object* v_k_155_, lean_object* v_cleanupAnnotations_156_, lean_object* v_whnfType_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_165_; uint8_t v_whnfType_boxed_166_; lean_object* v_res_167_; 
v_cleanupAnnotations_boxed_165_ = lean_unbox(v_cleanupAnnotations_156_);
v_whnfType_boxed_166_ = lean_unbox(v_whnfType_157_);
v_res_167_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_type_153_, v_maxFVars_x3f_154_, v_k_155_, v_cleanupAnnotations_boxed_165_, v_whnfType_boxed_166_, v___y_158_, v___y_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16(lean_object* v_00_u03b1_168_, lean_object* v_type_169_, lean_object* v_maxFVars_x3f_170_, lean_object* v_k_171_, uint8_t v_cleanupAnnotations_172_, uint8_t v_whnfType_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_type_169_, v_maxFVars_x3f_170_, v_k_171_, v_cleanupAnnotations_172_, v_whnfType_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_00_u03b1_182_, lean_object* v_type_183_, lean_object* v_maxFVars_x3f_184_, lean_object* v_k_185_, lean_object* v_cleanupAnnotations_186_, lean_object* v_whnfType_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_195_; uint8_t v_whnfType_boxed_196_; lean_object* v_res_197_; 
v_cleanupAnnotations_boxed_195_ = lean_unbox(v_cleanupAnnotations_186_);
v_whnfType_boxed_196_ = lean_unbox(v_whnfType_187_);
v_res_197_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16(v_00_u03b1_182_, v_type_183_, v_maxFVars_x3f_184_, v_k_185_, v_cleanupAnnotations_boxed_195_, v_whnfType_boxed_196_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
return v_res_197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object* v_opts_198_, lean_object* v_opt_199_){
_start:
{
lean_object* v_name_200_; lean_object* v_defValue_201_; lean_object* v_map_202_; lean_object* v___x_203_; 
v_name_200_ = lean_ctor_get(v_opt_199_, 0);
v_defValue_201_ = lean_ctor_get(v_opt_199_, 1);
v_map_202_ = lean_ctor_get(v_opts_198_, 0);
v___x_203_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_202_, v_name_200_);
if (lean_obj_tag(v___x_203_) == 0)
{
uint8_t v___x_204_; 
v___x_204_ = lean_unbox(v_defValue_201_);
return v___x_204_;
}
else
{
lean_object* v_val_205_; 
v_val_205_ = lean_ctor_get(v___x_203_, 0);
lean_inc(v_val_205_);
lean_dec_ref(v___x_203_);
if (lean_obj_tag(v_val_205_) == 1)
{
uint8_t v_v_206_; 
v_v_206_ = lean_ctor_get_uint8(v_val_205_, 0);
lean_dec_ref(v_val_205_);
return v_v_206_;
}
else
{
uint8_t v___x_207_; 
lean_dec(v_val_205_);
v___x_207_ = lean_unbox(v_defValue_201_);
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___boxed(lean_object* v_opts_208_, lean_object* v_opt_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_opts_208_, v_opt_209_);
lean_dec_ref(v_opt_209_);
lean_dec_ref(v_opts_208_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__0(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_box(1);
v___x_213_ = l_Lean_MessageData_ofFormat(v___x_212_);
return v___x_213_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__3(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__2));
v___x_218_ = l_Lean_MessageData_ofFormat(v___x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6(lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
return v_x_219_;
}
else
{
lean_object* v_head_221_; lean_object* v_tail_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_244_; 
v_head_221_ = lean_ctor_get(v_x_220_, 0);
v_tail_222_ = lean_ctor_get(v_x_220_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_220_);
if (v_isSharedCheck_244_ == 0)
{
v___x_224_ = v_x_220_;
v_isShared_225_ = v_isSharedCheck_244_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_tail_222_);
lean_inc(v_head_221_);
lean_dec(v_x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_244_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v_before_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_242_; 
v_before_226_ = lean_ctor_get(v_head_221_, 0);
v_isSharedCheck_242_ = !lean_is_exclusive(v_head_221_);
if (v_isSharedCheck_242_ == 0)
{
lean_object* v_unused_243_; 
v_unused_243_ = lean_ctor_get(v_head_221_, 1);
lean_dec(v_unused_243_);
v___x_228_ = v_head_221_;
v_isShared_229_ = v_isSharedCheck_242_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_before_226_);
lean_dec(v_head_221_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_242_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_230_; lean_object* v___x_232_; 
v___x_230_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_229_ == 0)
{
lean_ctor_set_tag(v___x_228_, 7);
lean_ctor_set(v___x_228_, 1, v___x_230_);
lean_ctor_set(v___x_228_, 0, v_x_219_);
v___x_232_ = v___x_228_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_x_219_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v___x_230_);
v___x_232_ = v_reuseFailAlloc_241_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_235_; 
v___x_233_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__3);
if (v_isShared_225_ == 0)
{
lean_ctor_set_tag(v___x_224_, 7);
lean_ctor_set(v___x_224_, 1, v___x_233_);
lean_ctor_set(v___x_224_, 0, v___x_232_);
v___x_235_ = v___x_224_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_233_);
v___x_235_ = v_reuseFailAlloc_240_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = l_Lean_MessageData_ofSyntax(v_before_226_);
v___x_237_ = l_Lean_indentD(v___x_236_);
v___x_238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_235_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v_x_219_ = v___x_238_;
v_x_220_ = v_tail_222_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1));
v___x_249_ = l_Lean_MessageData_ofFormat(v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object* v_msgData_250_, lean_object* v_macroStack_251_, lean_object* v___y_252_){
_start:
{
lean_object* v_options_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_options_254_ = lean_ctor_get(v___y_252_, 2);
v___x_255_ = l_Lean_Elab_pp_macroStack;
v___x_256_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_options_254_, v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v_macroStack_251_);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v_msgData_250_);
return v___x_257_;
}
else
{
if (lean_obj_tag(v_macroStack_251_) == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v_msgData_250_);
return v___x_258_;
}
else
{
lean_object* v_head_259_; lean_object* v_after_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_275_; 
v_head_259_ = lean_ctor_get(v_macroStack_251_, 0);
lean_inc(v_head_259_);
v_after_260_ = lean_ctor_get(v_head_259_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_head_259_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_head_259_, 0);
lean_dec(v_unused_276_);
v___x_262_ = v_head_259_;
v_isShared_263_ = v_isSharedCheck_275_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_after_260_);
lean_dec(v_head_259_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_275_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_264_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6___closed__0);
if (v_isShared_263_ == 0)
{
lean_ctor_set_tag(v___x_262_, 7);
lean_ctor_set(v___x_262_, 1, v___x_264_);
lean_ctor_set(v___x_262_, 0, v_msgData_250_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_msgData_250_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_264_);
v___x_266_ = v_reuseFailAlloc_274_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v_msgData_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_267_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Lean_MessageData_ofSyntax(v_after_260_);
v___x_270_ = l_Lean_indentD(v___x_269_);
v_msgData_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_271_, 0, v___x_268_);
lean_ctor_set(v_msgData_271_, 1, v___x_270_);
v___x_272_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__6(v_msgData_271_, v_macroStack_251_);
v___x_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_277_, lean_object* v_macroStack_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_277_, v_macroStack_278_, v___y_279_);
lean_dec_ref(v___y_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object* v_msgData_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; lean_object* v_env_289_; lean_object* v___x_290_; lean_object* v_mctx_291_; lean_object* v_lctx_292_; lean_object* v_options_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_288_ = lean_st_ref_get(v___y_286_);
v_env_289_ = lean_ctor_get(v___x_288_, 0);
lean_inc_ref(v_env_289_);
lean_dec(v___x_288_);
v___x_290_ = lean_st_ref_get(v___y_284_);
v_mctx_291_ = lean_ctor_get(v___x_290_, 0);
lean_inc_ref(v_mctx_291_);
lean_dec(v___x_290_);
v_lctx_292_ = lean_ctor_get(v___y_283_, 2);
v_options_293_ = lean_ctor_get(v___y_285_, 2);
lean_inc_ref(v_options_293_);
lean_inc_ref(v_lctx_292_);
v___x_294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_294_, 0, v_env_289_);
lean_ctor_set(v___x_294_, 1, v_mctx_291_);
lean_ctor_set(v___x_294_, 2, v_lctx_292_);
lean_ctor_set(v___x_294_, 3, v_options_293_);
v___x_295_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v_msgData_282_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object* v_msgData_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object* v_msg_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_ref_312_; lean_object* v___x_313_; lean_object* v_a_314_; lean_object* v_macroStack_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_326_; 
v_ref_312_ = lean_ctor_get(v___y_309_, 5);
v___x_313_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_304_, v___y_307_, v___y_308_, v___y_309_, v___y_310_);
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref(v___x_313_);
v_macroStack_315_ = lean_ctor_get(v___y_305_, 1);
lean_inc(v_macroStack_315_);
lean_dec_ref(v___y_305_);
lean_inc(v_macroStack_315_);
v___x_316_ = l_Lean_Elab_getBetterRef(v_ref_312_, v_macroStack_315_);
v___x_317_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_314_, v_macroStack_315_, v___y_309_);
v_a_318_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_326_ == 0)
{
v___x_320_ = v___x_317_;
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_326_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_316_);
lean_ctor_set(v___x_322_, 1, v_a_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set_tag(v___x_320_, 1);
lean_ctor_set(v___x_320_, 0, v___x_322_);
v___x_324_ = v___x_320_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
return v_res_335_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0));
v___x_338_ = l_Lean_stringToMessageData(v___x_337_);
return v___x_338_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2));
v___x_341_ = l_Lean_stringToMessageData(v___x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(lean_object* v_as_342_, size_t v_sz_343_, size_t v_i_344_, lean_object* v_b_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_){
_start:
{
lean_object* v_a_354_; uint8_t v___x_358_; 
v___x_358_ = lean_usize_dec_lt(v_i_344_, v_sz_343_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_dec_ref(v___y_346_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v_b_345_);
return v___x_359_;
}
else
{
lean_object* v_array_360_; lean_object* v_start_361_; lean_object* v_stop_362_; uint8_t v___x_363_; 
v_array_360_ = lean_ctor_get(v_b_345_, 0);
v_start_361_ = lean_ctor_get(v_b_345_, 1);
v_stop_362_ = lean_ctor_get(v_b_345_, 2);
v___x_363_ = lean_nat_dec_lt(v_start_361_, v_stop_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; 
lean_dec_ref(v___y_346_);
v___x_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_364_, 0, v_b_345_);
return v___x_364_;
}
else
{
lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_393_; 
lean_inc(v_stop_362_);
lean_inc(v_start_361_);
lean_inc_ref(v_array_360_);
v_isSharedCheck_393_ = !lean_is_exclusive(v_b_345_);
if (v_isSharedCheck_393_ == 0)
{
lean_object* v_unused_394_; lean_object* v_unused_395_; lean_object* v_unused_396_; 
v_unused_394_ = lean_ctor_get(v_b_345_, 2);
lean_dec(v_unused_394_);
v_unused_395_ = lean_ctor_get(v_b_345_, 1);
lean_dec(v_unused_395_);
v_unused_396_ = lean_ctor_get(v_b_345_, 0);
lean_dec(v_unused_396_);
v___x_366_ = v_b_345_;
v_isShared_367_ = v_isSharedCheck_393_;
goto v_resetjp_365_;
}
else
{
lean_dec(v_b_345_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_393_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v_a_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v_a_368_ = lean_array_uget_borrowed(v_as_342_, v_i_344_);
v___x_369_ = lean_array_fget(v_array_360_, v_start_361_);
v___x_370_ = lean_unsigned_to_nat(1u);
v___x_371_ = lean_nat_add(v_start_361_, v___x_370_);
lean_dec(v_start_361_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v___x_371_);
v___x_373_ = v___x_366_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_array_360_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_392_, 2, v_stop_362_);
v___x_373_ = v_reuseFailAlloc_392_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v___x_374_ = lean_array_get_size(v_a_368_);
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_nat_dec_eq(v___x_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_dec(v___x_369_);
v_a_354_ = v___x_373_;
goto v___jp_353_;
}
else
{
lean_object* v_declName_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v_declName_377_ = lean_ctor_get(v___x_369_, 3);
lean_inc(v_declName_377_);
lean_dec(v___x_369_);
v___x_378_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1);
v___x_379_ = l_Lean_MessageData_ofName(v_declName_377_);
v___x_380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
v___x_381_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3);
v___x_382_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_380_);
lean_ctor_set(v___x_382_, 1, v___x_381_);
lean_inc_ref(v___y_346_);
v___x_383_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_382_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
if (lean_obj_tag(v___x_383_) == 0)
{
lean_dec_ref(v___x_383_);
v_a_354_ = v___x_373_;
goto v___jp_353_;
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
lean_dec_ref(v___x_373_);
lean_dec_ref(v___y_346_);
v_a_384_ = lean_ctor_get(v___x_383_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_383_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_383_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_383_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
}
}
}
v___jp_353_:
{
size_t v___x_355_; size_t v___x_356_; 
v___x_355_ = ((size_t)1ULL);
v___x_356_ = lean_usize_add(v_i_344_, v___x_355_);
v_i_344_ = v___x_356_;
v_b_345_ = v_a_354_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object* v_as_397_, lean_object* v_sz_398_, lean_object* v_i_399_, lean_object* v_b_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_398_);
lean_dec(v_sz_398_);
v_i_boxed_409_ = lean_unbox_usize(v_i_399_);
lean_dec(v_i_399_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_as_397_, v_sz_boxed_408_, v_i_boxed_409_, v_b_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
lean_dec(v___y_402_);
lean_dec_ref(v_as_397_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object* v_a_411_, lean_object* v_as_412_, lean_object* v_i_413_, lean_object* v_j_414_, lean_object* v_bs_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_zero_421_; uint8_t v_isZero_422_; 
v_zero_421_ = lean_unsigned_to_nat(0u);
v_isZero_422_ = lean_nat_dec_eq(v_i_413_, v_zero_421_);
if (v_isZero_422_ == 1)
{
lean_object* v___x_423_; 
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v_j_414_);
lean_dec(v_i_413_);
lean_dec_ref(v_a_411_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v_bs_415_);
return v___x_423_;
}
else
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_array_fget_borrowed(v_as_412_, v_j_414_);
lean_inc(v___y_419_);
lean_inc_ref(v___y_418_);
lean_inc(v___y_417_);
lean_inc_ref(v___y_416_);
lean_inc(v___x_424_);
lean_inc(v_j_414_);
lean_inc_ref(v_a_411_);
v___x_425_ = l_Lean_Elab_WF_varyingVarNames(v_a_411_, v_j_414_, v___x_424_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_a_426_; lean_object* v_one_427_; lean_object* v_n_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v_a_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_a_426_);
lean_dec_ref(v___x_425_);
v_one_427_ = lean_unsigned_to_nat(1u);
v_n_428_ = lean_nat_sub(v_i_413_, v_one_427_);
lean_dec(v_i_413_);
v___x_429_ = lean_nat_add(v_j_414_, v_one_427_);
lean_dec(v_j_414_);
v___x_430_ = lean_array_push(v_bs_415_, v_a_426_);
v_i_413_ = v_n_428_;
v_j_414_ = v___x_429_;
v_bs_415_ = v___x_430_;
goto _start;
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec_ref(v_bs_415_);
lean_dec(v_j_414_);
lean_dec(v_i_413_);
lean_dec_ref(v_a_411_);
v_a_432_ = lean_ctor_get(v___x_425_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_425_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_425_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object* v_a_440_, lean_object* v_as_441_, lean_object* v_i_442_, lean_object* v_j_443_, lean_object* v_bs_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_440_, v_as_441_, v_i_442_, v_j_443_, v_bs_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec_ref(v_as_441_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(lean_object* v_as_451_, size_t v_sz_452_, size_t v_i_453_, lean_object* v_b_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
uint8_t v___x_458_; 
v___x_458_ = lean_usize_dec_lt(v_i_453_, v_sz_452_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v_b_454_);
return v___x_459_;
}
else
{
lean_object* v_a_460_; lean_object* v___x_461_; 
v_a_460_ = lean_array_uget_borrowed(v_as_451_, v_i_453_);
lean_inc(v___y_456_);
lean_inc_ref(v___y_455_);
v___x_461_ = l_Lean_Elab_addAsAxiom___redArg(v_a_460_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v___x_462_; size_t v___x_463_; size_t v___x_464_; 
lean_dec_ref(v___x_461_);
v___x_462_ = lean_box(0);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_add(v_i_453_, v___x_463_);
v_i_453_ = v___x_464_;
v_b_454_ = v___x_462_;
goto _start;
}
else
{
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* v_as_466_, lean_object* v_sz_467_, lean_object* v_i_468_, lean_object* v_b_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
size_t v_sz_boxed_473_; size_t v_i_boxed_474_; lean_object* v_res_475_; 
v_sz_boxed_473_ = lean_unbox_usize(v_sz_467_);
lean_dec(v_sz_467_);
v_i_boxed_474_ = lean_unbox_usize(v_i_468_);
lean_dec(v_i_468_);
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_466_, v_sz_boxed_473_, v_i_boxed_474_, v_b_469_, v___y_470_, v___y_471_);
lean_dec_ref(v_as_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(size_t v_sz_476_, size_t v_i_477_, lean_object* v_bs_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = lean_usize_dec_lt(v_i_477_, v_sz_476_);
if (v___x_479_ == 0)
{
return v_bs_478_;
}
else
{
lean_object* v_v_480_; lean_object* v_declName_481_; lean_object* v___x_482_; lean_object* v_bs_x27_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; 
v_v_480_ = lean_array_uget_borrowed(v_bs_478_, v_i_477_);
v_declName_481_ = lean_ctor_get(v_v_480_, 3);
lean_inc(v_declName_481_);
v___x_482_ = lean_unsigned_to_nat(0u);
v_bs_x27_483_ = lean_array_uset(v_bs_478_, v_i_477_, v___x_482_);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_add(v_i_477_, v___x_484_);
v___x_486_ = lean_array_uset(v_bs_x27_483_, v_i_477_, v_declName_481_);
v_i_477_ = v___x_485_;
v_bs_478_ = v___x_486_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object* v_sz_488_, lean_object* v_i_489_, lean_object* v_bs_490_){
_start:
{
size_t v_sz_boxed_491_; size_t v_i_boxed_492_; lean_object* v_res_493_; 
v_sz_boxed_491_ = lean_unbox_usize(v_sz_488_);
lean_dec(v_sz_488_);
v_i_boxed_492_ = lean_unbox_usize(v_i_489_);
lean_dec(v_i_489_);
v_res_493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_boxed_491_, v_i_boxed_492_, v_bs_490_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(lean_object* v_a_494_, lean_object* v___x_495_, size_t v_sz_496_, size_t v_i_497_, lean_object* v_bs_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
uint8_t v___x_502_; 
v___x_502_ = lean_usize_dec_lt(v_i_497_, v_sz_496_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec(v___x_495_);
lean_dec_ref(v_a_494_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v_bs_498_);
return v___x_503_;
}
else
{
lean_object* v_v_504_; lean_object* v_ref_505_; uint8_t v_kind_506_; lean_object* v_levelParams_507_; lean_object* v_modifiers_508_; lean_object* v_declName_509_; lean_object* v_binders_510_; lean_object* v_numSectionVars_511_; lean_object* v_type_512_; lean_object* v_value_513_; lean_object* v_termination_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_540_; 
v_v_504_ = lean_array_uget(v_bs_498_, v_i_497_);
v_ref_505_ = lean_ctor_get(v_v_504_, 0);
v_kind_506_ = lean_ctor_get_uint8(v_v_504_, sizeof(void*)*9);
v_levelParams_507_ = lean_ctor_get(v_v_504_, 1);
v_modifiers_508_ = lean_ctor_get(v_v_504_, 2);
v_declName_509_ = lean_ctor_get(v_v_504_, 3);
v_binders_510_ = lean_ctor_get(v_v_504_, 4);
v_numSectionVars_511_ = lean_ctor_get(v_v_504_, 5);
v_type_512_ = lean_ctor_get(v_v_504_, 6);
v_value_513_ = lean_ctor_get(v_v_504_, 7);
v_termination_514_ = lean_ctor_get(v_v_504_, 8);
v_isSharedCheck_540_ = !lean_is_exclusive(v_v_504_);
if (v_isSharedCheck_540_ == 0)
{
v___x_516_ = v_v_504_;
v_isShared_517_ = v_isSharedCheck_540_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_termination_514_);
lean_inc(v_value_513_);
lean_inc(v_type_512_);
lean_inc(v_numSectionVars_511_);
lean_inc(v_binders_510_);
lean_inc(v_declName_509_);
lean_inc(v_modifiers_508_);
lean_inc(v_levelParams_507_);
lean_inc(v_ref_505_);
lean_dec(v_v_504_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_540_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
size_t v_sz_518_; size_t v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_sz_518_ = lean_array_size(v_a_494_);
v___x_519_ = ((size_t)0ULL);
lean_inc_ref(v_a_494_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_518_, v___x_519_, v_a_494_);
lean_inc(v___y_500_);
lean_inc_ref(v___y_499_);
lean_inc(v___x_495_);
v___x_521_ = l_Lean_Meta_unfoldIfArgIsAppOf(v___x_520_, v___x_495_, v_value_513_, v___y_499_, v___y_500_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; lean_object* v_bs_x27_524_; lean_object* v___x_526_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v___x_521_);
v___x_523_ = lean_unsigned_to_nat(0u);
v_bs_x27_524_ = lean_array_uset(v_bs_498_, v_i_497_, v___x_523_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 7, v_a_522_);
v___x_526_ = v___x_516_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_ref_505_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_levelParams_507_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_modifiers_508_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v_declName_509_);
lean_ctor_set(v_reuseFailAlloc_531_, 4, v_binders_510_);
lean_ctor_set(v_reuseFailAlloc_531_, 5, v_numSectionVars_511_);
lean_ctor_set(v_reuseFailAlloc_531_, 6, v_type_512_);
lean_ctor_set(v_reuseFailAlloc_531_, 7, v_a_522_);
lean_ctor_set(v_reuseFailAlloc_531_, 8, v_termination_514_);
lean_ctor_set_uint8(v_reuseFailAlloc_531_, sizeof(void*)*9, v_kind_506_);
v___x_526_ = v_reuseFailAlloc_531_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; 
v___x_527_ = ((size_t)1ULL);
v___x_528_ = lean_usize_add(v_i_497_, v___x_527_);
v___x_529_ = lean_array_uset(v_bs_x27_524_, v_i_497_, v___x_526_);
v_i_497_ = v___x_528_;
v_bs_498_ = v___x_529_;
goto _start;
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_del_object(v___x_516_);
lean_dec_ref(v_termination_514_);
lean_dec_ref(v_type_512_);
lean_dec(v_numSectionVars_511_);
lean_dec(v_binders_510_);
lean_dec(v_declName_509_);
lean_dec_ref(v_modifiers_508_);
lean_dec(v_levelParams_507_);
lean_dec(v_ref_505_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
lean_dec_ref(v_bs_498_);
lean_dec(v___x_495_);
lean_dec_ref(v_a_494_);
v_a_532_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_521_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_521_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg___boxed(lean_object* v_a_541_, lean_object* v___x_542_, lean_object* v_sz_543_, lean_object* v_i_544_, lean_object* v_bs_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
size_t v_sz_boxed_549_; size_t v_i_boxed_550_; lean_object* v_res_551_; 
v_sz_boxed_549_ = lean_unbox_usize(v_sz_543_);
lean_dec(v_sz_543_);
v_i_boxed_550_ = lean_unbox_usize(v_i_544_);
lean_dec(v_i_544_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_541_, v___x_542_, v_sz_boxed_549_, v_i_boxed_550_, v_bs_545_, v___y_546_, v___y_547_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* v_a_552_, size_t v_sz_553_, size_t v___x_554_, lean_object* v___x_555_, lean_object* v___x_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v___x_564_; 
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_a_552_, v_sz_553_, v___x_554_, v___x_555_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; 
lean_dec_ref(v___x_564_);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
lean_inc(v___y_560_);
lean_inc_ref(v___y_559_);
lean_inc_ref(v_a_552_);
v___x_565_ = l_Lean_Elab_getFixedParamPerms(v_a_552_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
lean_dec_ref(v___x_565_);
v___x_567_ = lean_array_get_size(v_a_552_);
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_mk_empty_array_with_capacity(v___x_567_);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
lean_inc(v___y_560_);
lean_inc_ref(v___y_559_);
lean_inc(v_a_566_);
v___x_570_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_566_, v_a_552_, v___x_567_, v___x_568_, v___x_569_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; size_t v_sz_573_; lean_object* v___x_574_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref(v___x_570_);
lean_inc_ref(v_a_552_);
v___x_572_ = l_Array_toSubarray___redArg(v_a_552_, v___x_568_, v___x_567_);
v_sz_573_ = lean_array_size(v_a_571_);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_a_571_, v_sz_573_, v___x_554_, v___x_572_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v___x_575_; lean_object* v_numSectionVars_576_; lean_object* v___x_577_; 
lean_dec_ref(v___x_574_);
v___x_575_ = lean_array_get_borrowed(v___x_556_, v_a_552_, v___x_568_);
v_numSectionVars_576_ = lean_ctor_get(v___x_575_, 5);
lean_inc(v_numSectionVars_576_);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
lean_inc_ref(v_a_552_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_552_, v_numSectionVars_576_, v_sz_553_, v___x_554_, v_a_552_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v_a_578_; lean_object* v___x_579_; 
v_a_578_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_a_578_);
lean_dec_ref(v___x_577_);
lean_inc(v_a_571_);
lean_inc(v_a_566_);
v___x_579_ = l_Lean_Elab_WF_packMutual(v_a_566_, v_a_571_, v_a_578_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_589_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_589_ == 0)
{
v___x_582_ = v___x_579_;
v_isShared_583_ = v_isSharedCheck_589_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_579_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_589_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v_a_571_);
lean_ctor_set(v___x_584_, 1, v_a_580_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_a_566_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 0, v___x_585_);
v___x_587_ = v___x_582_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
}
else
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_a_571_);
lean_dec(v_a_566_);
v_a_590_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_579_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_579_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_a_571_);
lean_dec(v_a_566_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
v_a_598_ = lean_ctor_get(v___x_577_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_577_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_577_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_577_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec(v_a_571_);
lean_dec(v_a_566_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec_ref(v___x_556_);
lean_dec_ref(v_a_552_);
v_a_606_ = lean_ctor_get(v___x_574_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_574_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_574_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_574_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_a_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_621_; 
lean_dec(v_a_566_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___x_556_);
lean_dec_ref(v_a_552_);
v_a_614_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_621_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_621_ == 0)
{
v___x_616_ = v___x_570_;
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_a_614_);
lean_dec(v___x_570_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_621_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_617_ == 0)
{
v___x_619_ = v___x_616_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_a_614_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
}
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___x_556_);
lean_dec_ref(v_a_552_);
v_a_622_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_565_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_565_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_637_; 
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec_ref(v___y_557_);
lean_dec_ref(v___x_556_);
lean_dec_ref(v_a_552_);
v_a_630_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_637_ == 0)
{
v___x_632_ = v___x_564_;
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_564_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_637_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
lean_object* v___x_635_; 
if (v_isShared_633_ == 0)
{
v___x_635_ = v___x_632_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_a_630_);
v___x_635_ = v_reuseFailAlloc_636_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
return v___x_635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object* v_a_638_, lean_object* v_sz_639_, lean_object* v___x_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_){
_start:
{
size_t v_sz_boxed_650_; size_t v___x_48121__boxed_651_; lean_object* v_res_652_; 
v_sz_boxed_650_ = lean_unbox_usize(v_sz_639_);
lean_dec(v_sz_639_);
v___x_48121__boxed_651_ = lean_unbox_usize(v___x_640_);
lean_dec(v___x_640_);
v_res_652_ = l_Lean_Elab_wfRecursion___lam__0(v_a_638_, v_sz_boxed_650_, v___x_48121__boxed_651_, v___x_641_, v___x_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_, v___y_648_);
lean_dec(v___y_644_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* v_snd_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
lean_inc(v___y_659_);
lean_inc_ref(v___y_658_);
v___x_661_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_653_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_ref_662_; uint8_t v_kind_663_; lean_object* v_levelParams_664_; lean_object* v_modifiers_665_; lean_object* v_declName_666_; lean_object* v_binders_667_; lean_object* v_numSectionVars_668_; lean_object* v_type_669_; lean_object* v_value_670_; lean_object* v_termination_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v___x_661_);
v_ref_662_ = lean_ctor_get(v_snd_653_, 0);
v_kind_663_ = lean_ctor_get_uint8(v_snd_653_, sizeof(void*)*9);
v_levelParams_664_ = lean_ctor_get(v_snd_653_, 1);
v_modifiers_665_ = lean_ctor_get(v_snd_653_, 2);
v_declName_666_ = lean_ctor_get(v_snd_653_, 3);
v_binders_667_ = lean_ctor_get(v_snd_653_, 4);
v_numSectionVars_668_ = lean_ctor_get(v_snd_653_, 5);
v_type_669_ = lean_ctor_get(v_snd_653_, 6);
v_value_670_ = lean_ctor_get(v_snd_653_, 7);
v_termination_671_ = lean_ctor_get(v_snd_653_, 8);
v_isSharedCheck_697_ = !lean_is_exclusive(v_snd_653_);
if (v_isSharedCheck_697_ == 0)
{
v___x_673_ = v_snd_653_;
v_isShared_674_ = v_isSharedCheck_697_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_termination_671_);
lean_inc(v_value_670_);
lean_inc(v_type_669_);
lean_inc(v_numSectionVars_668_);
lean_inc(v_binders_667_);
lean_inc(v_declName_666_);
lean_inc(v_modifiers_665_);
lean_inc(v_levelParams_664_);
lean_inc(v_ref_662_);
lean_dec(v_snd_653_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_697_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; 
v___x_675_ = l_Lean_Elab_WF_preprocess(v_value_670_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_688_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_688_ == 0)
{
v___x_678_ = v___x_675_;
v_isShared_679_ = v_isSharedCheck_688_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_675_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_688_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_expr_680_; lean_object* v___x_682_; 
v_expr_680_ = lean_ctor_get(v_a_676_, 0);
lean_inc_ref(v_expr_680_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 7, v_expr_680_);
v___x_682_ = v___x_673_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_ref_662_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_levelParams_664_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_modifiers_665_);
lean_ctor_set(v_reuseFailAlloc_687_, 3, v_declName_666_);
lean_ctor_set(v_reuseFailAlloc_687_, 4, v_binders_667_);
lean_ctor_set(v_reuseFailAlloc_687_, 5, v_numSectionVars_668_);
lean_ctor_set(v_reuseFailAlloc_687_, 6, v_type_669_);
lean_ctor_set(v_reuseFailAlloc_687_, 7, v_expr_680_);
lean_ctor_set(v_reuseFailAlloc_687_, 8, v_termination_671_);
lean_ctor_set_uint8(v_reuseFailAlloc_687_, sizeof(void*)*9, v_kind_663_);
v___x_682_ = v_reuseFailAlloc_687_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v_a_676_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_683_);
v___x_685_ = v___x_678_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
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
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
lean_del_object(v___x_673_);
lean_dec_ref(v_termination_671_);
lean_dec_ref(v_type_669_);
lean_dec(v_numSectionVars_668_);
lean_dec(v_binders_667_);
lean_dec(v_declName_666_);
lean_dec_ref(v_modifiers_665_);
lean_dec(v_levelParams_664_);
lean_dec(v_ref_662_);
v_a_689_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_675_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_675_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
else
{
lean_object* v_a_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_705_; 
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v_snd_653_);
v_a_698_ = lean_ctor_get(v___x_661_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_705_ == 0)
{
v___x_700_ = v___x_661_;
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_a_698_);
lean_dec(v___x_661_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_705_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_703_; 
if (v_isShared_701_ == 0)
{
v___x_703_ = v___x_700_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_a_698_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* v_snd_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Elab_wfRecursion___lam__1(v_snd_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__11(size_t v_sz_715_, size_t v_i_716_, lean_object* v_bs_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = lean_usize_dec_lt(v_i_716_, v_sz_715_);
if (v___x_718_ == 0)
{
return v_bs_717_;
}
else
{
lean_object* v_v_719_; lean_object* v_termination_720_; lean_object* v_decreasingBy_x3f_721_; lean_object* v___x_722_; lean_object* v_bs_x27_723_; size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; 
v_v_719_ = lean_array_uget_borrowed(v_bs_717_, v_i_716_);
v_termination_720_ = lean_ctor_get(v_v_719_, 8);
v_decreasingBy_x3f_721_ = lean_ctor_get(v_termination_720_, 4);
lean_inc(v_decreasingBy_x3f_721_);
v___x_722_ = lean_unsigned_to_nat(0u);
v_bs_x27_723_ = lean_array_uset(v_bs_717_, v_i_716_, v___x_722_);
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_716_, v___x_724_);
v___x_726_ = lean_array_uset(v_bs_x27_723_, v_i_716_, v_decreasingBy_x3f_721_);
v_i_716_ = v___x_725_;
v_bs_717_ = v___x_726_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object* v_sz_728_, lean_object* v_i_729_, lean_object* v_bs_730_){
_start:
{
size_t v_sz_boxed_731_; size_t v_i_boxed_732_; lean_object* v_res_733_; 
v_sz_boxed_731_ = lean_unbox_usize(v_sz_728_);
lean_dec(v_sz_728_);
v_i_boxed_732_ = lean_unbox_usize(v_i_729_);
lean_dec(v_i_729_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__11(v_sz_boxed_731_, v_i_boxed_732_, v_bs_730_);
return v_res_733_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_734_; double v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_float_of_nat(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object* v_cls_739_, lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_ref_746_; lean_object* v___x_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_792_; 
v_ref_746_ = lean_ctor_get(v___y_743_, 5);
v___x_747_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_792_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_792_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_792_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v_traceState_753_; lean_object* v_env_754_; lean_object* v_nextMacroScope_755_; lean_object* v_ngen_756_; lean_object* v_auxDeclNGen_757_; lean_object* v_cache_758_; lean_object* v_messages_759_; lean_object* v_infoState_760_; lean_object* v_snapshotTasks_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_791_; 
v___x_752_ = lean_st_ref_take(v___y_744_);
v_traceState_753_ = lean_ctor_get(v___x_752_, 4);
v_env_754_ = lean_ctor_get(v___x_752_, 0);
v_nextMacroScope_755_ = lean_ctor_get(v___x_752_, 1);
v_ngen_756_ = lean_ctor_get(v___x_752_, 2);
v_auxDeclNGen_757_ = lean_ctor_get(v___x_752_, 3);
v_cache_758_ = lean_ctor_get(v___x_752_, 5);
v_messages_759_ = lean_ctor_get(v___x_752_, 6);
v_infoState_760_ = lean_ctor_get(v___x_752_, 7);
v_snapshotTasks_761_ = lean_ctor_get(v___x_752_, 8);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_791_ == 0)
{
v___x_763_ = v___x_752_;
v_isShared_764_ = v_isSharedCheck_791_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_snapshotTasks_761_);
lean_inc(v_infoState_760_);
lean_inc(v_messages_759_);
lean_inc(v_cache_758_);
lean_inc(v_traceState_753_);
lean_inc(v_auxDeclNGen_757_);
lean_inc(v_ngen_756_);
lean_inc(v_nextMacroScope_755_);
lean_inc(v_env_754_);
lean_dec(v___x_752_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_791_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
uint64_t v_tid_765_; lean_object* v_traces_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_790_; 
v_tid_765_ = lean_ctor_get_uint64(v_traceState_753_, sizeof(void*)*1);
v_traces_766_ = lean_ctor_get(v_traceState_753_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_traceState_753_);
if (v_isSharedCheck_790_ == 0)
{
v___x_768_ = v_traceState_753_;
v_isShared_769_ = v_isSharedCheck_790_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_traces_766_);
lean_dec(v_traceState_753_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_790_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_770_; double v___x_771_; uint8_t v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_770_ = lean_box(0);
v___x_771_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__0);
v___x_772_ = 0;
v___x_773_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__1));
v___x_774_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_774_, 0, v_cls_739_);
lean_ctor_set(v___x_774_, 1, v___x_770_);
lean_ctor_set(v___x_774_, 2, v___x_773_);
lean_ctor_set_float(v___x_774_, sizeof(void*)*3, v___x_771_);
lean_ctor_set_float(v___x_774_, sizeof(void*)*3 + 8, v___x_771_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*3 + 16, v___x_772_);
v___x_775_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__2));
v___x_776_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
lean_ctor_set(v___x_776_, 1, v_a_748_);
lean_ctor_set(v___x_776_, 2, v___x_775_);
lean_inc(v_ref_746_);
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_ref_746_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
v___x_778_ = l_Lean_PersistentArray_push___redArg(v_traces_766_, v___x_777_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_778_);
v___x_780_ = v___x_768_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_778_);
lean_ctor_set_uint64(v_reuseFailAlloc_789_, sizeof(void*)*1, v_tid_765_);
v___x_780_ = v_reuseFailAlloc_789_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_782_; 
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 4, v___x_780_);
v___x_782_ = v___x_763_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_env_754_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_nextMacroScope_755_);
lean_ctor_set(v_reuseFailAlloc_788_, 2, v_ngen_756_);
lean_ctor_set(v_reuseFailAlloc_788_, 3, v_auxDeclNGen_757_);
lean_ctor_set(v_reuseFailAlloc_788_, 4, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_788_, 5, v_cache_758_);
lean_ctor_set(v_reuseFailAlloc_788_, 6, v_messages_759_);
lean_ctor_set(v_reuseFailAlloc_788_, 7, v_infoState_760_);
lean_ctor_set(v_reuseFailAlloc_788_, 8, v_snapshotTasks_761_);
v___x_782_ = v_reuseFailAlloc_788_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_783_ = lean_st_ref_set(v___y_744_, v___x_782_);
v___x_784_ = lean_box(0);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_784_);
v___x_786_ = v___x_750_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object* v_cls_793_, lean_object* v_msg_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_cls_793_, v_msg_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_);
lean_dec(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_800_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0(uint8_t v___y_808_, uint8_t v_suppressElabErrors_809_, lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_810_) == 1)
{
lean_object* v_pre_811_; 
v_pre_811_ = lean_ctor_get(v_x_810_, 0);
switch(lean_obj_tag(v_pre_811_))
{
case 1:
{
lean_object* v_pre_812_; 
v_pre_812_ = lean_ctor_get(v_pre_811_, 0);
switch(lean_obj_tag(v_pre_812_))
{
case 0:
{
lean_object* v_str_813_; lean_object* v_str_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_str_813_ = lean_ctor_get(v_x_810_, 1);
v_str_814_ = lean_ctor_get(v_pre_811_, 1);
v___x_815_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__0));
v___x_816_ = lean_string_dec_eq(v_str_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__1));
v___x_818_ = lean_string_dec_eq(v_str_814_, v___x_817_);
if (v___x_818_ == 0)
{
return v___y_808_;
}
else
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__2));
v___x_820_ = lean_string_dec_eq(v_str_813_, v___x_819_);
if (v___x_820_ == 0)
{
return v___y_808_;
}
else
{
return v_suppressElabErrors_809_;
}
}
}
else
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__3));
v___x_822_ = lean_string_dec_eq(v_str_813_, v___x_821_);
if (v___x_822_ == 0)
{
return v___y_808_;
}
else
{
return v_suppressElabErrors_809_;
}
}
}
case 1:
{
lean_object* v_pre_823_; 
v_pre_823_ = lean_ctor_get(v_pre_812_, 0);
if (lean_obj_tag(v_pre_823_) == 0)
{
lean_object* v_str_824_; lean_object* v_str_825_; lean_object* v_str_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_str_824_ = lean_ctor_get(v_x_810_, 1);
v_str_825_ = lean_ctor_get(v_pre_811_, 1);
v_str_826_ = lean_ctor_get(v_pre_812_, 1);
v___x_827_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__4));
v___x_828_ = lean_string_dec_eq(v_str_826_, v___x_827_);
if (v___x_828_ == 0)
{
return v___y_808_;
}
else
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__5));
v___x_830_ = lean_string_dec_eq(v_str_825_, v___x_829_);
if (v___x_830_ == 0)
{
return v___y_808_;
}
else
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___closed__6));
v___x_832_ = lean_string_dec_eq(v_str_824_, v___x_831_);
if (v___x_832_ == 0)
{
return v___y_808_;
}
else
{
return v_suppressElabErrors_809_;
}
}
}
}
else
{
return v___y_808_;
}
}
default: 
{
return v___y_808_;
}
}
}
case 0:
{
lean_object* v_str_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_str_833_ = lean_ctor_get(v_x_810_, 1);
v___x_834_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg___closed__0));
v___x_835_ = lean_string_dec_eq(v_str_833_, v___x_834_);
if (v___x_835_ == 0)
{
return v___y_808_;
}
else
{
return v_suppressElabErrors_809_;
}
}
default: 
{
return v___y_808_;
}
}
}
else
{
return v___y_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___boxed(lean_object* v___y_836_, lean_object* v_suppressElabErrors_837_, lean_object* v_x_838_){
_start:
{
uint8_t v___y_48519__boxed_839_; uint8_t v_suppressElabErrors_boxed_840_; uint8_t v_res_841_; lean_object* v_r_842_; 
v___y_48519__boxed_839_ = lean_unbox(v___y_836_);
v_suppressElabErrors_boxed_840_ = lean_unbox(v_suppressElabErrors_837_);
v_res_841_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0(v___y_48519__boxed_839_, v_suppressElabErrors_boxed_840_, v_x_838_);
lean_dec(v_x_838_);
v_r_842_ = lean_box(v_res_841_);
return v_r_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg(lean_object* v_ref_843_, lean_object* v_msgData_844_, uint8_t v_severity_845_, uint8_t v_isSilent_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; uint8_t v___y_856_; lean_object* v___y_857_; uint8_t v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_889_; lean_object* v___y_890_; lean_object* v___y_891_; lean_object* v___y_892_; uint8_t v___y_893_; uint8_t v___y_894_; uint8_t v___y_895_; lean_object* v___y_896_; lean_object* v___y_914_; lean_object* v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; uint8_t v___y_918_; uint8_t v___y_919_; uint8_t v___y_920_; lean_object* v___y_921_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; uint8_t v___y_929_; uint8_t v___y_930_; uint8_t v___y_931_; uint8_t v___x_936_; lean_object* v___y_938_; lean_object* v___y_939_; lean_object* v___y_940_; lean_object* v___y_941_; uint8_t v___y_942_; uint8_t v___y_943_; uint8_t v___y_944_; uint8_t v___y_946_; uint8_t v___x_961_; 
v___x_936_ = 2;
v___x_961_ = l_Lean_instBEqMessageSeverity_beq(v_severity_845_, v___x_936_);
if (v___x_961_ == 0)
{
v___y_946_ = v___x_961_;
goto v___jp_945_;
}
else
{
uint8_t v___x_962_; 
lean_inc_ref(v_msgData_844_);
v___x_962_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_844_);
v___y_946_ = v___x_962_;
goto v___jp_945_;
}
v___jp_852_:
{
lean_object* v___x_862_; lean_object* v_currNamespace_863_; lean_object* v_openDecls_864_; lean_object* v_env_865_; lean_object* v_nextMacroScope_866_; lean_object* v_ngen_867_; lean_object* v_auxDeclNGen_868_; lean_object* v_traceState_869_; lean_object* v_cache_870_; lean_object* v_messages_871_; lean_object* v_infoState_872_; lean_object* v_snapshotTasks_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_887_; 
v___x_862_ = lean_st_ref_take(v___y_861_);
v_currNamespace_863_ = lean_ctor_get(v___y_860_, 6);
lean_inc(v_currNamespace_863_);
v_openDecls_864_ = lean_ctor_get(v___y_860_, 7);
lean_inc(v_openDecls_864_);
lean_dec_ref(v___y_860_);
v_env_865_ = lean_ctor_get(v___x_862_, 0);
v_nextMacroScope_866_ = lean_ctor_get(v___x_862_, 1);
v_ngen_867_ = lean_ctor_get(v___x_862_, 2);
v_auxDeclNGen_868_ = lean_ctor_get(v___x_862_, 3);
v_traceState_869_ = lean_ctor_get(v___x_862_, 4);
v_cache_870_ = lean_ctor_get(v___x_862_, 5);
v_messages_871_ = lean_ctor_get(v___x_862_, 6);
v_infoState_872_ = lean_ctor_get(v___x_862_, 7);
v_snapshotTasks_873_ = lean_ctor_get(v___x_862_, 8);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_887_ == 0)
{
v___x_875_ = v___x_862_;
v_isShared_876_ = v_isSharedCheck_887_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_snapshotTasks_873_);
lean_inc(v_infoState_872_);
lean_inc(v_messages_871_);
lean_inc(v_cache_870_);
lean_inc(v_traceState_869_);
lean_inc(v_auxDeclNGen_868_);
lean_inc(v_ngen_867_);
lean_inc(v_nextMacroScope_866_);
lean_inc(v_env_865_);
lean_dec(v___x_862_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_887_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_877_, 0, v_currNamespace_863_);
lean_ctor_set(v___x_877_, 1, v_openDecls_864_);
v___x_878_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v___y_857_);
v___x_879_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_879_, 0, v___y_854_);
lean_ctor_set(v___x_879_, 1, v___y_855_);
lean_ctor_set(v___x_879_, 2, v___y_859_);
lean_ctor_set(v___x_879_, 3, v___y_853_);
lean_ctor_set(v___x_879_, 4, v___x_878_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*5, v___y_858_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*5 + 1, v___y_856_);
lean_ctor_set_uint8(v___x_879_, sizeof(void*)*5 + 2, v_isSilent_846_);
v___x_880_ = l_Lean_MessageLog_add(v___x_879_, v_messages_871_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 6, v___x_880_);
v___x_882_ = v___x_875_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_env_865_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_nextMacroScope_866_);
lean_ctor_set(v_reuseFailAlloc_886_, 2, v_ngen_867_);
lean_ctor_set(v_reuseFailAlloc_886_, 3, v_auxDeclNGen_868_);
lean_ctor_set(v_reuseFailAlloc_886_, 4, v_traceState_869_);
lean_ctor_set(v_reuseFailAlloc_886_, 5, v_cache_870_);
lean_ctor_set(v_reuseFailAlloc_886_, 6, v___x_880_);
lean_ctor_set(v_reuseFailAlloc_886_, 7, v_infoState_872_);
lean_ctor_set(v_reuseFailAlloc_886_, 8, v_snapshotTasks_873_);
v___x_882_ = v_reuseFailAlloc_886_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_883_ = lean_st_ref_set(v___y_861_, v___x_882_);
v___x_884_ = lean_box(0);
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
return v___x_885_;
}
}
}
v___jp_888_:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_a_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_912_; 
v___x_897_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_844_);
v___x_898_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_897_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
v_a_899_ = lean_ctor_get(v___x_898_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_898_);
if (v_isSharedCheck_912_ == 0)
{
v___x_901_ = v___x_898_;
v_isShared_902_ = v_isSharedCheck_912_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_a_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_912_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
lean_inc_ref(v___y_891_);
v___x_903_ = l_Lean_FileMap_toPosition(v___y_891_, v___y_890_);
lean_dec(v___y_890_);
v___x_904_ = l_Lean_FileMap_toPosition(v___y_891_, v___y_896_);
lean_dec(v___y_896_);
v___x_905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
v___x_906_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg___closed__1));
if (v___y_894_ == 0)
{
lean_del_object(v___x_901_);
lean_dec_ref(v___y_889_);
v___y_853_ = v___x_906_;
v___y_854_ = v___y_892_;
v___y_855_ = v___x_903_;
v___y_856_ = v___y_893_;
v___y_857_ = v_a_899_;
v___y_858_ = v___y_895_;
v___y_859_ = v___x_905_;
v___y_860_ = v___y_849_;
v___y_861_ = v___y_850_;
goto v___jp_852_;
}
else
{
uint8_t v___x_907_; 
lean_inc(v_a_899_);
v___x_907_ = l_Lean_MessageData_hasTag(v___y_889_, v_a_899_);
if (v___x_907_ == 0)
{
lean_object* v___x_908_; lean_object* v___x_910_; 
lean_dec_ref(v___x_905_);
lean_dec_ref(v___x_903_);
lean_dec(v_a_899_);
lean_dec_ref(v___y_892_);
lean_dec_ref(v___y_849_);
v___x_908_ = lean_box(0);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 0, v___x_908_);
v___x_910_ = v___x_901_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_908_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
else
{
lean_del_object(v___x_901_);
v___y_853_ = v___x_906_;
v___y_854_ = v___y_892_;
v___y_855_ = v___x_903_;
v___y_856_ = v___y_893_;
v___y_857_ = v_a_899_;
v___y_858_ = v___y_895_;
v___y_859_ = v___x_905_;
v___y_860_ = v___y_849_;
v___y_861_ = v___y_850_;
goto v___jp_852_;
}
}
}
}
v___jp_913_:
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Syntax_getTailPos_x3f(v___y_917_, v___y_920_);
lean_dec(v___y_917_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_inc(v___y_921_);
v___y_889_ = v___y_914_;
v___y_890_ = v___y_921_;
v___y_891_ = v___y_915_;
v___y_892_ = v___y_916_;
v___y_893_ = v___y_918_;
v___y_894_ = v___y_919_;
v___y_895_ = v___y_920_;
v___y_896_ = v___y_921_;
goto v___jp_888_;
}
else
{
lean_object* v_val_923_; 
v_val_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_val_923_);
lean_dec_ref(v___x_922_);
v___y_889_ = v___y_914_;
v___y_890_ = v___y_921_;
v___y_891_ = v___y_915_;
v___y_892_ = v___y_916_;
v___y_893_ = v___y_918_;
v___y_894_ = v___y_919_;
v___y_895_ = v___y_920_;
v___y_896_ = v_val_923_;
goto v___jp_888_;
}
}
v___jp_924_:
{
lean_object* v_ref_932_; lean_object* v___x_933_; 
v_ref_932_ = l_Lean_replaceRef(v_ref_843_, v___y_928_);
lean_dec(v___y_928_);
v___x_933_ = l_Lean_Syntax_getPos_x3f(v_ref_932_, v___y_930_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; 
v___x_934_ = lean_unsigned_to_nat(0u);
v___y_914_ = v___y_925_;
v___y_915_ = v___y_926_;
v___y_916_ = v___y_927_;
v___y_917_ = v_ref_932_;
v___y_918_ = v___y_931_;
v___y_919_ = v___y_929_;
v___y_920_ = v___y_930_;
v___y_921_ = v___x_934_;
goto v___jp_913_;
}
else
{
lean_object* v_val_935_; 
v_val_935_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_val_935_);
lean_dec_ref(v___x_933_);
v___y_914_ = v___y_925_;
v___y_915_ = v___y_926_;
v___y_916_ = v___y_927_;
v___y_917_ = v_ref_932_;
v___y_918_ = v___y_931_;
v___y_919_ = v___y_929_;
v___y_920_ = v___y_930_;
v___y_921_ = v_val_935_;
goto v___jp_913_;
}
}
v___jp_937_:
{
if (v___y_944_ == 0)
{
v___y_925_ = v___y_941_;
v___y_926_ = v___y_938_;
v___y_927_ = v___y_940_;
v___y_928_ = v___y_939_;
v___y_929_ = v___y_942_;
v___y_930_ = v___y_943_;
v___y_931_ = v_severity_845_;
goto v___jp_924_;
}
else
{
v___y_925_ = v___y_941_;
v___y_926_ = v___y_938_;
v___y_927_ = v___y_940_;
v___y_928_ = v___y_939_;
v___y_929_ = v___y_942_;
v___y_930_ = v___y_943_;
v___y_931_ = v___x_936_;
goto v___jp_924_;
}
}
v___jp_945_:
{
if (v___y_946_ == 0)
{
lean_object* v_fileName_947_; lean_object* v_fileMap_948_; lean_object* v_options_949_; lean_object* v_ref_950_; uint8_t v_suppressElabErrors_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___f_954_; uint8_t v___x_955_; uint8_t v___x_956_; 
v_fileName_947_ = lean_ctor_get(v___y_849_, 0);
v_fileMap_948_ = lean_ctor_get(v___y_849_, 1);
v_options_949_ = lean_ctor_get(v___y_849_, 2);
v_ref_950_ = lean_ctor_get(v___y_849_, 5);
v_suppressElabErrors_951_ = lean_ctor_get_uint8(v___y_849_, sizeof(void*)*14 + 1);
v___x_952_ = lean_box(v___y_946_);
v___x_953_ = lean_box(v_suppressElabErrors_951_);
v___f_954_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_954_, 0, v___x_952_);
lean_closure_set(v___f_954_, 1, v___x_953_);
v___x_955_ = 1;
v___x_956_ = l_Lean_instBEqMessageSeverity_beq(v_severity_845_, v___x_955_);
if (v___x_956_ == 0)
{
lean_inc_ref(v_fileName_947_);
lean_inc(v_ref_950_);
lean_inc_ref(v_fileMap_948_);
v___y_938_ = v_fileMap_948_;
v___y_939_ = v_ref_950_;
v___y_940_ = v_fileName_947_;
v___y_941_ = v___f_954_;
v___y_942_ = v_suppressElabErrors_951_;
v___y_943_ = v___y_946_;
v___y_944_ = v___x_956_;
goto v___jp_937_;
}
else
{
lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_957_ = l_Lean_warningAsError;
v___x_958_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_options_949_, v___x_957_);
lean_inc_ref(v_fileName_947_);
lean_inc(v_ref_950_);
lean_inc_ref(v_fileMap_948_);
v___y_938_ = v_fileMap_948_;
v___y_939_ = v_ref_950_;
v___y_940_ = v_fileName_947_;
v___y_941_ = v___f_954_;
v___y_942_ = v_suppressElabErrors_951_;
v___y_943_ = v___y_946_;
v___y_944_ = v___x_958_;
goto v___jp_937_;
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec_ref(v___y_849_);
lean_dec_ref(v_msgData_844_);
v___x_959_ = lean_box(0);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg___boxed(lean_object* v_ref_963_, lean_object* v_msgData_964_, lean_object* v_severity_965_, lean_object* v_isSilent_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
uint8_t v_severity_boxed_972_; uint8_t v_isSilent_boxed_973_; lean_object* v_res_974_; 
v_severity_boxed_972_ = lean_unbox(v_severity_965_);
v_isSilent_boxed_973_ = lean_unbox(v_isSilent_966_);
v_res_974_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg(v_ref_963_, v_msgData_964_, v_severity_boxed_972_, v_isSilent_boxed_973_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
lean_dec(v___y_970_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v_ref_963_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v_ref_975_, lean_object* v_msgData_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
uint8_t v___x_984_; uint8_t v___x_985_; lean_object* v___x_986_; 
v___x_984_ = 1;
v___x_985_ = 0;
v___x_986_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg(v_ref_975_, v_msgData_976_, v___x_984_, v___x_985_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v_ref_987_, lean_object* v_msgData_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12(v_ref_987_, v_msgData_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v_ref_987_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v_as_1005_, size_t v_i_1006_, size_t v_stop_1007_, lean_object* v_b_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_a_1017_; uint8_t v___x_1021_; 
v___x_1021_ = lean_usize_dec_eq(v_i_1006_, v_stop_1007_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v_name_1023_; lean_object* v_stx_1024_; uint8_t v___y_1026_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1022_ = lean_array_uget_borrowed(v_as_1005_, v_i_1006_);
v_name_1023_ = lean_ctor_get(v___x_1022_, 0);
v_stx_1024_ = lean_ctor_get(v___x_1022_, 1);
v___x_1036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__3));
v___x_1037_ = lean_name_eq(v_name_1023_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; uint8_t v___x_1039_; 
v___x_1038_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__5));
v___x_1039_ = lean_name_eq(v_name_1023_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_box(0);
v_a_1017_ = v___x_1040_;
goto v___jp_1016_;
}
else
{
v___y_1026_ = v___x_1039_;
goto v___jp_1025_;
}
}
else
{
v___y_1026_ = v___x_1037_;
goto v___jp_1025_;
}
v___jp_1025_:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1027_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__0));
lean_inc(v_name_1023_);
v___x_1028_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1023_, v___y_1026_);
v___x_1029_ = lean_string_append(v___x_1027_, v___x_1028_);
lean_dec_ref(v___x_1028_);
v___x_1030_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___closed__1));
v___x_1031_ = lean_string_append(v___x_1029_, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
v___x_1033_ = l_Lean_MessageData_ofFormat(v___x_1032_);
lean_inc_ref(v___y_1013_);
v___x_1034_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12(v_stx_1024_, v___x_1033_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_object* v_a_1035_; 
v_a_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_a_1035_);
lean_dec_ref(v___x_1034_);
v_a_1017_ = v_a_1035_;
goto v___jp_1016_;
}
else
{
lean_dec_ref(v___y_1013_);
return v___x_1034_;
}
}
}
else
{
lean_object* v___x_1041_; 
lean_dec_ref(v___y_1013_);
v___x_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_b_1008_);
return v___x_1041_;
}
v___jp_1016_:
{
size_t v___x_1018_; size_t v___x_1019_; 
v___x_1018_ = ((size_t)1ULL);
v___x_1019_ = lean_usize_add(v_i_1006_, v___x_1018_);
v_i_1006_ = v___x_1019_;
v_b_1008_ = v_a_1017_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v_as_1042_, lean_object* v_i_1043_, lean_object* v_stop_1044_, lean_object* v_b_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
size_t v_i_boxed_1053_; size_t v_stop_boxed_1054_; lean_object* v_res_1055_; 
v_i_boxed_1053_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_stop_boxed_1054_ = lean_unbox_usize(v_stop_1044_);
lean_dec(v_stop_1044_);
v_res_1055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_as_1042_, v_i_boxed_1053_, v_stop_boxed_1054_, v_b_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec_ref(v_as_1042_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v_as_1056_, size_t v_i_1057_, size_t v_stop_1058_, lean_object* v_b_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_a_1068_; lean_object* v___y_1073_; uint8_t v___x_1075_; 
v___x_1075_ = lean_usize_dec_eq(v_i_1057_, v_stop_1058_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v_modifiers_1077_; lean_object* v_attrs_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1076_ = lean_array_uget_borrowed(v_as_1056_, v_i_1057_);
v_modifiers_1077_ = lean_ctor_get(v___x_1076_, 2);
v_attrs_1078_ = lean_ctor_get(v_modifiers_1077_, 2);
v___x_1079_ = lean_unsigned_to_nat(0u);
v___x_1080_ = lean_array_get_size(v_attrs_1078_);
v___x_1081_ = lean_box(0);
v___x_1082_ = lean_nat_dec_lt(v___x_1079_, v___x_1080_);
if (v___x_1082_ == 0)
{
v_a_1068_ = v___x_1081_;
goto v___jp_1067_;
}
else
{
uint8_t v___x_1083_; 
v___x_1083_ = lean_nat_dec_le(v___x_1080_, v___x_1080_);
if (v___x_1083_ == 0)
{
if (v___x_1082_ == 0)
{
v_a_1068_ = v___x_1081_;
goto v___jp_1067_;
}
else
{
size_t v___x_1084_; size_t v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = ((size_t)0ULL);
v___x_1085_ = lean_usize_of_nat(v___x_1080_);
lean_inc_ref(v___y_1064_);
v___x_1086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_attrs_1078_, v___x_1084_, v___x_1085_, v___x_1081_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
v___y_1073_ = v___x_1086_;
goto v___jp_1072_;
}
}
else
{
size_t v___x_1087_; size_t v___x_1088_; lean_object* v___x_1089_; 
v___x_1087_ = ((size_t)0ULL);
v___x_1088_ = lean_usize_of_nat(v___x_1080_);
lean_inc_ref(v___y_1064_);
v___x_1089_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_attrs_1078_, v___x_1087_, v___x_1088_, v___x_1081_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
v___y_1073_ = v___x_1089_;
goto v___jp_1072_;
}
}
}
else
{
lean_object* v___x_1090_; 
lean_dec_ref(v___y_1064_);
v___x_1090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1090_, 0, v_b_1059_);
return v___x_1090_;
}
v___jp_1067_:
{
size_t v___x_1069_; size_t v___x_1070_; 
v___x_1069_ = ((size_t)1ULL);
v___x_1070_ = lean_usize_add(v_i_1057_, v___x_1069_);
v_i_1057_ = v___x_1070_;
v_b_1059_ = v_a_1068_;
goto _start;
}
v___jp_1072_:
{
if (lean_obj_tag(v___y_1073_) == 0)
{
lean_object* v_a_1074_; 
v_a_1074_ = lean_ctor_get(v___y_1073_, 0);
lean_inc(v_a_1074_);
lean_dec_ref(v___y_1073_);
v_a_1068_ = v_a_1074_;
goto v___jp_1067_;
}
else
{
lean_dec_ref(v___y_1064_);
return v___y_1073_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v_as_1091_, lean_object* v_i_1092_, lean_object* v_stop_1093_, lean_object* v_b_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
size_t v_i_boxed_1102_; size_t v_stop_boxed_1103_; lean_object* v_res_1104_; 
v_i_boxed_1102_ = lean_unbox_usize(v_i_1092_);
lean_dec(v_i_1092_);
v_stop_boxed_1103_ = lean_unbox_usize(v_stop_1093_);
lean_dec(v_stop_1093_);
v_res_1104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14(v_as_1091_, v_i_boxed_1102_, v_stop_boxed_1103_, v_b_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec_ref(v_as_1091_);
return v_res_1104_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__0));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* v___x_1108_, lean_object* v_fst_1109_, lean_object* v_snd_1110_, size_t v_sz_1111_, size_t v___x_1112_, lean_object* v_a_1113_, lean_object* v_fixedArgs_1114_, lean_object* v_fst_1115_, lean_object* v___x_1116_, lean_object* v___x_1117_, lean_object* v_wfRel_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___y_1127_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___y_1130_; lean_object* v___y_1131_; lean_object* v___y_1132_; lean_object* v___y_1133_; lean_object* v_a_1134_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; lean_object* v___y_1149_; lean_object* v___y_1150_; lean_object* v___y_1151_; lean_object* v___y_1152_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___x_1283_; lean_object* v_a_1284_; uint8_t v___x_1285_; 
lean_inc(v___x_1108_);
v___x_1283_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1108_, v___y_1123_);
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = lean_unbox(v_a_1284_);
lean_dec(v_a_1284_);
if (v___x_1285_ == 0)
{
lean_dec(v___x_1108_);
v___y_1259_ = v___y_1119_;
v___y_1260_ = v___y_1120_;
v___y_1261_ = v___y_1121_;
v___y_1262_ = v___y_1122_;
v___y_1263_ = v___y_1123_;
v___y_1264_ = v___y_1124_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__2___closed__1, &l_Lean_Elab_wfRecursion___lam__2___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__2___closed__1);
lean_inc_ref(v_wfRel_1118_);
v___x_1287_ = l_Lean_MessageData_ofExpr(v_wfRel_1118_);
v___x_1288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1286_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v___x_1108_, v___x_1288_, v___y_1121_, v___y_1122_, v___y_1123_, v___y_1124_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_dec_ref(v___x_1289_);
v___y_1259_ = v___y_1119_;
v___y_1260_ = v___y_1120_;
v___y_1261_ = v___y_1121_;
v___y_1262_ = v___y_1122_;
v___y_1263_ = v___y_1123_;
v___y_1264_ = v___y_1124_;
goto v___jp_1258_;
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec(v___y_1124_);
lean_dec_ref(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec_ref(v___y_1121_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec_ref(v_wfRel_1118_);
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_fst_1115_);
lean_dec_ref(v_fixedArgs_1114_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_fst_1109_);
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
v___jp_1126_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec_ref(v___y_1133_);
lean_dec_ref(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v___y_1130_);
v___x_1135_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg(v___y_1127_, v___y_1128_, v___y_1129_);
lean_dec(v___y_1129_);
lean_dec(v___y_1128_);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v___x_1135_, 0);
lean_dec(v_unused_1143_);
v___x_1137_ = v___x_1135_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_dec(v___x_1135_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 1);
lean_ctor_set(v___x_1137_, 0, v_a_1134_);
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1134_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
v___jp_1144_:
{
if (lean_obj_tag(v___y_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v_env_1156_; lean_object* v___x_1157_; 
lean_dec_ref(v___y_1151_);
lean_dec_ref(v___y_1149_);
lean_dec(v___y_1147_);
v_a_1153_ = lean_ctor_get(v___y_1152_, 0);
lean_inc(v_a_1153_);
lean_dec_ref(v___y_1152_);
v___x_1154_ = lean_st_ref_get(v___y_1148_);
v___x_1155_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg(v___y_1145_, v___y_1146_, v___y_1148_);
lean_dec_ref(v___x_1155_);
v_env_1156_ = lean_ctor_get(v___x_1154_, 0);
lean_inc_ref(v_env_1156_);
lean_dec(v___x_1154_);
lean_inc(v___y_1148_);
lean_inc_ref(v_env_1156_);
v___x_1157_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1156_, v_a_1153_, v___y_1150_, v___y_1148_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1217_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1160_ = v___x_1157_;
v_isShared_1161_ = v_isSharedCheck_1217_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1157_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1217_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v_env_1163_; lean_object* v_nextMacroScope_1164_; lean_object* v_ngen_1165_; lean_object* v_auxDeclNGen_1166_; lean_object* v_traceState_1167_; lean_object* v_messages_1168_; lean_object* v_infoState_1169_; lean_object* v_snapshotTasks_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1215_; 
v___x_1162_ = lean_st_ref_take(v___y_1148_);
v_env_1163_ = lean_ctor_get(v___x_1162_, 0);
v_nextMacroScope_1164_ = lean_ctor_get(v___x_1162_, 1);
v_ngen_1165_ = lean_ctor_get(v___x_1162_, 2);
v_auxDeclNGen_1166_ = lean_ctor_get(v___x_1162_, 3);
v_traceState_1167_ = lean_ctor_get(v___x_1162_, 4);
v_messages_1168_ = lean_ctor_get(v___x_1162_, 6);
v_infoState_1169_ = lean_ctor_get(v___x_1162_, 7);
v_snapshotTasks_1170_ = lean_ctor_get(v___x_1162_, 8);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v___x_1162_, 5);
lean_dec(v_unused_1216_);
v___x_1172_ = v___x_1162_;
v_isShared_1173_ = v_isSharedCheck_1215_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_snapshotTasks_1170_);
lean_inc(v_infoState_1169_);
lean_inc(v_messages_1168_);
lean_inc(v_traceState_1167_);
lean_inc(v_auxDeclNGen_1166_);
lean_inc(v_ngen_1165_);
lean_inc(v_nextMacroScope_1164_);
lean_inc(v_env_1163_);
lean_dec(v___x_1162_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1215_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1174_ = l_Lean_copyExtraModUses(v_env_1156_, v_env_1163_);
v___x_1175_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 5, v___x_1175_);
lean_ctor_set(v___x_1172_, 0, v___x_1174_);
v___x_1177_ = v___x_1172_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1214_, 1, v_nextMacroScope_1164_);
lean_ctor_set(v_reuseFailAlloc_1214_, 2, v_ngen_1165_);
lean_ctor_set(v_reuseFailAlloc_1214_, 3, v_auxDeclNGen_1166_);
lean_ctor_set(v_reuseFailAlloc_1214_, 4, v_traceState_1167_);
lean_ctor_set(v_reuseFailAlloc_1214_, 5, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1214_, 6, v_messages_1168_);
lean_ctor_set(v_reuseFailAlloc_1214_, 7, v_infoState_1169_);
lean_ctor_set(v_reuseFailAlloc_1214_, 8, v_snapshotTasks_1170_);
v___x_1177_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v_mctx_1180_; lean_object* v_zetaDeltaFVarIds_1181_; lean_object* v_postponed_1182_; lean_object* v_diag_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1212_; 
v___x_1178_ = lean_st_ref_set(v___y_1148_, v___x_1177_);
lean_dec(v___y_1148_);
v___x_1179_ = lean_st_ref_take(v___y_1146_);
v_mctx_1180_ = lean_ctor_get(v___x_1179_, 0);
v_zetaDeltaFVarIds_1181_ = lean_ctor_get(v___x_1179_, 2);
v_postponed_1182_ = lean_ctor_get(v___x_1179_, 3);
v_diag_1183_ = lean_ctor_get(v___x_1179_, 4);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1212_ == 0)
{
lean_object* v_unused_1213_; 
v_unused_1213_ = lean_ctor_get(v___x_1179_, 1);
lean_dec(v_unused_1213_);
v___x_1185_ = v___x_1179_;
v_isShared_1186_ = v_isSharedCheck_1212_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_diag_1183_);
lean_inc(v_postponed_1182_);
lean_inc(v_zetaDeltaFVarIds_1181_);
lean_inc(v_mctx_1180_);
lean_dec(v___x_1179_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1212_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1187_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1187_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_mctx_1180_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1211_, 2, v_zetaDeltaFVarIds_1181_);
lean_ctor_set(v_reuseFailAlloc_1211_, 3, v_postponed_1182_);
lean_ctor_set(v_reuseFailAlloc_1211_, 4, v_diag_1183_);
v___x_1189_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; lean_object* v_ref_1191_; uint8_t v_kind_1192_; lean_object* v_levelParams_1193_; lean_object* v_modifiers_1194_; lean_object* v_declName_1195_; lean_object* v_binders_1196_; lean_object* v_numSectionVars_1197_; lean_object* v_type_1198_; lean_object* v_termination_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1209_; 
v___x_1190_ = lean_st_ref_set(v___y_1146_, v___x_1189_);
lean_dec(v___y_1146_);
v_ref_1191_ = lean_ctor_get(v_fst_1109_, 0);
v_kind_1192_ = lean_ctor_get_uint8(v_fst_1109_, sizeof(void*)*9);
v_levelParams_1193_ = lean_ctor_get(v_fst_1109_, 1);
v_modifiers_1194_ = lean_ctor_get(v_fst_1109_, 2);
v_declName_1195_ = lean_ctor_get(v_fst_1109_, 3);
v_binders_1196_ = lean_ctor_get(v_fst_1109_, 4);
v_numSectionVars_1197_ = lean_ctor_get(v_fst_1109_, 5);
v_type_1198_ = lean_ctor_get(v_fst_1109_, 6);
v_termination_1199_ = lean_ctor_get(v_fst_1109_, 8);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_fst_1109_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v_fst_1109_, 7);
lean_dec(v_unused_1210_);
v___x_1201_ = v_fst_1109_;
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_termination_1199_);
lean_inc(v_type_1198_);
lean_inc(v_numSectionVars_1197_);
lean_inc(v_binders_1196_);
lean_inc(v_declName_1195_);
lean_inc(v_modifiers_1194_);
lean_inc(v_levelParams_1193_);
lean_inc(v_ref_1191_);
lean_dec(v_fst_1109_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 7, v_a_1158_);
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_ref_1191_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_levelParams_1193_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_modifiers_1194_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_declName_1195_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_binders_1196_);
lean_ctor_set(v_reuseFailAlloc_1208_, 5, v_numSectionVars_1197_);
lean_ctor_set(v_reuseFailAlloc_1208_, 6, v_type_1198_);
lean_ctor_set(v_reuseFailAlloc_1208_, 7, v_a_1158_);
lean_ctor_set(v_reuseFailAlloc_1208_, 8, v_termination_1199_);
lean_ctor_set_uint8(v_reuseFailAlloc_1208_, sizeof(void*)*9, v_kind_1192_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 0, v___x_1204_);
v___x_1206_ = v___x_1160_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
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
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v_env_1156_);
lean_dec(v___y_1148_);
lean_dec(v___y_1146_);
lean_dec_ref(v_fst_1109_);
v_a_1218_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1157_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1157_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v_a_1226_; 
lean_dec_ref(v_fst_1109_);
v_a_1226_ = lean_ctor_get(v___y_1152_, 0);
lean_inc(v_a_1226_);
lean_dec_ref(v___y_1152_);
v___y_1127_ = v___y_1145_;
v___y_1128_ = v___y_1146_;
v___y_1129_ = v___y_1148_;
v___y_1130_ = v___y_1147_;
v___y_1131_ = v___y_1149_;
v___y_1132_ = v___y_1150_;
v___y_1133_ = v___y_1151_;
v_a_1134_ = v_a_1226_;
goto v___jp_1126_;
}
}
v___jp_1227_:
{
lean_object* v___x_1234_; lean_object* v_env_1235_; lean_object* v___x_1236_; 
v___x_1234_ = lean_st_ref_get(v___y_1233_);
v_env_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc_ref(v_env_1235_);
lean_dec(v___x_1234_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
v___x_1236_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1110_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec_ref(v___x_1236_);
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__11(v_sz_1111_, v___x_1112_, v_a_1113_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1231_);
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1229_);
lean_inc_ref(v___y_1228_);
lean_inc_ref(v_fst_1109_);
v___x_1238_ = l_Lean_Elab_WF_mkFix(v_fst_1109_, v_fixedArgs_1114_, v_fst_1115_, v_wfRel_1118_, v___x_1116_, v___x_1237_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
v___x_1240_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1239_, v___y_1232_, v___y_1233_);
v___y_1145_ = v_env_1235_;
v___y_1146_ = v___y_1231_;
v___y_1147_ = v___y_1229_;
v___y_1148_ = v___y_1233_;
v___y_1149_ = v___y_1228_;
v___y_1150_ = v___y_1232_;
v___y_1151_ = v___y_1230_;
v___y_1152_ = v___x_1240_;
goto v___jp_1144_;
}
else
{
v___y_1145_ = v_env_1235_;
v___y_1146_ = v___y_1231_;
v___y_1147_ = v___y_1229_;
v___y_1148_ = v___y_1233_;
v___y_1149_ = v___y_1228_;
v___y_1150_ = v___y_1232_;
v___y_1151_ = v___y_1230_;
v___y_1152_ = v___x_1238_;
goto v___jp_1144_;
}
}
else
{
lean_object* v_a_1241_; 
lean_dec_ref(v_wfRel_1118_);
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_fst_1115_);
lean_dec_ref(v_fixedArgs_1114_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_fst_1109_);
v_a_1241_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1241_);
lean_dec_ref(v___x_1236_);
v___y_1127_ = v_env_1235_;
v___y_1128_ = v___y_1231_;
v___y_1129_ = v___y_1233_;
v___y_1130_ = v___y_1229_;
v___y_1131_ = v___y_1228_;
v___y_1132_ = v___y_1232_;
v___y_1133_ = v___y_1230_;
v_a_1134_ = v_a_1241_;
goto v___jp_1126_;
}
}
v___jp_1242_:
{
if (lean_obj_tag(v___y_1249_) == 0)
{
lean_dec_ref(v___y_1249_);
v___y_1228_ = v___y_1245_;
v___y_1229_ = v___y_1243_;
v___y_1230_ = v___y_1244_;
v___y_1231_ = v___y_1246_;
v___y_1232_ = v___y_1248_;
v___y_1233_ = v___y_1247_;
goto v___jp_1227_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v_wfRel_1118_);
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_fst_1115_);
lean_dec_ref(v_fixedArgs_1114_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_fst_1109_);
v_a_1250_ = lean_ctor_get(v___y_1249_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___y_1249_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___y_1249_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___y_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
v___jp_1258_:
{
lean_object* v___x_1265_; 
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc_ref(v_wfRel_1118_);
v___x_1265_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1118_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_a_1266_);
lean_dec_ref(v___x_1265_);
if (lean_obj_tag(v_a_1266_) == 0)
{
lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v___x_1267_ = lean_unsigned_to_nat(0u);
v___x_1268_ = lean_array_get_size(v_a_1113_);
v___x_1269_ = lean_nat_dec_lt(v___x_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
v___y_1228_ = v___y_1259_;
v___y_1229_ = v___y_1260_;
v___y_1230_ = v___y_1261_;
v___y_1231_ = v___y_1262_;
v___y_1232_ = v___y_1263_;
v___y_1233_ = v___y_1264_;
goto v___jp_1227_;
}
else
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_nat_dec_le(v___x_1268_, v___x_1268_);
if (v___x_1270_ == 0)
{
if (v___x_1269_ == 0)
{
v___y_1228_ = v___y_1259_;
v___y_1229_ = v___y_1260_;
v___y_1230_ = v___y_1261_;
v___y_1231_ = v___y_1262_;
v___y_1232_ = v___y_1263_;
v___y_1233_ = v___y_1264_;
goto v___jp_1227_;
}
else
{
size_t v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_usize_of_nat(v___x_1268_);
lean_inc_ref(v___y_1263_);
v___x_1272_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14(v_a_1113_, v___x_1112_, v___x_1271_, v___x_1117_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
v___y_1243_ = v___y_1260_;
v___y_1244_ = v___y_1261_;
v___y_1245_ = v___y_1259_;
v___y_1246_ = v___y_1262_;
v___y_1247_ = v___y_1264_;
v___y_1248_ = v___y_1263_;
v___y_1249_ = v___x_1272_;
goto v___jp_1242_;
}
}
else
{
size_t v___x_1273_; lean_object* v___x_1274_; 
v___x_1273_ = lean_usize_of_nat(v___x_1268_);
lean_inc_ref(v___y_1263_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__14(v_a_1113_, v___x_1112_, v___x_1273_, v___x_1117_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
v___y_1243_ = v___y_1260_;
v___y_1244_ = v___y_1261_;
v___y_1245_ = v___y_1259_;
v___y_1246_ = v___y_1262_;
v___y_1247_ = v___y_1264_;
v___y_1248_ = v___y_1263_;
v___y_1249_ = v___x_1274_;
goto v___jp_1242_;
}
}
}
else
{
lean_dec_ref(v_a_1266_);
v___y_1228_ = v___y_1259_;
v___y_1229_ = v___y_1260_;
v___y_1230_ = v___y_1261_;
v___y_1231_ = v___y_1262_;
v___y_1232_ = v___y_1263_;
v___y_1233_ = v___y_1264_;
goto v___jp_1227_;
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec_ref(v_wfRel_1118_);
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_fst_1115_);
lean_dec_ref(v_fixedArgs_1114_);
lean_dec_ref(v_a_1113_);
lean_dec_ref(v_fst_1109_);
v_a_1275_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1265_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1265_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object** _args){
lean_object* v___x_1298_ = _args[0];
lean_object* v_fst_1299_ = _args[1];
lean_object* v_snd_1300_ = _args[2];
lean_object* v_sz_1301_ = _args[3];
lean_object* v___x_1302_ = _args[4];
lean_object* v_a_1303_ = _args[5];
lean_object* v_fixedArgs_1304_ = _args[6];
lean_object* v_fst_1305_ = _args[7];
lean_object* v___x_1306_ = _args[8];
lean_object* v___x_1307_ = _args[9];
lean_object* v_wfRel_1308_ = _args[10];
lean_object* v___y_1309_ = _args[11];
lean_object* v___y_1310_ = _args[12];
lean_object* v___y_1311_ = _args[13];
lean_object* v___y_1312_ = _args[14];
lean_object* v___y_1313_ = _args[15];
lean_object* v___y_1314_ = _args[16];
lean_object* v___y_1315_ = _args[17];
_start:
{
size_t v_sz_boxed_1316_; size_t v___x_49004__boxed_1317_; lean_object* v_res_1318_; 
v_sz_boxed_1316_ = lean_unbox_usize(v_sz_1301_);
lean_dec(v_sz_1301_);
v___x_49004__boxed_1317_ = lean_unbox_usize(v___x_1302_);
lean_dec(v___x_1302_);
v_res_1318_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1298_, v_fst_1299_, v_snd_1300_, v_sz_boxed_1316_, v___x_49004__boxed_1317_, v_a_1303_, v_fixedArgs_1304_, v_fst_1305_, v___x_1306_, v___x_1307_, v_wfRel_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec_ref(v_snd_1300_);
return v_res_1318_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1321_ = l_Lean_stringToMessageData(v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(size_t v_sz_1322_, size_t v___x_1323_, lean_object* v_a_1324_, lean_object* v___x_1325_, lean_object* v_fst_1326_, lean_object* v_snd_1327_, lean_object* v_fst_1328_, lean_object* v___x_1329_, lean_object* v_declName_1330_, lean_object* v_fst_1331_, lean_object* v_wf_1332_, lean_object* v_fixedArgs_1333_, lean_object* v_type_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v___x_1342_; 
lean_inc(v___y_1340_);
lean_inc_ref(v___y_1339_);
lean_inc(v___y_1338_);
lean_inc_ref(v___y_1337_);
v___x_1342_ = l_Lean_Meta_whnfForall(v_type_1334_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; uint8_t v___x_1357_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref(v___x_1342_);
v___x_1357_ = l_Lean_Expr_isForall(v_a_1343_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec_ref(v_fixedArgs_1333_);
lean_dec_ref(v_wf_1332_);
lean_dec_ref(v_fst_1331_);
lean_dec(v_declName_1330_);
lean_dec_ref(v_fst_1328_);
lean_dec_ref(v_snd_1327_);
lean_dec_ref(v_fst_1326_);
lean_dec(v___x_1325_);
lean_dec_ref(v_a_1324_);
v___x_1358_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
v___x_1359_ = l_Lean_MessageData_ofExpr(v_a_1343_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1360_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
else
{
v___y_1345_ = v___y_1335_;
v___y_1346_ = v___y_1336_;
v___y_1347_ = v___y_1337_;
v___y_1348_ = v___y_1338_;
v___y_1349_ = v___y_1339_;
v___y_1350_ = v___y_1340_;
goto v___jp_1344_;
}
v___jp_1344_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___f_1355_; lean_object* v___x_1356_; 
v___x_1351_ = l_Lean_Expr_bindingDomain_x21(v_a_1343_);
lean_dec(v_a_1343_);
lean_inc_ref(v_a_1324_);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_1322_, v___x_1323_, v_a_1324_);
v___x_1353_ = lean_box_usize(v_sz_1322_);
v___x_1354_ = lean_box_usize(v___x_1323_);
lean_inc_ref(v___x_1352_);
lean_inc_ref(v_fst_1328_);
lean_inc_ref(v_fixedArgs_1333_);
v___f_1355_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__2___boxed), 18, 10);
lean_closure_set(v___f_1355_, 0, v___x_1325_);
lean_closure_set(v___f_1355_, 1, v_fst_1326_);
lean_closure_set(v___f_1355_, 2, v_snd_1327_);
lean_closure_set(v___f_1355_, 3, v___x_1353_);
lean_closure_set(v___f_1355_, 4, v___x_1354_);
lean_closure_set(v___f_1355_, 5, v_a_1324_);
lean_closure_set(v___f_1355_, 6, v_fixedArgs_1333_);
lean_closure_set(v___f_1355_, 7, v_fst_1328_);
lean_closure_set(v___f_1355_, 8, v___x_1352_);
lean_closure_set(v___f_1355_, 9, v___x_1329_);
v___x_1356_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1352_, v_declName_1330_, v_fst_1331_, v_fixedArgs_1333_, v_fst_1328_, v___x_1351_, v_wf_1332_, v___f_1355_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_, v___y_1350_);
return v___x_1356_;
}
}
else
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1377_; 
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec_ref(v_fixedArgs_1333_);
lean_dec_ref(v_wf_1332_);
lean_dec_ref(v_fst_1331_);
lean_dec(v_declName_1330_);
lean_dec_ref(v_fst_1328_);
lean_dec_ref(v_snd_1327_);
lean_dec_ref(v_fst_1326_);
lean_dec(v___x_1325_);
lean_dec_ref(v_a_1324_);
v_a_1370_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1372_ = v___x_1342_;
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1342_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1377_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v_a_1370_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args){
lean_object* v_sz_1378_ = _args[0];
lean_object* v___x_1379_ = _args[1];
lean_object* v_a_1380_ = _args[2];
lean_object* v___x_1381_ = _args[3];
lean_object* v_fst_1382_ = _args[4];
lean_object* v_snd_1383_ = _args[5];
lean_object* v_fst_1384_ = _args[6];
lean_object* v___x_1385_ = _args[7];
lean_object* v_declName_1386_ = _args[8];
lean_object* v_fst_1387_ = _args[9];
lean_object* v_wf_1388_ = _args[10];
lean_object* v_fixedArgs_1389_ = _args[11];
lean_object* v_type_1390_ = _args[12];
lean_object* v___y_1391_ = _args[13];
lean_object* v___y_1392_ = _args[14];
lean_object* v___y_1393_ = _args[15];
lean_object* v___y_1394_ = _args[16];
lean_object* v___y_1395_ = _args[17];
lean_object* v___y_1396_ = _args[18];
lean_object* v___y_1397_ = _args[19];
_start:
{
size_t v_sz_boxed_1398_; size_t v___x_49362__boxed_1399_; lean_object* v_res_1400_; 
v_sz_boxed_1398_ = lean_unbox_usize(v_sz_1378_);
lean_dec(v_sz_1378_);
v___x_49362__boxed_1399_ = lean_unbox_usize(v___x_1379_);
lean_dec(v___x_1379_);
v_res_1400_ = l_Lean_Elab_wfRecursion___lam__3(v_sz_boxed_1398_, v___x_49362__boxed_1399_, v_a_1380_, v___x_1381_, v_fst_1382_, v_snd_1383_, v_fst_1384_, v___x_1385_, v_declName_1386_, v_fst_1387_, v_wf_1388_, v_fixedArgs_1389_, v_type_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(lean_object* v_a_1401_, lean_object* v_fst_1402_, lean_object* v_fst_1403_, lean_object* v_fst_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_Elab_WF_guessLex(v_a_1401_, v_fst_1402_, v_fst_1403_, v_fst_1404_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object* v_a_1413_, lean_object* v_fst_1414_, lean_object* v_fst_1415_, lean_object* v_fst_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Elab_wfRecursion___lam__4(v_a_1413_, v_fst_1414_, v_fst_1415_, v_fst_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg___lam__0(lean_object* v___y_1425_, uint8_t v_isExporting_1426_, lean_object* v___x_1427_, lean_object* v___y_1428_, lean_object* v___x_1429_, lean_object* v_a_x3f_1430_){
_start:
{
lean_object* v___x_1432_; lean_object* v_env_1433_; lean_object* v_nextMacroScope_1434_; lean_object* v_ngen_1435_; lean_object* v_auxDeclNGen_1436_; lean_object* v_traceState_1437_; lean_object* v_messages_1438_; lean_object* v_infoState_1439_; lean_object* v_snapshotTasks_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1465_; 
v___x_1432_ = lean_st_ref_take(v___y_1425_);
v_env_1433_ = lean_ctor_get(v___x_1432_, 0);
v_nextMacroScope_1434_ = lean_ctor_get(v___x_1432_, 1);
v_ngen_1435_ = lean_ctor_get(v___x_1432_, 2);
v_auxDeclNGen_1436_ = lean_ctor_get(v___x_1432_, 3);
v_traceState_1437_ = lean_ctor_get(v___x_1432_, 4);
v_messages_1438_ = lean_ctor_get(v___x_1432_, 6);
v_infoState_1439_ = lean_ctor_get(v___x_1432_, 7);
v_snapshotTasks_1440_ = lean_ctor_get(v___x_1432_, 8);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v___x_1432_, 5);
lean_dec(v_unused_1466_);
v___x_1442_ = v___x_1432_;
v_isShared_1443_ = v_isSharedCheck_1465_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_snapshotTasks_1440_);
lean_inc(v_infoState_1439_);
lean_inc(v_messages_1438_);
lean_inc(v_traceState_1437_);
lean_inc(v_auxDeclNGen_1436_);
lean_inc(v_ngen_1435_);
lean_inc(v_nextMacroScope_1434_);
lean_inc(v_env_1433_);
lean_dec(v___x_1432_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1465_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1446_; 
v___x_1444_ = l_Lean_Environment_setExporting(v_env_1433_, v_isExporting_1426_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 5, v___x_1427_);
lean_ctor_set(v___x_1442_, 0, v___x_1444_);
v___x_1446_ = v___x_1442_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_nextMacroScope_1434_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_ngen_1435_);
lean_ctor_set(v_reuseFailAlloc_1464_, 3, v_auxDeclNGen_1436_);
lean_ctor_set(v_reuseFailAlloc_1464_, 4, v_traceState_1437_);
lean_ctor_set(v_reuseFailAlloc_1464_, 5, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1464_, 6, v_messages_1438_);
lean_ctor_set(v_reuseFailAlloc_1464_, 7, v_infoState_1439_);
lean_ctor_set(v_reuseFailAlloc_1464_, 8, v_snapshotTasks_1440_);
v___x_1446_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v_mctx_1449_; lean_object* v_zetaDeltaFVarIds_1450_; lean_object* v_postponed_1451_; lean_object* v_diag_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1462_; 
v___x_1447_ = lean_st_ref_set(v___y_1425_, v___x_1446_);
v___x_1448_ = lean_st_ref_take(v___y_1428_);
v_mctx_1449_ = lean_ctor_get(v___x_1448_, 0);
v_zetaDeltaFVarIds_1450_ = lean_ctor_get(v___x_1448_, 2);
v_postponed_1451_ = lean_ctor_get(v___x_1448_, 3);
v_diag_1452_ = lean_ctor_get(v___x_1448_, 4);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1462_ == 0)
{
lean_object* v_unused_1463_; 
v_unused_1463_ = lean_ctor_get(v___x_1448_, 1);
lean_dec(v_unused_1463_);
v___x_1454_ = v___x_1448_;
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_diag_1452_);
lean_inc(v_postponed_1451_);
lean_inc(v_zetaDeltaFVarIds_1450_);
lean_inc(v_mctx_1449_);
lean_dec(v___x_1448_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1462_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 1, v___x_1429_);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_mctx_1449_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_zetaDeltaFVarIds_1450_);
lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_postponed_1451_);
lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_diag_1452_);
v___x_1457_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_st_ref_set(v___y_1428_, v___x_1457_);
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
return v___x_1460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg___lam__0___boxed(lean_object* v___y_1467_, lean_object* v_isExporting_1468_, lean_object* v___x_1469_, lean_object* v___y_1470_, lean_object* v___x_1471_, lean_object* v_a_x3f_1472_, lean_object* v___y_1473_){
_start:
{
uint8_t v_isExporting_boxed_1474_; lean_object* v_res_1475_; 
v_isExporting_boxed_1474_ = lean_unbox(v_isExporting_1468_);
v_res_1475_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg___lam__0(v___y_1467_, v_isExporting_boxed_1474_, v___x_1469_, v___y_1470_, v___x_1471_, v_a_x3f_1472_);
lean_dec(v_a_x3f_1472_);
lean_dec(v___y_1470_);
lean_dec(v___y_1467_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg(lean_object* v_x_1476_, uint8_t v_isExporting_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v___x_1485_; lean_object* v_env_1486_; uint8_t v_isExporting_1487_; lean_object* v___x_1488_; lean_object* v_env_1489_; lean_object* v_nextMacroScope_1490_; lean_object* v_ngen_1491_; lean_object* v_auxDeclNGen_1492_; lean_object* v_traceState_1493_; lean_object* v_messages_1494_; lean_object* v_infoState_1495_; lean_object* v_snapshotTasks_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1550_; 
v___x_1485_ = lean_st_ref_get(v___y_1483_);
v_env_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc_ref(v_env_1486_);
lean_dec(v___x_1485_);
v_isExporting_1487_ = lean_ctor_get_uint8(v_env_1486_, sizeof(void*)*8);
lean_dec_ref(v_env_1486_);
v___x_1488_ = lean_st_ref_take(v___y_1483_);
v_env_1489_ = lean_ctor_get(v___x_1488_, 0);
v_nextMacroScope_1490_ = lean_ctor_get(v___x_1488_, 1);
v_ngen_1491_ = lean_ctor_get(v___x_1488_, 2);
v_auxDeclNGen_1492_ = lean_ctor_get(v___x_1488_, 3);
v_traceState_1493_ = lean_ctor_get(v___x_1488_, 4);
v_messages_1494_ = lean_ctor_get(v___x_1488_, 6);
v_infoState_1495_ = lean_ctor_get(v___x_1488_, 7);
v_snapshotTasks_1496_ = lean_ctor_get(v___x_1488_, 8);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v___x_1488_, 5);
lean_dec(v_unused_1551_);
v___x_1498_ = v___x_1488_;
v_isShared_1499_ = v_isSharedCheck_1550_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snapshotTasks_1496_);
lean_inc(v_infoState_1495_);
lean_inc(v_messages_1494_);
lean_inc(v_traceState_1493_);
lean_inc(v_auxDeclNGen_1492_);
lean_inc(v_ngen_1491_);
lean_inc(v_nextMacroScope_1490_);
lean_inc(v_env_1489_);
lean_dec(v___x_1488_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1550_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1503_; 
v___x_1500_ = l_Lean_Environment_setExporting(v_env_1489_, v_isExporting_1477_);
v___x_1501_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__2);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 5, v___x_1501_);
lean_ctor_set(v___x_1498_, 0, v___x_1500_);
v___x_1503_ = v___x_1498_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_nextMacroScope_1490_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_ngen_1491_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_auxDeclNGen_1492_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_traceState_1493_);
lean_ctor_set(v_reuseFailAlloc_1549_, 5, v___x_1501_);
lean_ctor_set(v_reuseFailAlloc_1549_, 6, v_messages_1494_);
lean_ctor_set(v_reuseFailAlloc_1549_, 7, v_infoState_1495_);
lean_ctor_set(v_reuseFailAlloc_1549_, 8, v_snapshotTasks_1496_);
v___x_1503_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_mctx_1506_; lean_object* v_zetaDeltaFVarIds_1507_; lean_object* v_postponed_1508_; lean_object* v_diag_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1547_; 
v___x_1504_ = lean_st_ref_set(v___y_1483_, v___x_1503_);
v___x_1505_ = lean_st_ref_take(v___y_1481_);
v_mctx_1506_ = lean_ctor_get(v___x_1505_, 0);
v_zetaDeltaFVarIds_1507_ = lean_ctor_get(v___x_1505_, 2);
v_postponed_1508_ = lean_ctor_get(v___x_1505_, 3);
v_diag_1509_ = lean_ctor_get(v___x_1505_, 4);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v___x_1505_, 1);
lean_dec(v_unused_1548_);
v___x_1511_ = v___x_1505_;
v_isShared_1512_ = v_isSharedCheck_1547_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_diag_1509_);
lean_inc(v_postponed_1508_);
lean_inc(v_zetaDeltaFVarIds_1507_);
lean_inc(v_mctx_1506_);
lean_dec(v___x_1505_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1547_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; lean_object* v___x_1515_; 
v___x_1513_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg___closed__3);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 1, v___x_1513_);
v___x_1515_ = v___x_1511_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_mctx_1506_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1513_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_zetaDeltaFVarIds_1507_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_postponed_1508_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_diag_1509_);
v___x_1515_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
lean_object* v___x_1516_; lean_object* v_r_1517_; 
v___x_1516_ = lean_st_ref_set(v___y_1481_, v___x_1515_);
lean_inc(v___y_1483_);
lean_inc(v___y_1481_);
v_r_1517_ = lean_apply_7(v_x_1476_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, lean_box(0));
if (lean_obj_tag(v_r_1517_) == 0)
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1534_; 
v_a_1518_ = lean_ctor_get(v_r_1517_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_r_1517_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1520_ = v_r_1517_;
v_isShared_1521_ = v_isSharedCheck_1534_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v_r_1517_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1534_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
lean_inc(v_a_1518_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 1);
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
lean_object* v___x_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
v___x_1524_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg___lam__0(v___y_1483_, v_isExporting_1487_, v___x_1501_, v___y_1481_, v___x_1513_, v___x_1523_);
lean_dec_ref(v___x_1523_);
lean_dec(v___y_1481_);
lean_dec(v___y_1483_);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v___x_1524_, 0);
lean_dec(v_unused_1532_);
v___x_1526_ = v___x_1524_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_dec(v___x_1524_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v_a_1518_);
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1518_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
}
else
{
lean_object* v_a_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
v_a_1535_ = lean_ctor_get(v_r_1517_, 0);
lean_inc(v_a_1535_);
lean_dec_ref(v_r_1517_);
v___x_1536_ = lean_box(0);
v___x_1537_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg___lam__0(v___y_1483_, v_isExporting_1487_, v___x_1501_, v___y_1481_, v___x_1513_, v___x_1536_);
lean_dec(v___y_1481_);
lean_dec(v___y_1483_);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v___x_1537_, 0);
lean_dec(v_unused_1545_);
v___x_1539_ = v___x_1537_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_dec(v___x_1537_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
lean_ctor_set_tag(v___x_1539_, 1);
lean_ctor_set(v___x_1539_, 0, v_a_1535_);
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1535_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg___boxed(lean_object* v_x_1552_, lean_object* v_isExporting_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v_isExporting_boxed_1561_; lean_object* v_res_1562_; 
v_isExporting_boxed_1561_ = lean_unbox(v_isExporting_1553_);
v_res_1562_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg(v_x_1552_, v_isExporting_boxed_1561_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg(lean_object* v_x_1563_, uint8_t v_when_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
if (v_when_1564_ == 0)
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_apply_7(v_x_1563_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_, lean_box(0));
return v___x_1572_;
}
else
{
uint8_t v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = 0;
v___x_1574_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg(v_x_1563_, v___x_1573_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg___boxed(lean_object* v_x_1575_, lean_object* v_when_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
uint8_t v_when_boxed_1584_; lean_object* v_res_1585_; 
v_when_boxed_1584_ = lean_unbox(v_when_1576_);
v_res_1585_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg(v_x_1575_, v_when_boxed_1584_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v___x_1586_, lean_object* v_as_1587_, size_t v_sz_1588_, size_t v_i_1589_, lean_object* v_b_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_a_1597_; uint8_t v___x_1601_; 
v___x_1601_ = lean_usize_dec_lt(v_i_1589_, v_sz_1588_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___x_1586_);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v_b_1590_);
return v___x_1602_;
}
else
{
lean_object* v_a_1603_; uint8_t v_kind_1604_; lean_object* v_declName_1605_; lean_object* v_type_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v_a_1603_ = lean_array_uget_borrowed(v_as_1587_, v_i_1589_);
v_kind_1604_ = lean_ctor_get_uint8(v_a_1603_, sizeof(void*)*9);
v_declName_1605_ = lean_ctor_get(v_a_1603_, 3);
v_type_1606_ = lean_ctor_get(v_a_1603_, 6);
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_name_eq(v_declName_1605_, v___x_1586_);
if (v___x_1608_ == 0)
{
uint8_t v___x_1609_; 
v___x_1609_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1604_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc_ref(v_type_1606_);
v___x_1610_ = l_Lean_Meta_isProp(v_type_1606_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1610_) == 0)
{
lean_object* v_a_1611_; uint8_t v___x_1612_; 
v_a_1611_ = lean_ctor_get(v___x_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v___x_1610_);
v___x_1612_ = lean_unbox(v_a_1611_);
lean_dec(v_a_1611_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_inc(v___y_1594_);
lean_inc_ref(v___y_1593_);
lean_inc(v___y_1592_);
lean_inc_ref(v___y_1591_);
lean_inc(v___x_1586_);
lean_inc(v_a_1603_);
v___x_1613_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1603_, v___x_1586_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_dec_ref(v___x_1613_);
v_a_1597_ = v___x_1607_;
goto v___jp_1596_;
}
else
{
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___x_1586_);
return v___x_1613_;
}
}
else
{
v_a_1597_ = v___x_1607_;
goto v___jp_1596_;
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___x_1586_);
v_a_1614_ = lean_ctor_get(v___x_1610_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1610_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1610_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1610_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
else
{
v_a_1597_ = v___x_1607_;
goto v___jp_1596_;
}
}
else
{
v_a_1597_ = v___x_1607_;
goto v___jp_1596_;
}
}
v___jp_1596_:
{
size_t v___x_1598_; size_t v___x_1599_; 
v___x_1598_ = ((size_t)1ULL);
v___x_1599_ = lean_usize_add(v_i_1589_, v___x_1598_);
v_i_1589_ = v___x_1599_;
v_b_1590_ = v_a_1597_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v___x_1622_, lean_object* v_as_1623_, lean_object* v_sz_1624_, lean_object* v_i_1625_, lean_object* v_b_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
size_t v_sz_boxed_1632_; size_t v_i_boxed_1633_; lean_object* v_res_1634_; 
v_sz_boxed_1632_ = lean_unbox_usize(v_sz_1624_);
lean_dec(v_sz_1624_);
v_i_boxed_1633_ = lean_unbox_usize(v_i_1625_);
lean_dec(v_i_1625_);
v_res_1634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___x_1622_, v_as_1623_, v_sz_boxed_1632_, v_i_boxed_1633_, v_b_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_);
lean_dec_ref(v_as_1623_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__9(size_t v_sz_1635_, size_t v_i_1636_, lean_object* v_bs_1637_){
_start:
{
uint8_t v___x_1638_; 
v___x_1638_ = lean_usize_dec_lt(v_i_1636_, v_sz_1635_);
if (v___x_1638_ == 0)
{
lean_object* v___x_1639_; 
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v_bs_1637_);
return v___x_1639_;
}
else
{
lean_object* v_v_1640_; 
v_v_1640_ = lean_array_uget_borrowed(v_bs_1637_, v_i_1636_);
if (lean_obj_tag(v_v_1640_) == 0)
{
lean_object* v___x_1641_; 
lean_dec_ref(v_bs_1637_);
v___x_1641_ = lean_box(0);
return v___x_1641_;
}
else
{
lean_object* v_val_1642_; lean_object* v___x_1643_; lean_object* v_bs_x27_1644_; size_t v___x_1645_; size_t v___x_1646_; lean_object* v___x_1647_; 
v_val_1642_ = lean_ctor_get(v_v_1640_, 0);
lean_inc(v_val_1642_);
v___x_1643_ = lean_unsigned_to_nat(0u);
v_bs_x27_1644_ = lean_array_uset(v_bs_1637_, v_i_1636_, v___x_1643_);
v___x_1645_ = ((size_t)1ULL);
v___x_1646_ = lean_usize_add(v_i_1636_, v___x_1645_);
v___x_1647_ = lean_array_uset(v_bs_x27_1644_, v_i_1636_, v_val_1642_);
v_i_1636_ = v___x_1646_;
v_bs_1637_ = v___x_1647_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object* v_sz_1649_, lean_object* v_i_1650_, lean_object* v_bs_1651_){
_start:
{
size_t v_sz_boxed_1652_; size_t v_i_boxed_1653_; lean_object* v_res_1654_; 
v_sz_boxed_1652_ = lean_unbox_usize(v_sz_1649_);
lean_dec(v_sz_1649_);
v_i_boxed_1653_ = lean_unbox_usize(v_i_1650_);
lean_dec(v_i_1650_);
v_res_1654_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__9(v_sz_boxed_1652_, v_i_boxed_1653_, v_bs_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(size_t v_sz_1655_, size_t v_i_1656_, lean_object* v_bs_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
uint8_t v___x_1661_; 
v___x_1661_ = lean_usize_dec_lt(v_i_1656_, v_sz_1655_);
if (v___x_1661_ == 0)
{
lean_object* v___x_1662_; 
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
v___x_1662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1662_, 0, v_bs_1657_);
return v___x_1662_;
}
else
{
lean_object* v_v_1663_; lean_object* v_ref_1664_; uint8_t v_kind_1665_; lean_object* v_levelParams_1666_; lean_object* v_modifiers_1667_; lean_object* v_declName_1668_; lean_object* v_binders_1669_; lean_object* v_numSectionVars_1670_; lean_object* v_type_1671_; lean_object* v_value_1672_; lean_object* v_termination_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1696_; 
v_v_1663_ = lean_array_uget(v_bs_1657_, v_i_1656_);
v_ref_1664_ = lean_ctor_get(v_v_1663_, 0);
v_kind_1665_ = lean_ctor_get_uint8(v_v_1663_, sizeof(void*)*9);
v_levelParams_1666_ = lean_ctor_get(v_v_1663_, 1);
v_modifiers_1667_ = lean_ctor_get(v_v_1663_, 2);
v_declName_1668_ = lean_ctor_get(v_v_1663_, 3);
v_binders_1669_ = lean_ctor_get(v_v_1663_, 4);
v_numSectionVars_1670_ = lean_ctor_get(v_v_1663_, 5);
v_type_1671_ = lean_ctor_get(v_v_1663_, 6);
v_value_1672_ = lean_ctor_get(v_v_1663_, 7);
v_termination_1673_ = lean_ctor_get(v_v_1663_, 8);
v_isSharedCheck_1696_ = !lean_is_exclusive(v_v_1663_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1675_ = v_v_1663_;
v_isShared_1676_ = v_isSharedCheck_1696_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_termination_1673_);
lean_inc(v_value_1672_);
lean_inc(v_type_1671_);
lean_inc(v_numSectionVars_1670_);
lean_inc(v_binders_1669_);
lean_inc(v_declName_1668_);
lean_inc(v_modifiers_1667_);
lean_inc(v_levelParams_1666_);
lean_inc(v_ref_1664_);
lean_dec(v_v_1663_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1696_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; 
lean_inc(v___y_1659_);
lean_inc_ref(v___y_1658_);
v___x_1677_ = l_Lean_Elab_WF_floatRecApp(v_value_1672_, v___y_1658_, v___y_1659_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; lean_object* v___x_1679_; lean_object* v_bs_x27_1680_; lean_object* v___x_1682_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref(v___x_1677_);
v___x_1679_ = lean_unsigned_to_nat(0u);
v_bs_x27_1680_ = lean_array_uset(v_bs_1657_, v_i_1656_, v___x_1679_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 7, v_a_1678_);
v___x_1682_ = v___x_1675_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_ref_1664_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_levelParams_1666_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_modifiers_1667_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_declName_1668_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_binders_1669_);
lean_ctor_set(v_reuseFailAlloc_1687_, 5, v_numSectionVars_1670_);
lean_ctor_set(v_reuseFailAlloc_1687_, 6, v_type_1671_);
lean_ctor_set(v_reuseFailAlloc_1687_, 7, v_a_1678_);
lean_ctor_set(v_reuseFailAlloc_1687_, 8, v_termination_1673_);
lean_ctor_set_uint8(v_reuseFailAlloc_1687_, sizeof(void*)*9, v_kind_1665_);
v___x_1682_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
size_t v___x_1683_; size_t v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = ((size_t)1ULL);
v___x_1684_ = lean_usize_add(v_i_1656_, v___x_1683_);
v___x_1685_ = lean_array_uset(v_bs_x27_1680_, v_i_1656_, v___x_1682_);
v_i_1656_ = v___x_1684_;
v_bs_1657_ = v___x_1685_;
goto _start;
}
}
else
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1695_; 
lean_del_object(v___x_1675_);
lean_dec_ref(v_termination_1673_);
lean_dec_ref(v_type_1671_);
lean_dec(v_numSectionVars_1670_);
lean_dec(v_binders_1669_);
lean_dec(v_declName_1668_);
lean_dec_ref(v_modifiers_1667_);
lean_dec(v_levelParams_1666_);
lean_dec(v_ref_1664_);
lean_dec(v___y_1659_);
lean_dec_ref(v___y_1658_);
lean_dec_ref(v_bs_1657_);
v_a_1688_ = lean_ctor_get(v___x_1677_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1677_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1690_ = v___x_1677_;
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1677_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1695_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1693_; 
if (v_isShared_1691_ == 0)
{
v___x_1693_ = v___x_1690_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_a_1688_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object* v_sz_1697_, lean_object* v_i_1698_, lean_object* v_bs_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_){
_start:
{
size_t v_sz_boxed_1703_; size_t v_i_boxed_1704_; lean_object* v_res_1705_; 
v_sz_boxed_1703_ = lean_unbox_usize(v_sz_1697_);
lean_dec(v_sz_1697_);
v_i_boxed_1704_ = lean_unbox_usize(v_i_1698_);
lean_dec(v_i_1698_);
v_res_1705_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_boxed_1703_, v_i_boxed_1704_, v_bs_1699_, v___y_1700_, v___y_1701_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg(size_t v_sz_1706_, size_t v_i_1707_, lean_object* v_bs_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_usize_dec_lt(v_i_1707_, v_sz_1706_);
if (v___x_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
v___x_1715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1715_, 0, v_bs_1708_);
return v___x_1715_;
}
else
{
uint8_t v___x_1716_; lean_object* v_v_1717_; lean_object* v___x_1718_; 
v___x_1716_ = 0;
v_v_1717_ = lean_array_uget_borrowed(v_bs_1708_, v_i_1707_);
lean_inc(v___y_1712_);
lean_inc_ref(v___y_1711_);
lean_inc(v___y_1710_);
lean_inc_ref(v___y_1709_);
lean_inc(v_v_1717_);
v___x_1718_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1717_, v___x_1716_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; lean_object* v_bs_x27_1721_; size_t v___x_1722_; size_t v___x_1723_; lean_object* v___x_1724_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref(v___x_1718_);
v___x_1720_ = lean_unsigned_to_nat(0u);
v_bs_x27_1721_ = lean_array_uset(v_bs_1708_, v_i_1707_, v___x_1720_);
v___x_1722_ = ((size_t)1ULL);
v___x_1723_ = lean_usize_add(v_i_1707_, v___x_1722_);
v___x_1724_ = lean_array_uset(v_bs_x27_1721_, v_i_1707_, v_a_1719_);
v_i_1707_ = v___x_1723_;
v_bs_1708_ = v___x_1724_;
goto _start;
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec_ref(v_bs_1708_);
v_a_1726_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1718_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1718_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v_sz_1734_, lean_object* v_i_1735_, lean_object* v_bs_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
size_t v_sz_boxed_1742_; size_t v_i_boxed_1743_; lean_object* v_res_1744_; 
v_sz_boxed_1742_ = lean_unbox_usize(v_sz_1734_);
lean_dec(v_sz_1734_);
v_i_boxed_1743_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v_res_1744_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg(v_sz_boxed_1742_, v_i_boxed_1743_, v_bs_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_env_1745_, lean_object* v_x_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v___x_1754_; lean_object* v_env_1755_; lean_object* v_a_1757_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v___x_1754_ = lean_st_ref_get(v___y_1752_);
v_env_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc_ref(v_env_1755_);
lean_dec(v___x_1754_);
v___x_1767_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg(v_env_1745_, v___y_1750_, v___y_1752_);
lean_dec_ref(v___x_1767_);
lean_inc(v___y_1752_);
lean_inc(v___y_1750_);
v___x_1768_ = lean_apply_7(v_x_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, lean_box(0));
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
v___x_1770_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg(v_env_1755_, v___y_1750_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec(v___y_1750_);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v___x_1770_, 0);
lean_dec(v_unused_1778_);
v___x_1772_ = v___x_1770_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_dec(v___x_1770_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v_a_1769_);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1769_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
else
{
lean_object* v_a_1779_; 
v_a_1779_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1768_);
v_a_1757_ = v_a_1779_;
goto v___jp_1756_;
}
v___jp_1756_:
{
lean_object* v___x_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1765_; 
v___x_1758_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__10___redArg(v_env_1755_, v___y_1750_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec(v___y_1750_);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1766_);
v___x_1760_ = v___x_1758_;
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v___x_1758_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1765_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1763_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set_tag(v___x_1760_, 1);
lean_ctor_set(v___x_1760_, 0, v_a_1757_);
v___x_1763_ = v___x_1760_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1757_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_env_1780_, lean_object* v_x_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_1780_, v_x_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_);
return v_res_1789_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1798_ = l_Lean_stringToMessageData(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1801_ = l_Lean_stringToMessageData(v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1804_ = l_Lean_stringToMessageData(v___x_1803_);
return v___x_1804_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1807_ = l_Lean_stringToMessageData(v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1810_, lean_object* v_preDefs_1811_, lean_object* v_termMeasure_x3fs_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
size_t v_sz_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v_sz_1820_ = lean_array_size(v_preDefs_1811_);
v___x_1821_ = ((size_t)0ULL);
lean_inc(v_a_1818_);
lean_inc_ref(v_a_1817_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_1820_, v___x_1821_, v_preDefs_1811_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; lean_object* v_env_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; lean_object* v___y_1835_; lean_object* v___y_1836_; size_t v_sz_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___f_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1822_);
v___x_1824_ = lean_st_ref_get(v_a_1818_);
v_env_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc_ref(v_env_1825_);
lean_dec(v___x_1824_);
v___x_1826_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v___x_1827_ = lean_box(0);
v_sz_1841_ = lean_array_size(v_a_1823_);
v___x_1842_ = lean_box_usize(v_sz_1841_);
v___x_1843_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_a_1823_);
v___f_1844_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1844_, 0, v_a_1823_);
lean_closure_set(v___f_1844_, 1, v___x_1842_);
lean_closure_set(v___f_1844_, 2, v___x_1843_);
lean_closure_set(v___f_1844_, 3, v___x_1827_);
lean_closure_set(v___f_1844_, 4, v___x_1826_);
v___x_1845_ = l_Lean_Environment_unlockAsync(v_env_1825_);
lean_inc(v_a_1818_);
lean_inc_ref(v_a_1817_);
lean_inc(v_a_1816_);
lean_inc_ref(v_a_1815_);
lean_inc(v_a_1814_);
lean_inc_ref(v_a_1813_);
v___x_1846_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_1845_, v___f_1844_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v_snd_1848_; lean_object* v_fst_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_2036_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref(v___x_1846_);
v_snd_1848_ = lean_ctor_get(v_a_1847_, 1);
v_fst_1849_ = lean_ctor_get(v_a_1847_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_1847_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_1851_ = v_a_1847_;
v_isShared_1852_ = v_isSharedCheck_2036_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_snd_1848_);
lean_inc(v_fst_1849_);
lean_dec(v_a_1847_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_2036_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_fst_1853_; lean_object* v_snd_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_2035_; 
v_fst_1853_ = lean_ctor_get(v_snd_1848_, 0);
v_snd_1854_ = lean_ctor_get(v_snd_1848_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_snd_1848_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_1856_ = v_snd_1848_;
v_isShared_1857_ = v_isSharedCheck_2035_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_snd_1854_);
lean_inc(v_fst_1853_);
lean_dec(v_snd_1848_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_2035_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___y_1859_; lean_object* v___y_1860_; uint8_t v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; lean_object* v___y_1864_; lean_object* v___y_1865_; lean_object* v___y_1866_; lean_object* v___y_1867_; lean_object* v___x_1917_; lean_object* v___y_1919_; lean_object* v___y_1920_; lean_object* v_wf_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___x_1963_; lean_object* v_a_1964_; lean_object* v___f_1965_; size_t v_sz_1966_; lean_object* v_termMeasures_x3f_1967_; lean_object* v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; uint8_t v___x_2028_; 
v___x_1917_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_1963_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1917_, v_a_1817_);
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref(v___x_1963_);
lean_inc(v_snd_1854_);
v___f_1965_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__1___boxed), 8, 1);
lean_closure_set(v___f_1965_, 0, v_snd_1854_);
v_sz_1966_ = lean_array_size(v_termMeasure_x3fs_1812_);
v_termMeasures_x3f_1967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__9(v_sz_1966_, v___x_1821_, v_termMeasure_x3fs_1812_);
v___x_2028_ = lean_unbox(v_a_1964_);
lean_dec(v_a_1964_);
if (v___x_2028_ == 0)
{
v___y_1991_ = v_a_1813_;
v___y_1992_ = v_a_1814_;
v___y_1993_ = v_a_1815_;
v___y_1994_ = v_a_1816_;
v___y_1995_ = v_a_1817_;
v___y_1996_ = v_a_1818_;
goto v___jp_1990_;
}
else
{
lean_object* v_value_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_value_2029_ = lean_ctor_get(v_snd_1854_, 7);
v___x_2030_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2029_);
v___x_2031_ = l_Lean_MessageData_ofExpr(v_value_2029_);
v___x_2032_ = l_Lean_indentD(v___x_2031_);
v___x_2033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2030_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v___x_1917_, v___x_2033_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_dec_ref(v___x_2034_);
v___y_1991_ = v_a_1813_;
v___y_1992_ = v_a_1814_;
v___y_1993_ = v_a_1815_;
v___y_1994_ = v_a_1816_;
v___y_1995_ = v_a_1817_;
v___y_1996_ = v_a_1818_;
goto v___jp_1990_;
}
else
{
lean_dec(v_termMeasures_x3f_1967_);
lean_dec_ref(v___f_1965_);
lean_del_object(v___x_1856_);
lean_dec(v_snd_1854_);
lean_dec(v_fst_1853_);
lean_del_object(v___x_1851_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1823_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_docCtx_1810_);
return v___x_2034_;
}
}
v___jp_1858_:
{
lean_object* v___x_1868_; 
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc_ref(v___y_1860_);
lean_inc(v_a_1823_);
lean_inc(v_fst_1853_);
lean_inc(v_fst_1849_);
v___x_1868_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1849_, v_fst_1853_, v_a_1823_, v___y_1860_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; lean_object* v___x_1870_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___x_1868_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc_ref(v___y_1860_);
lean_inc(v_a_1823_);
lean_inc_ref(v_docCtx_1810_);
v___x_1870_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1810_, v_a_1823_, v_a_1869_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
lean_dec(v_a_1869_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v___x_1871_; 
lean_dec_ref(v___x_1870_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v___y_1863_);
lean_inc_ref(v___y_1862_);
lean_inc(v_a_1823_);
v___x_1871_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1810_, v_a_1823_, v___y_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v___x_1871_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
v___x_1872_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1854_, v___y_1861_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
v___x_1874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__17___redArg(v_sz_1841_, v___x_1821_, v_a_1823_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v_declName_1876_; lean_object* v___x_1877_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___x_1874_);
v_declName_1876_ = lean_ctor_get(v___y_1860_, 3);
lean_inc(v_declName_1876_);
lean_dec_ref(v___y_1860_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v_declName_1876_);
lean_inc(v_a_1875_);
v___x_1877_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1875_, v_declName_1876_, v_fst_1849_, v_fst_1853_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_declName_1878_; lean_object* v_type_1879_; lean_object* v___x_1880_; 
lean_dec_ref(v___x_1877_);
v_declName_1878_ = lean_ctor_get(v_a_1873_, 3);
v_type_1879_ = lean_ctor_get(v_a_1873_, 6);
lean_inc(v_declName_1878_);
v___x_1880_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1878_, v___y_1867_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v___x_1881_; 
lean_dec_ref(v___x_1880_);
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc_ref(v_type_1879_);
v___x_1881_ = l_Lean_Meta_isProp(v_type_1879_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; uint8_t v___x_1883_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v___x_1881_);
v___x_1883_ = lean_unbox(v_a_1882_);
lean_dec(v_a_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
lean_inc(v___y_1867_);
lean_inc_ref(v___y_1866_);
lean_inc(v___y_1865_);
lean_inc_ref(v___y_1864_);
lean_inc(v_declName_1876_);
v___x_1884_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1873_, v_declName_1876_, v___y_1859_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_dec_ref(v___x_1884_);
v___y_1829_ = v_declName_1876_;
v___y_1830_ = v_a_1875_;
v___y_1831_ = v___y_1862_;
v___y_1832_ = v___y_1863_;
v___y_1833_ = v___y_1864_;
v___y_1834_ = v___y_1865_;
v___y_1835_ = v___y_1866_;
v___y_1836_ = v___y_1867_;
goto v___jp_1828_;
}
else
{
lean_dec(v_declName_1876_);
lean_dec(v_a_1875_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
return v___x_1884_;
}
}
else
{
lean_dec(v_a_1873_);
lean_dec_ref(v___y_1859_);
v___y_1829_ = v_declName_1876_;
v___y_1830_ = v_a_1875_;
v___y_1831_ = v___y_1862_;
v___y_1832_ = v___y_1863_;
v___y_1833_ = v___y_1864_;
v___y_1834_ = v___y_1865_;
v___y_1835_ = v___y_1866_;
v___y_1836_ = v___y_1867_;
goto v___jp_1828_;
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_dec(v_declName_1876_);
lean_dec(v_a_1875_);
lean_dec(v_a_1873_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1859_);
v_a_1885_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1881_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1881_);
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
else
{
lean_dec(v_declName_1876_);
lean_dec(v_a_1875_);
lean_dec(v_a_1873_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1859_);
return v___x_1880_;
}
}
else
{
lean_dec(v_declName_1876_);
lean_dec(v_a_1875_);
lean_dec(v_a_1873_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1859_);
return v___x_1877_;
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
lean_dec(v_a_1873_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_fst_1853_);
lean_dec(v_fst_1849_);
v_a_1893_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1874_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1874_);
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
else
{
lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_fst_1853_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1823_);
v_a_1901_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1908_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v___x_1872_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1872_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
else
{
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_snd_1854_);
lean_dec(v_fst_1853_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1823_);
return v___x_1871_;
}
}
else
{
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_snd_1854_);
lean_dec(v_fst_1853_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1823_);
lean_dec_ref(v_docCtx_1810_);
return v___x_1870_;
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec_ref(v___y_1860_);
lean_dec_ref(v___y_1859_);
lean_dec(v_snd_1854_);
lean_dec(v_fst_1853_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1823_);
lean_dec_ref(v_docCtx_1810_);
v_a_1909_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1868_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1868_);
v___x_1911_ = lean_box(0);
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
v_resetjp_1910_:
{
lean_object* v___x_1914_; 
if (v_isShared_1912_ == 0)
{
v___x_1914_ = v___x_1911_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_a_1909_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
}
}
v___jp_1918_:
{
lean_object* v_declName_1928_; lean_object* v_type_1929_; lean_object* v_numFixed_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___f_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; 
v_declName_1928_ = lean_ctor_get(v_snd_1854_, 3);
v_type_1929_ = lean_ctor_get(v_snd_1854_, 6);
v_numFixed_1930_ = lean_ctor_get(v_fst_1849_, 0);
v___x_1931_ = lean_box_usize(v_sz_1841_);
v___x_1932_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1849_);
lean_inc(v_declName_1928_);
lean_inc(v_fst_1853_);
lean_inc(v_snd_1854_);
lean_inc(v_a_1823_);
v___f_1933_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 20, 11);
lean_closure_set(v___f_1933_, 0, v___x_1931_);
lean_closure_set(v___f_1933_, 1, v___x_1932_);
lean_closure_set(v___f_1933_, 2, v_a_1823_);
lean_closure_set(v___f_1933_, 3, v___x_1917_);
lean_closure_set(v___f_1933_, 4, v___y_1919_);
lean_closure_set(v___f_1933_, 5, v_snd_1854_);
lean_closure_set(v___f_1933_, 6, v_fst_1853_);
lean_closure_set(v___f_1933_, 7, v___x_1827_);
lean_closure_set(v___f_1933_, 8, v_declName_1928_);
lean_closure_set(v___f_1933_, 9, v_fst_1849_);
lean_closure_set(v___f_1933_, 10, v_wf_1921_);
lean_inc(v_numFixed_1930_);
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_numFixed_1930_);
v___x_1935_ = 0;
lean_inc(v___y_1927_);
lean_inc_ref(v___y_1926_);
lean_inc(v___y_1925_);
lean_inc_ref(v___y_1924_);
lean_inc(v___y_1923_);
lean_inc_ref(v___y_1922_);
lean_inc_ref(v_type_1929_);
v___x_1936_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_type_1929_, v___x_1934_, v___f_1933_, v___x_1935_, v___x_1935_, v___y_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; lean_object* v___x_1938_; lean_object* v_a_1939_; uint8_t v___x_1940_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref(v___x_1936_);
v___x_1938_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1917_, v___y_1926_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref(v___x_1938_);
v___x_1940_ = lean_unbox(v_a_1939_);
lean_dec(v_a_1939_);
if (v___x_1940_ == 0)
{
lean_del_object(v___x_1856_);
lean_del_object(v___x_1851_);
v___y_1859_ = v___y_1920_;
v___y_1860_ = v_a_1937_;
v___y_1861_ = v___x_1935_;
v___y_1862_ = v___y_1922_;
v___y_1863_ = v___y_1923_;
v___y_1864_ = v___y_1924_;
v___y_1865_ = v___y_1925_;
v___y_1866_ = v___y_1926_;
v___y_1867_ = v___y_1927_;
goto v___jp_1858_;
}
else
{
lean_object* v_declName_1941_; lean_object* v_value_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
v_declName_1941_ = lean_ctor_get(v_a_1937_, 3);
v_value_1942_ = lean_ctor_get(v_a_1937_, 7);
v___x_1943_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1941_);
v___x_1944_ = l_Lean_MessageData_ofName(v_declName_1941_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set_tag(v___x_1856_, 7);
lean_ctor_set(v___x_1856_, 1, v___x_1944_);
lean_ctor_set(v___x_1856_, 0, v___x_1943_);
v___x_1946_ = v___x_1856_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___x_1944_);
v___x_1946_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1947_; lean_object* v___x_1949_; 
v___x_1947_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 7);
lean_ctor_set(v___x_1851_, 1, v___x_1947_);
lean_ctor_set(v___x_1851_, 0, v___x_1946_);
v___x_1949_ = v___x_1851_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1946_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1947_);
v___x_1949_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_inc_ref(v_value_1942_);
v___x_1950_ = l_Lean_MessageData_ofExpr(v_value_1942_);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v___x_1917_, v___x_1951_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_dec_ref(v___x_1952_);
v___y_1859_ = v___y_1920_;
v___y_1860_ = v_a_1937_;
v___y_1861_ = v___x_1935_;
v___y_1862_ = v___y_1922_;
v___y_1863_ = v___y_1923_;
v___y_1864_ = v___y_1924_;
v___y_1865_ = v___y_1925_;
v___y_1866_ = v___y_1926_;
v___y_1867_ = v___y_1927_;
goto v___jp_1858_;
}
else
{
lean_dec(v_a_1937_);
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec_ref(v___y_1920_);
lean_dec(v_snd_1854_);
lean_dec(v_fst_1853_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1823_);
lean_dec_ref(v_docCtx_1810_);
return v___x_1952_;
}
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v___y_1927_);
lean_dec_ref(v___y_1926_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec_ref(v___y_1920_);
lean_del_object(v___x_1856_);
lean_dec(v_snd_1854_);
lean_dec(v_fst_1853_);
lean_del_object(v___x_1851_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1823_);
lean_dec_ref(v_docCtx_1810_);
v_a_1955_ = lean_ctor_get(v___x_1936_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1936_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1936_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
v___jp_1968_:
{
if (lean_obj_tag(v_termMeasures_x3f_1967_) == 1)
{
lean_object* v_val_1978_; 
lean_dec_ref(v___y_1970_);
v_val_1978_ = lean_ctor_get(v_termMeasures_x3f_1967_, 0);
lean_inc(v_val_1978_);
lean_dec_ref(v_termMeasures_x3f_1967_);
v___y_1919_ = v___y_1969_;
v___y_1920_ = v___y_1971_;
v_wf_1921_ = v_val_1978_;
v___y_1922_ = v___y_1972_;
v___y_1923_ = v___y_1973_;
v___y_1924_ = v___y_1974_;
v___y_1925_ = v___y_1975_;
v___y_1926_ = v___y_1976_;
v___y_1927_ = v___y_1977_;
goto v___jp_1918_;
}
else
{
uint8_t v___x_1979_; lean_object* v___x_1980_; 
lean_dec(v_termMeasures_x3f_1967_);
v___x_1979_ = 1;
lean_inc(v___y_1977_);
lean_inc_ref(v___y_1976_);
lean_inc(v___y_1975_);
lean_inc_ref(v___y_1974_);
lean_inc(v___y_1973_);
lean_inc_ref(v___y_1972_);
v___x_1980_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg(v___y_1970_, v___x_1979_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref(v___x_1980_);
v___y_1919_ = v___y_1969_;
v___y_1920_ = v___y_1971_;
v_wf_1921_ = v_a_1981_;
v___y_1922_ = v___y_1972_;
v___y_1923_ = v___y_1973_;
v___y_1924_ = v___y_1974_;
v___y_1925_ = v___y_1975_;
v___y_1926_ = v___y_1976_;
v___y_1927_ = v___y_1977_;
goto v___jp_1918_;
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec(v___y_1977_);
lean_dec_ref(v___y_1976_);
lean_dec(v___y_1975_);
lean_dec_ref(v___y_1974_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec_ref(v___y_1971_);
lean_dec_ref(v___y_1969_);
lean_del_object(v___x_1856_);
lean_dec(v_snd_1854_);
lean_dec(v_fst_1853_);
lean_del_object(v___x_1851_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1823_);
lean_dec_ref(v_docCtx_1810_);
v_a_1982_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1980_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1980_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
v___jp_1990_:
{
lean_object* v___x_1997_; lean_object* v_env_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1997_ = lean_st_ref_get(v___y_1996_);
v_env_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc_ref(v_env_1998_);
lean_dec(v___x_1997_);
v___x_1999_ = l_Lean_Environment_unlockAsync(v_env_1998_);
lean_inc(v___y_1996_);
lean_inc_ref(v___y_1995_);
lean_inc(v___y_1994_);
lean_inc_ref(v___y_1993_);
lean_inc(v___y_1992_);
lean_inc_ref(v___y_1991_);
v___x_2000_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v___x_1999_, v___f_1965_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2019_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref(v___x_2000_);
v_fst_2002_ = lean_ctor_get(v_a_2001_, 0);
v_snd_2003_ = lean_ctor_get(v_a_2001_, 1);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_a_2001_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2005_ = v_a_2001_;
v_isShared_2006_ = v_isSharedCheck_2019_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snd_2003_);
lean_inc(v_fst_2002_);
lean_dec(v_a_2001_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2019_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; lean_object* v_a_2008_; lean_object* v___f_2009_; uint8_t v___x_2010_; 
v___x_2007_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1917_, v___y_1995_);
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v___x_2007_);
lean_inc(v_fst_1853_);
lean_inc(v_fst_1849_);
lean_inc(v_fst_2002_);
lean_inc(v_a_1823_);
v___f_2009_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 11, 4);
lean_closure_set(v___f_2009_, 0, v_a_1823_);
lean_closure_set(v___f_2009_, 1, v_fst_2002_);
lean_closure_set(v___f_2009_, 2, v_fst_1849_);
lean_closure_set(v___f_2009_, 3, v_fst_1853_);
v___x_2010_ = lean_unbox(v_a_2008_);
lean_dec(v_a_2008_);
if (v___x_2010_ == 0)
{
lean_del_object(v___x_2005_);
v___y_1969_ = v_fst_2002_;
v___y_1970_ = v___f_2009_;
v___y_1971_ = v_snd_2003_;
v___y_1972_ = v___y_1991_;
v___y_1973_ = v___y_1992_;
v___y_1974_ = v___y_1993_;
v___y_1975_ = v___y_1994_;
v___y_1976_ = v___y_1995_;
v___y_1977_ = v___y_1996_;
goto v___jp_1968_;
}
else
{
lean_object* v_value_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v_value_2011_ = lean_ctor_get(v_snd_1854_, 7);
v___x_2012_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_2011_);
v___x_2013_ = l_Lean_MessageData_ofExpr(v_value_2011_);
v___x_2014_ = l_Lean_indentD(v___x_2013_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set_tag(v___x_2005_, 7);
lean_ctor_set(v___x_2005_, 1, v___x_2014_);
lean_ctor_set(v___x_2005_, 0, v___x_2012_);
v___x_2016_ = v___x_2005_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2012_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__15___redArg(v___x_1917_, v___x_2016_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_dec_ref(v___x_2017_);
v___y_1969_ = v_fst_2002_;
v___y_1970_ = v___f_2009_;
v___y_1971_ = v_snd_2003_;
v___y_1972_ = v___y_1991_;
v___y_1973_ = v___y_1992_;
v___y_1974_ = v___y_1993_;
v___y_1975_ = v___y_1994_;
v___y_1976_ = v___y_1995_;
v___y_1977_ = v___y_1996_;
goto v___jp_1968_;
}
else
{
lean_dec_ref(v___f_2009_);
lean_dec(v_snd_2003_);
lean_dec(v_fst_2002_);
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v_termMeasures_x3f_1967_);
lean_del_object(v___x_1856_);
lean_dec(v_snd_1854_);
lean_dec(v_fst_1853_);
lean_del_object(v___x_1851_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1823_);
lean_dec_ref(v_docCtx_1810_);
return v___x_2017_;
}
}
}
}
}
else
{
lean_object* v_a_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2027_; 
lean_dec(v___y_1996_);
lean_dec_ref(v___y_1995_);
lean_dec(v___y_1994_);
lean_dec_ref(v___y_1993_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
lean_dec(v_termMeasures_x3f_1967_);
lean_del_object(v___x_1856_);
lean_dec(v_snd_1854_);
lean_dec(v_fst_1853_);
lean_del_object(v___x_1851_);
lean_dec(v_fst_1849_);
lean_dec(v_a_1823_);
lean_dec_ref(v_docCtx_1810_);
v_a_2020_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2027_ == 0)
{
v___x_2022_ = v___x_2000_;
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_a_2020_);
lean_dec(v___x_2000_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2027_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2025_; 
if (v_isShared_2023_ == 0)
{
v___x_2025_ = v___x_2022_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_a_2020_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
return v___x_2025_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2044_; 
lean_dec(v_a_1823_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_termMeasure_x3fs_1812_);
lean_dec_ref(v_docCtx_1810_);
v_a_2037_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2039_ = v___x_1846_;
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_a_2037_);
lean_dec(v___x_1846_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2044_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
v___jp_1828_:
{
size_t v_sz_1837_; lean_object* v___x_1838_; 
v_sz_1837_ = lean_array_size(v___y_1830_);
lean_inc(v___y_1836_);
lean_inc_ref(v___y_1835_);
lean_inc(v___y_1834_);
lean_inc_ref(v___y_1833_);
lean_inc(v___y_1829_);
v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_1829_, v___y_1830_, v_sz_1837_, v___x_1821_, v___x_1827_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1838_) == 0)
{
lean_object* v___x_1839_; 
lean_dec_ref(v___x_1838_);
lean_inc_ref(v___y_1835_);
v___x_1839_ = l_Lean_enableRealizationsForConst(v___y_1829_, v___y_1835_, v___y_1836_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_object* v___x_1840_; 
lean_dec_ref(v___x_1839_);
v___x_1840_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_, v___y_1836_);
return v___x_1840_;
}
else
{
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec_ref(v___y_1830_);
return v___x_1839_;
}
}
else
{
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec(v___y_1834_);
lean_dec_ref(v___y_1833_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec_ref(v___y_1830_);
lean_dec(v___y_1829_);
return v___x_1838_;
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec_ref(v_termMeasure_x3fs_1812_);
lean_dec_ref(v_docCtx_1810_);
v_a_2045_ = lean_ctor_get(v___x_1822_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_1822_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_1822_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2053_, lean_object* v_preDefs_2054_, lean_object* v_termMeasure_x3fs_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lean_Elab_wfRecursion(v_docCtx_2053_, v_preDefs_2054_, v_termMeasure_x3fs_2055_, v_a_2056_, v_a_2057_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2064_, lean_object* v_msg_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2074_, lean_object* v_msg_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2074_, v_msg_2075_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
lean_dec(v___y_2079_);
lean_dec_ref(v___y_2078_);
lean_dec(v___y_2077_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_2084_, size_t v_i_2085_, lean_object* v_bs_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_2084_, v_i_2085_, v_bs_2086_, v___y_2091_, v___y_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_2095_, lean_object* v_i_2096_, lean_object* v_bs_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
size_t v_sz_boxed_2105_; size_t v_i_boxed_2106_; lean_object* v_res_2107_; 
v_sz_boxed_2105_ = lean_unbox_usize(v_sz_2095_);
lean_dec(v_sz_2095_);
v_i_boxed_2106_ = lean_unbox_usize(v_i_2096_);
lean_dec(v_i_2096_);
v_res_2107_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_2105_, v_i_boxed_2106_, v_bs_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(lean_object* v_as_2108_, size_t v_sz_2109_, size_t v_i_2110_, lean_object* v_b_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_2108_, v_sz_2109_, v_i_2110_, v_b_2111_, v___y_2116_, v___y_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_as_2120_, lean_object* v_sz_2121_, lean_object* v_i_2122_, lean_object* v_b_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
size_t v_sz_boxed_2131_; size_t v_i_boxed_2132_; lean_object* v_res_2133_; 
v_sz_boxed_2131_ = lean_unbox_usize(v_sz_2121_);
lean_dec(v_sz_2121_);
v_i_boxed_2132_ = lean_unbox_usize(v_i_2122_);
lean_dec(v_i_2122_);
v_res_2133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(v_as_2120_, v_sz_boxed_2131_, v_i_boxed_2132_, v_b_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec_ref(v_as_2120_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_a_2134_, lean_object* v_as_2135_, lean_object* v_i_2136_, lean_object* v_j_2137_, lean_object* v_inv_2138_, lean_object* v_bs_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_2134_, v_as_2135_, v_i_2136_, v_j_2137_, v_bs_2139_, v___y_2142_, v___y_2143_, v___y_2144_, v___y_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_a_2148_, lean_object* v_as_2149_, lean_object* v_i_2150_, lean_object* v_j_2151_, lean_object* v_inv_2152_, lean_object* v_bs_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v_res_2161_; 
v_res_2161_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3(v_a_2148_, v_as_2149_, v_i_2150_, v_j_2151_, v_inv_2152_, v_bs_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_);
lean_dec(v___y_2155_);
lean_dec_ref(v___y_2154_);
lean_dec_ref(v_as_2149_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(lean_object* v_a_2162_, lean_object* v___x_2163_, size_t v_sz_2164_, size_t v_i_2165_, lean_object* v_bs_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_2162_, v___x_2163_, v_sz_2164_, v_i_2165_, v_bs_2166_, v___y_2171_, v___y_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_a_2175_, lean_object* v___x_2176_, lean_object* v_sz_2177_, lean_object* v_i_2178_, lean_object* v_bs_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
size_t v_sz_boxed_2187_; size_t v_i_boxed_2188_; lean_object* v_res_2189_; 
v_sz_boxed_2187_ = lean_unbox_usize(v_sz_2177_);
lean_dec(v_sz_2177_);
v_i_boxed_2188_ = lean_unbox_usize(v_i_2178_);
lean_dec(v_i_2178_);
v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_a_2175_, v___x_2176_, v_sz_boxed_2187_, v_i_boxed_2188_, v_bs_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_00_u03b1_2190_, lean_object* v_env_2191_, lean_object* v_x_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_env_2191_, v_x_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_00_u03b1_2201_, lean_object* v_env_2202_, lean_object* v_x_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(v_00_u03b1_2201_, v_env_2202_, v_x_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
return v_res_2211_;
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
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v_as_2270_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22(lean_object* v_00_u03b1_2284_, lean_object* v_x_2285_, uint8_t v_isExporting_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___redArg(v_x_2285_, v_isExporting_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22___boxed(lean_object* v_00_u03b1_2295_, lean_object* v_x_2296_, lean_object* v_isExporting_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_){
_start:
{
uint8_t v_isExporting_boxed_2305_; lean_object* v_res_2306_; 
v_isExporting_boxed_2305_ = lean_unbox(v_isExporting_2297_);
v_res_2306_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19_spec__22(v_00_u03b1_2295_, v_x_2296_, v_isExporting_boxed_2305_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19(lean_object* v_00_u03b1_2307_, lean_object* v_x_2308_, uint8_t v_when_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___redArg(v_x_2308_, v_when_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19___boxed(lean_object* v_00_u03b1_2318_, lean_object* v_x_2319_, lean_object* v_when_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
uint8_t v_when_boxed_2328_; lean_object* v_res_2329_; 
v_when_boxed_2328_ = lean_unbox(v_when_2320_);
v_res_2329_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__19(v_00_u03b1_2318_, v_x_2319_, v_when_boxed_2328_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2330_, lean_object* v_macroStack_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2330_, v_macroStack_2331_, v___y_2336_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2340_, lean_object* v_macroStack_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2340_, v_macroStack_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14(lean_object* v_ref_2350_, lean_object* v_msgData_2351_, uint8_t v_severity_2352_, uint8_t v_isSilent_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___redArg(v_ref_2350_, v_msgData_2351_, v_severity_2352_, v_isSilent_2353_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14___boxed(lean_object* v_ref_2362_, lean_object* v_msgData_2363_, lean_object* v_severity_2364_, lean_object* v_isSilent_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
uint8_t v_severity_boxed_2373_; uint8_t v_isSilent_boxed_2374_; lean_object* v_res_2375_; 
v_severity_boxed_2373_ = lean_unbox(v_severity_2364_);
v_isSilent_boxed_2374_ = lean_unbox(v_isSilent_2365_);
v_res_2375_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__12_spec__14(v_ref_2362_, v_msgData_2363_, v_severity_boxed_2373_, v_isSilent_boxed_2374_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_);
lean_dec(v___y_2371_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v_ref_2362_);
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
