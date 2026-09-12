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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldIfArgIsAppOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition_default;
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2;
static lean_once_cell_t l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "marking functions defined by well-founded recursion as `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "` is not effective"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "reducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value),LEAN_SCALAR_PTR_LITERAL(29, 67, 225, 118, 155, 2, 197, 97)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "semireducible"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value),LEAN_SCALAR_PTR_LITERAL(106, 254, 211, 230, 8, 182, 79, 36)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "wfRel: "};
static const lean_object* l_Lean_Elab_wfRecursion___lam__3___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__3___closed__0_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object**);
static const lean_string_object l_Lean_Elab_wfRecursion___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "wfRecursion: expected unary function type: "};
static const lean_object* l_Lean_Elab_wfRecursion___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_Elab_wfRecursion___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_wfRecursion___lam__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_wfRecursion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "definition"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__0 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__0_value;
static const lean_string_object l_Lean_Elab_wfRecursion___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wf"};
static const lean_object* l_Lean_Elab_wfRecursion___closed__1 = (const lean_object*)&l_Lean_Elab_wfRecursion___closed__1_value;
static const lean_ctor_object l_Lean_Elab_wfRecursion___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(136, 8, 70, 241, 95, 177, 39, 230)}};
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
static const lean_ctor_object l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value),((lean_object*)&l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 119, 48, 4, 113, 111, 251, 171)}};
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
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1);
v___x_7_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_6_);
lean_ctor_set(v___x_7_, 2, v___x_6_);
lean_ctor_set(v___x_7_, 3, v___x_6_);
lean_ctor_set(v___x_7_, 4, v___x_6_);
lean_ctor_set(v___x_7_, 5, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(lean_object* v_env_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v___x_12_; lean_object* v_nextMacroScope_13_; lean_object* v_ngen_14_; lean_object* v_auxDeclNGen_15_; lean_object* v_traceState_16_; lean_object* v_messages_17_; lean_object* v_infoState_18_; lean_object* v_snapshotTasks_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_45_; 
v___x_12_ = lean_st_ref_take(v___y_10_);
v_nextMacroScope_13_ = lean_ctor_get(v___x_12_, 1);
v_ngen_14_ = lean_ctor_get(v___x_12_, 2);
v_auxDeclNGen_15_ = lean_ctor_get(v___x_12_, 3);
v_traceState_16_ = lean_ctor_get(v___x_12_, 4);
v_messages_17_ = lean_ctor_get(v___x_12_, 6);
v_infoState_18_ = lean_ctor_get(v___x_12_, 7);
v_snapshotTasks_19_ = lean_ctor_get(v___x_12_, 8);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_12_);
if (v_isSharedCheck_45_ == 0)
{
lean_object* v_unused_46_; lean_object* v_unused_47_; 
v_unused_46_ = lean_ctor_get(v___x_12_, 5);
lean_dec(v_unused_46_);
v_unused_47_ = lean_ctor_get(v___x_12_, 0);
lean_dec(v_unused_47_);
v___x_21_ = v___x_12_;
v_isShared_22_ = v_isSharedCheck_45_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_snapshotTasks_19_);
lean_inc(v_infoState_18_);
lean_inc(v_messages_17_);
lean_inc(v_traceState_16_);
lean_inc(v_auxDeclNGen_15_);
lean_inc(v_ngen_14_);
lean_inc(v_nextMacroScope_13_);
lean_dec(v___x_12_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_45_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 5, v___x_23_);
lean_ctor_set(v___x_21_, 0, v_env_8_);
v___x_25_ = v___x_21_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_env_8_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_nextMacroScope_13_);
lean_ctor_set(v_reuseFailAlloc_44_, 2, v_ngen_14_);
lean_ctor_set(v_reuseFailAlloc_44_, 3, v_auxDeclNGen_15_);
lean_ctor_set(v_reuseFailAlloc_44_, 4, v_traceState_16_);
lean_ctor_set(v_reuseFailAlloc_44_, 5, v___x_23_);
lean_ctor_set(v_reuseFailAlloc_44_, 6, v_messages_17_);
lean_ctor_set(v_reuseFailAlloc_44_, 7, v_infoState_18_);
lean_ctor_set(v_reuseFailAlloc_44_, 8, v_snapshotTasks_19_);
v___x_25_ = v_reuseFailAlloc_44_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v_mctx_28_; lean_object* v_zetaDeltaFVarIds_29_; lean_object* v_postponed_30_; lean_object* v_diag_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_42_; 
v___x_26_ = lean_st_ref_put(v___y_10_, v___x_25_);
v___x_27_ = lean_st_ref_take(v___y_9_);
v_mctx_28_ = lean_ctor_get(v___x_27_, 0);
v_zetaDeltaFVarIds_29_ = lean_ctor_get(v___x_27_, 2);
v_postponed_30_ = lean_ctor_get(v___x_27_, 3);
v_diag_31_ = lean_ctor_get(v___x_27_, 4);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_42_ == 0)
{
lean_object* v_unused_43_; 
v_unused_43_ = lean_ctor_get(v___x_27_, 1);
lean_dec(v_unused_43_);
v___x_33_ = v___x_27_;
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_diag_31_);
lean_inc(v_postponed_30_);
lean_inc(v_zetaDeltaFVarIds_29_);
lean_inc(v_mctx_28_);
lean_dec(v___x_27_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_42_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_35_ = lean_box(0);
v___x_36_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 1, v___x_36_);
v___x_38_ = v___x_33_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v_mctx_28_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v_zetaDeltaFVarIds_29_);
lean_ctor_set(v_reuseFailAlloc_41_, 3, v_postponed_30_);
lean_ctor_set(v_reuseFailAlloc_41_, 4, v_diag_31_);
v___x_38_ = v_reuseFailAlloc_41_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_39_ = lean_st_ref_put(v___y_9_, v___x_38_);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_35_);
return v___x_40_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(lean_object* v_env_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_48_, v___y_49_, v___y_50_);
lean_dec(v___y_50_);
lean_dec(v___y_49_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(lean_object* v_env_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_53_, v___y_57_, v___y_59_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(lean_object* v_env_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(v_env_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
lean_dec(v___y_68_);
lean_dec_ref(v___y_67_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec(v___y_64_);
lean_dec_ref(v___y_63_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(lean_object* v_k_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v_b_74_, lean_object* v_c_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v___x_81_; 
lean_inc(v___y_79_);
lean_inc_ref(v___y_78_);
lean_inc(v___y_77_);
lean_inc_ref(v___y_76_);
lean_inc(v___y_73_);
lean_inc_ref(v___y_72_);
v___x_81_ = lean_apply_9(v_k_71_, v_b_74_, v_c_75_, v___y_72_, v___y_73_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, lean_box(0));
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed(lean_object* v_k_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v_b_85_, lean_object* v_c_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(v_k_82_, v___y_83_, v___y_84_, v_b_85_, v_c_86_, v___y_87_, v___y_88_, v___y_89_, v___y_90_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
lean_dec(v___y_88_);
lean_dec_ref(v___y_87_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(lean_object* v_type_93_, lean_object* v_maxFVars_x3f_94_, lean_object* v_k_95_, uint8_t v_cleanupAnnotations_96_, uint8_t v_whnfType_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; 
lean_inc(v___y_99_);
lean_inc_ref(v___y_98_);
v___f_105_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed), 10, 3);
lean_closure_set(v___f_105_, 0, v_k_95_);
lean_closure_set(v___f_105_, 1, v___y_98_);
lean_closure_set(v___f_105_, 2, v___y_99_);
v___x_106_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_93_, v_maxFVars_x3f_94_, v___f_105_, v_cleanupAnnotations_96_, v_whnfType_97_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
if (lean_obj_tag(v___x_106_) == 0)
{
return v___x_106_;
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_106_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(lean_object* v_type_115_, lean_object* v_maxFVars_x3f_116_, lean_object* v_k_117_, lean_object* v_cleanupAnnotations_118_, lean_object* v_whnfType_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_127_; uint8_t v_whnfType_boxed_128_; lean_object* v_res_129_; 
v_cleanupAnnotations_boxed_127_ = lean_unbox(v_cleanupAnnotations_118_);
v_whnfType_boxed_128_ = lean_unbox(v_whnfType_119_);
v_res_129_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_115_, v_maxFVars_x3f_116_, v_k_117_, v_cleanupAnnotations_boxed_127_, v_whnfType_boxed_128_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(lean_object* v_00_u03b1_130_, lean_object* v_type_131_, lean_object* v_maxFVars_x3f_132_, lean_object* v_k_133_, uint8_t v_cleanupAnnotations_134_, uint8_t v_whnfType_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_131_, v_maxFVars_x3f_132_, v_k_133_, v_cleanupAnnotations_134_, v_whnfType_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___boxed(lean_object* v_00_u03b1_144_, lean_object* v_type_145_, lean_object* v_maxFVars_x3f_146_, lean_object* v_k_147_, lean_object* v_cleanupAnnotations_148_, lean_object* v_whnfType_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_157_; uint8_t v_whnfType_boxed_158_; lean_object* v_res_159_; 
v_cleanupAnnotations_boxed_157_ = lean_unbox(v_cleanupAnnotations_148_);
v_whnfType_boxed_158_ = lean_unbox(v_whnfType_149_);
v_res_159_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(v_00_u03b1_144_, v_type_145_, v_maxFVars_x3f_146_, v_k_147_, v_cleanupAnnotations_boxed_157_, v_whnfType_boxed_158_, v___y_150_, v___y_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_);
lean_dec(v___y_155_);
lean_dec_ref(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(lean_object* v_as_160_, size_t v_sz_161_, size_t v_i_162_, lean_object* v_b_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
uint8_t v___x_167_; 
v___x_167_ = lean_usize_dec_lt(v_i_162_, v_sz_161_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; 
v___x_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_168_, 0, v_b_163_);
return v___x_168_;
}
else
{
lean_object* v___x_169_; lean_object* v_a_170_; lean_object* v___x_171_; 
v___x_169_ = lean_box(0);
v_a_170_ = lean_array_uget_borrowed(v_as_160_, v_i_162_);
v___x_171_ = l_Lean_Elab_addAsAxiom___redArg(v_a_170_, v___y_164_, v___y_165_);
if (lean_obj_tag(v___x_171_) == 0)
{
size_t v___x_172_; size_t v___x_173_; 
lean_dec_ref_known(v___x_171_, 1);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = lean_usize_add(v_i_162_, v___x_172_);
v_i_162_ = v___x_173_;
v_b_163_ = v___x_169_;
goto _start;
}
else
{
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(lean_object* v_as_175_, lean_object* v_sz_176_, lean_object* v_i_177_, lean_object* v_b_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
size_t v_sz_boxed_182_; size_t v_i_boxed_183_; lean_object* v_res_184_; 
v_sz_boxed_182_ = lean_unbox_usize(v_sz_176_);
lean_dec(v_sz_176_);
v_i_boxed_183_ = lean_unbox_usize(v_i_177_);
lean_dec(v_i_177_);
v_res_184_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_as_175_, v_sz_boxed_182_, v_i_boxed_183_, v_b_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec_ref(v_as_175_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(lean_object* v_a_185_, size_t v_sz_186_, size_t v_i_187_, lean_object* v_bs_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_lt(v_i_187_, v_sz_186_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
lean_dec_ref(v_a_185_);
v___x_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_195_, 0, v_bs_188_);
return v___x_195_;
}
else
{
lean_object* v_v_196_; lean_object* v___x_197_; lean_object* v_bs_x27_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_v_196_ = lean_array_uget(v_bs_188_, v_i_187_);
v___x_197_ = lean_unsigned_to_nat(0u);
v_bs_x27_198_ = lean_array_uset(v_bs_188_, v_i_187_, v___x_197_);
v___x_199_ = lean_usize_to_nat(v_i_187_);
lean_inc_ref(v_a_185_);
v___x_200_ = l_Lean_Elab_WF_varyingVarNames(v_a_185_, v___x_199_, v_v_196_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; size_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref_known(v___x_200_, 1);
v___x_202_ = ((size_t)1ULL);
v___x_203_ = lean_usize_add(v_i_187_, v___x_202_);
v___x_204_ = lean_array_uset(v_bs_x27_198_, v_i_187_, v_a_201_);
v_i_187_ = v___x_203_;
v_bs_188_ = v___x_204_;
goto _start;
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec_ref(v_bs_x27_198_);
lean_dec_ref(v_a_185_);
v_a_206_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_200_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_200_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg___boxed(lean_object* v_a_214_, lean_object* v_sz_215_, lean_object* v_i_216_, lean_object* v_bs_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
size_t v_sz_boxed_223_; size_t v_i_boxed_224_; lean_object* v_res_225_; 
v_sz_boxed_223_ = lean_unbox_usize(v_sz_215_);
lean_dec(v_sz_215_);
v_i_boxed_224_ = lean_unbox_usize(v_i_216_);
lean_dec(v_i_216_);
v_res_225_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_214_, v_sz_boxed_223_, v_i_boxed_224_, v_bs_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
return v_res_225_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_box(1);
v___x_227_ = l_Lean_MessageData_ofFormat(v___x_226_);
return v___x_227_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2));
v___x_232_ = l_Lean_MessageData_ofFormat(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
if (lean_obj_tag(v_x_234_) == 0)
{
return v_x_233_;
}
else
{
lean_object* v_head_235_; lean_object* v_tail_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_258_; 
v_head_235_ = lean_ctor_get(v_x_234_, 0);
v_tail_236_ = lean_ctor_get(v_x_234_, 1);
v_isSharedCheck_258_ = !lean_is_exclusive(v_x_234_);
if (v_isSharedCheck_258_ == 0)
{
v___x_238_ = v_x_234_;
v_isShared_239_ = v_isSharedCheck_258_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_tail_236_);
lean_inc(v_head_235_);
lean_dec(v_x_234_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_258_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_before_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_256_; 
v_before_240_ = lean_ctor_get(v_head_235_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v_head_235_);
if (v_isSharedCheck_256_ == 0)
{
lean_object* v_unused_257_; 
v_unused_257_ = lean_ctor_get(v_head_235_, 1);
lean_dec(v_unused_257_);
v___x_242_ = v_head_235_;
v_isShared_243_ = v_isSharedCheck_256_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_before_240_);
lean_dec(v_head_235_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_256_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_243_ == 0)
{
lean_ctor_set_tag(v___x_242_, 7);
lean_ctor_set(v___x_242_, 1, v___x_244_);
lean_ctor_set(v___x_242_, 0, v_x_233_);
v___x_246_ = v___x_242_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_x_233_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_255_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_249_; 
v___x_247_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 7);
lean_ctor_set(v___x_238_, 1, v___x_247_);
lean_ctor_set(v___x_238_, 0, v___x_246_);
v___x_249_ = v___x_238_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_247_);
v___x_249_ = v_reuseFailAlloc_254_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = l_Lean_MessageData_ofSyntax(v_before_240_);
v___x_251_ = l_Lean_indentD(v___x_250_);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_249_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v_x_233_ = v___x_252_;
v_x_234_ = v_tail_236_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(lean_object* v_opts_259_, lean_object* v_opt_260_){
_start:
{
lean_object* v_name_261_; lean_object* v_defValue_262_; lean_object* v_map_263_; lean_object* v___x_264_; 
v_name_261_ = lean_ctor_get(v_opt_260_, 0);
v_defValue_262_ = lean_ctor_get(v_opt_260_, 1);
v_map_263_ = lean_ctor_get(v_opts_259_, 0);
v___x_264_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_263_, v_name_261_);
if (lean_obj_tag(v___x_264_) == 0)
{
uint8_t v___x_265_; 
v___x_265_ = lean_unbox(v_defValue_262_);
return v___x_265_;
}
else
{
lean_object* v_val_266_; 
v_val_266_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_val_266_);
lean_dec_ref_known(v___x_264_, 1);
if (lean_obj_tag(v_val_266_) == 1)
{
uint8_t v_v_267_; 
v_v_267_ = lean_ctor_get_uint8(v_val_266_, 0);
lean_dec_ref_known(v_val_266_, 0);
return v_v_267_;
}
else
{
uint8_t v___x_268_; 
lean_dec(v_val_266_);
v___x_268_ = lean_unbox(v_defValue_262_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___boxed(lean_object* v_opts_269_, lean_object* v_opt_270_){
_start:
{
uint8_t v_res_271_; lean_object* v_r_272_; 
v_res_271_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_opts_269_, v_opt_270_);
lean_dec_ref(v_opt_270_);
lean_dec_ref(v_opts_269_);
v_r_272_ = lean_box(v_res_271_);
return v_r_272_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1));
v___x_277_ = l_Lean_MessageData_ofFormat(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(lean_object* v_msgData_278_, lean_object* v_macroStack_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_toCold_282_; lean_object* v_options_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_toCold_282_ = lean_ctor_get(v___y_280_, 0);
v_options_283_ = lean_ctor_get(v_toCold_282_, 2);
v___x_284_ = l_Lean_Elab_pp_macroStack;
v___x_285_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
lean_dec(v_macroStack_279_);
v___x_286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_286_, 0, v_msgData_278_);
return v___x_286_;
}
else
{
if (lean_obj_tag(v_macroStack_279_) == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v_msgData_278_);
return v___x_287_;
}
else
{
lean_object* v_head_288_; lean_object* v_after_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_304_; 
v_head_288_ = lean_ctor_get(v_macroStack_279_, 0);
lean_inc(v_head_288_);
v_after_289_ = lean_ctor_get(v_head_288_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_head_288_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v_head_288_, 0);
lean_dec(v_unused_305_);
v___x_291_ = v_head_288_;
v_isShared_292_ = v_isSharedCheck_304_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_after_289_);
lean_dec(v_head_288_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_304_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 7);
lean_ctor_set(v___x_291_, 1, v___x_293_);
lean_ctor_set(v___x_291_, 0, v_msgData_278_);
v___x_295_ = v___x_291_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v_msgData_278_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_303_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_msgData_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_296_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2);
v___x_297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = l_Lean_MessageData_ofSyntax(v_after_289_);
v___x_299_ = l_Lean_indentD(v___x_298_);
v_msgData_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_300_, 0, v___x_297_);
lean_ctor_set(v_msgData_300_, 1, v___x_299_);
v___x_301_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_msgData_300_, v_macroStack_279_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(lean_object* v_msgData_306_, lean_object* v_macroStack_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_306_, v_macroStack_307_, v___y_308_);
lean_dec_ref(v___y_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(lean_object* v_msgData_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; lean_object* v_env_318_; lean_object* v___x_319_; lean_object* v_toCold_320_; lean_object* v_mctx_321_; lean_object* v_lctx_322_; lean_object* v_options_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_317_ = lean_st_ref_get(v___y_315_);
v_env_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc_ref(v_env_318_);
lean_dec(v___x_317_);
v___x_319_ = lean_st_ref_get(v___y_313_);
v_toCold_320_ = lean_ctor_get(v___y_314_, 0);
v_mctx_321_ = lean_ctor_get(v___x_319_, 0);
lean_inc_ref(v_mctx_321_);
lean_dec(v___x_319_);
v_lctx_322_ = lean_ctor_get(v___y_312_, 2);
v_options_323_ = lean_ctor_get(v_toCold_320_, 2);
lean_inc_ref(v_options_323_);
lean_inc_ref(v_lctx_322_);
v___x_324_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_324_, 0, v_env_318_);
lean_ctor_set(v___x_324_, 1, v_mctx_321_);
lean_ctor_set(v___x_324_, 2, v_lctx_322_);
lean_ctor_set(v___x_324_, 3, v_options_323_);
v___x_325_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v_msgData_311_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(lean_object* v_msgData_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_);
lean_dec(v___y_331_);
lean_dec_ref(v___y_330_);
lean_dec(v___y_329_);
lean_dec_ref(v___y_328_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(lean_object* v_msg_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_ref_342_; lean_object* v_macroStack_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_a_346_; lean_object* v___x_347_; lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_356_; 
v_ref_342_ = lean_ctor_get(v___y_339_, 2);
v_macroStack_343_ = lean_ctor_get(v___y_335_, 1);
v___x_344_ = l_Lean_Elab_getBetterRef(v_ref_342_, v_macroStack_343_);
v___x_345_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_334_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref(v___x_345_);
lean_inc(v_macroStack_343_);
v___x_347_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_346_, v_macroStack_343_, v___y_339_);
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_356_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_356_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_354_; 
v___x_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_344_);
lean_ctor_set(v___x_352_, 1, v_a_348_);
if (v_isShared_351_ == 0)
{
lean_ctor_set_tag(v___x_350_, 1);
lean_ctor_set(v___x_350_, 0, v___x_352_);
v___x_354_ = v___x_350_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v___x_352_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* v_msg_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_365_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__0));
v___x_368_ = l_Lean_stringToMessageData(v___x_367_);
return v___x_368_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__2));
v___x_371_ = l_Lean_stringToMessageData(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(lean_object* v_as_372_, size_t v_sz_373_, size_t v_i_374_, lean_object* v_b_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_a_384_; uint8_t v___x_388_; 
v___x_388_ = lean_usize_dec_lt(v_i_374_, v_sz_373_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_389_, 0, v_b_375_);
return v___x_389_;
}
else
{
lean_object* v_array_390_; lean_object* v_start_391_; lean_object* v_stop_392_; uint8_t v___x_393_; 
v_array_390_ = lean_ctor_get(v_b_375_, 0);
v_start_391_ = lean_ctor_get(v_b_375_, 1);
v_stop_392_ = lean_ctor_get(v_b_375_, 2);
v___x_393_ = lean_nat_dec_lt(v_start_391_, v_stop_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
v___x_394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_394_, 0, v_b_375_);
return v___x_394_;
}
else
{
lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_423_; 
lean_inc(v_stop_392_);
lean_inc(v_start_391_);
lean_inc_ref(v_array_390_);
v_isSharedCheck_423_ = !lean_is_exclusive(v_b_375_);
if (v_isSharedCheck_423_ == 0)
{
lean_object* v_unused_424_; lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_424_ = lean_ctor_get(v_b_375_, 2);
lean_dec(v_unused_424_);
v_unused_425_ = lean_ctor_get(v_b_375_, 1);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_b_375_, 0);
lean_dec(v_unused_426_);
v___x_396_ = v_b_375_;
v_isShared_397_ = v_isSharedCheck_423_;
goto v_resetjp_395_;
}
else
{
lean_dec(v_b_375_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_423_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v_a_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v_a_398_ = lean_array_uget_borrowed(v_as_372_, v_i_374_);
v___x_399_ = lean_array_fget(v_array_390_, v_start_391_);
v___x_400_ = lean_unsigned_to_nat(1u);
v___x_401_ = lean_nat_add(v_start_391_, v___x_400_);
lean_dec(v_start_391_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_401_);
v___x_403_ = v___x_396_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_array_390_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_stop_392_);
v___x_403_ = v_reuseFailAlloc_422_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_404_ = lean_array_get_size(v_a_398_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_nat_dec_eq(v___x_404_, v___x_405_);
if (v___x_406_ == 0)
{
lean_dec(v___x_399_);
v_a_384_ = v___x_403_;
goto v___jp_383_;
}
else
{
lean_object* v_declName_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_declName_407_ = lean_ctor_get(v___x_399_, 3);
lean_inc(v_declName_407_);
lean_dec(v___x_399_);
v___x_408_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__1);
v___x_409_ = l_Lean_MessageData_ofName(v_declName_407_);
v___x_410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_408_);
lean_ctor_set(v___x_410_, 1, v___x_409_);
v___x_411_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___closed__3);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_412_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_dec_ref_known(v___x_413_, 1);
v_a_384_ = v___x_403_;
goto v___jp_383_;
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec_ref(v___x_403_);
v_a_414_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_413_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_413_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
}
}
}
}
v___jp_383_:
{
size_t v___x_385_; size_t v___x_386_; 
v___x_385_ = ((size_t)1ULL);
v___x_386_ = lean_usize_add(v_i_374_, v___x_385_);
v_i_374_ = v___x_386_;
v_b_375_ = v_a_384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5___boxed(lean_object* v_as_427_, lean_object* v_sz_428_, lean_object* v_i_429_, lean_object* v_b_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
size_t v_sz_boxed_438_; size_t v_i_boxed_439_; lean_object* v_res_440_; 
v_sz_boxed_438_ = lean_unbox_usize(v_sz_428_);
lean_dec(v_sz_428_);
v_i_boxed_439_ = lean_unbox_usize(v_i_429_);
lean_dec(v_i_429_);
v_res_440_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_as_427_, v_sz_boxed_438_, v_i_boxed_439_, v_b_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
lean_dec(v___y_434_);
lean_dec_ref(v___y_433_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec_ref(v_as_427_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(size_t v_sz_441_, size_t v_i_442_, lean_object* v_bs_443_){
_start:
{
uint8_t v___x_444_; 
v___x_444_ = lean_usize_dec_lt(v_i_442_, v_sz_441_);
if (v___x_444_ == 0)
{
return v_bs_443_;
}
else
{
lean_object* v_v_445_; lean_object* v_declName_446_; lean_object* v___x_447_; lean_object* v_bs_x27_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v_v_445_ = lean_array_uget_borrowed(v_bs_443_, v_i_442_);
v_declName_446_ = lean_ctor_get(v_v_445_, 3);
lean_inc(v_declName_446_);
v___x_447_ = lean_unsigned_to_nat(0u);
v_bs_x27_448_ = lean_array_uset(v_bs_443_, v_i_442_, v___x_447_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_442_, v___x_449_);
v___x_451_ = lean_array_uset(v_bs_x27_448_, v_i_442_, v_declName_446_);
v_i_442_ = v___x_450_;
v_bs_443_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(lean_object* v_sz_453_, lean_object* v_i_454_, lean_object* v_bs_455_){
_start:
{
size_t v_sz_boxed_456_; size_t v_i_boxed_457_; lean_object* v_res_458_; 
v_sz_boxed_456_ = lean_unbox_usize(v_sz_453_);
lean_dec(v_sz_453_);
v_i_boxed_457_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_res_458_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_boxed_456_, v_i_boxed_457_, v_bs_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(lean_object* v_a_459_, lean_object* v___x_460_, size_t v_sz_461_, size_t v_i_462_, lean_object* v_bs_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = lean_usize_dec_lt(v_i_462_, v_sz_461_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_dec(v___x_460_);
lean_dec_ref(v_a_459_);
v___x_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_468_, 0, v_bs_463_);
return v___x_468_;
}
else
{
lean_object* v_v_469_; lean_object* v_ref_470_; uint8_t v_kind_471_; lean_object* v_levelParams_472_; lean_object* v_modifiers_473_; lean_object* v_declName_474_; lean_object* v_binders_475_; lean_object* v_numSectionVars_476_; lean_object* v_type_477_; lean_object* v_value_478_; lean_object* v_termination_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_505_; 
v_v_469_ = lean_array_uget(v_bs_463_, v_i_462_);
v_ref_470_ = lean_ctor_get(v_v_469_, 0);
v_kind_471_ = lean_ctor_get_uint8(v_v_469_, sizeof(void*)*9);
v_levelParams_472_ = lean_ctor_get(v_v_469_, 1);
v_modifiers_473_ = lean_ctor_get(v_v_469_, 2);
v_declName_474_ = lean_ctor_get(v_v_469_, 3);
v_binders_475_ = lean_ctor_get(v_v_469_, 4);
v_numSectionVars_476_ = lean_ctor_get(v_v_469_, 5);
v_type_477_ = lean_ctor_get(v_v_469_, 6);
v_value_478_ = lean_ctor_get(v_v_469_, 7);
v_termination_479_ = lean_ctor_get(v_v_469_, 8);
v_isSharedCheck_505_ = !lean_is_exclusive(v_v_469_);
if (v_isSharedCheck_505_ == 0)
{
v___x_481_ = v_v_469_;
v_isShared_482_ = v_isSharedCheck_505_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_termination_479_);
lean_inc(v_value_478_);
lean_inc(v_type_477_);
lean_inc(v_numSectionVars_476_);
lean_inc(v_binders_475_);
lean_inc(v_declName_474_);
lean_inc(v_modifiers_473_);
lean_inc(v_levelParams_472_);
lean_inc(v_ref_470_);
lean_dec(v_v_469_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_505_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
size_t v_sz_483_; lean_object* v___x_484_; lean_object* v_bs_x27_485_; size_t v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_sz_483_ = lean_array_size(v_a_459_);
v___x_484_ = lean_unsigned_to_nat(0u);
v_bs_x27_485_ = lean_array_uset(v_bs_463_, v_i_462_, v___x_484_);
v___x_486_ = ((size_t)0ULL);
lean_inc_ref(v_a_459_);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_483_, v___x_486_, v_a_459_);
lean_inc(v___x_460_);
v___x_488_ = l_Lean_Meta_unfoldIfArgIsAppOf(v___x_487_, v___x_460_, v_value_478_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_491_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 7, v_a_489_);
v___x_491_ = v___x_481_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_ref_470_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_levelParams_472_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_modifiers_473_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_declName_474_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_binders_475_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_numSectionVars_476_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v_type_477_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_a_489_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_termination_479_);
lean_ctor_set_uint8(v_reuseFailAlloc_496_, sizeof(void*)*9, v_kind_471_);
v___x_491_ = v_reuseFailAlloc_496_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_462_, v___x_492_);
v___x_494_ = lean_array_uset(v_bs_x27_485_, v_i_462_, v___x_491_);
v_i_462_ = v___x_493_;
v_bs_463_ = v___x_494_;
goto _start;
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_dec_ref(v_bs_x27_485_);
lean_del_object(v___x_481_);
lean_dec_ref(v_termination_479_);
lean_dec_ref(v_type_477_);
lean_dec(v_numSectionVars_476_);
lean_dec(v_binders_475_);
lean_dec(v_declName_474_);
lean_dec_ref(v_modifiers_473_);
lean_dec(v_levelParams_472_);
lean_dec(v_ref_470_);
lean_dec(v___x_460_);
lean_dec_ref(v_a_459_);
v_a_497_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_488_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_488_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* v_a_506_, lean_object* v___x_507_, lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_bs_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
size_t v_sz_boxed_514_; size_t v_i_boxed_515_; lean_object* v_res_516_; 
v_sz_boxed_514_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_515_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_506_, v___x_507_, v_sz_boxed_514_, v_i_boxed_515_, v_bs_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* v_a_517_, size_t v_sz_518_, size_t v___x_519_, lean_object* v___x_520_, lean_object* v___x_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_a_517_, v_sz_518_, v___x_519_, v___x_520_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v___x_530_; 
lean_dec_ref_known(v___x_529_, 1);
lean_inc_ref(v_a_517_);
v___x_530_ = l_Lean_Elab_getFixedParamPerms(v_a_517_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v_a_531_; lean_object* v___x_532_; 
v_a_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_n(v_a_531_, 2);
lean_dec_ref_known(v___x_530_, 1);
lean_inc_ref(v_a_517_);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_531_, v_sz_518_, v___x_519_, v_a_517_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; size_t v_sz_537_; lean_object* v___x_538_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v___x_532_, 1);
v___x_534_ = lean_unsigned_to_nat(0u);
v___x_535_ = lean_array_get_size(v_a_517_);
lean_inc_ref(v_a_517_);
v___x_536_ = l_Array_toSubarray___redArg(v_a_517_, v___x_534_, v___x_535_);
v_sz_537_ = lean_array_size(v_a_533_);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__5(v_a_533_, v_sz_537_, v___x_519_, v___x_536_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; lean_object* v_numSectionVars_540_; lean_object* v___x_541_; 
lean_dec_ref_known(v___x_538_, 1);
v___x_539_ = lean_array_get_borrowed(v___x_521_, v_a_517_, v___x_534_);
v_numSectionVars_540_ = lean_ctor_get(v___x_539_, 5);
lean_inc(v_numSectionVars_540_);
lean_inc_ref(v_a_517_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_517_, v_numSectionVars_540_, v_sz_518_, v___x_519_, v_a_517_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v_a_542_; lean_object* v___x_543_; 
v_a_542_ = lean_ctor_get(v___x_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___x_541_, 1);
lean_inc(v_a_533_);
lean_inc(v_a_531_);
v___x_543_ = l_Lean_Elab_WF_packMutual(v_a_531_, v_a_533_, v_a_542_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_553_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_553_ == 0)
{
v___x_546_ = v___x_543_;
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_553_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_551_; 
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_a_533_);
lean_ctor_set(v___x_548_, 1, v_a_544_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_a_531_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 0, v___x_549_);
v___x_551_ = v___x_546_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_dec(v_a_533_);
lean_dec(v_a_531_);
v_a_554_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_543_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_543_);
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
lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_569_; 
lean_dec(v_a_533_);
lean_dec(v_a_531_);
v_a_562_ = lean_ctor_get(v___x_541_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_541_);
if (v_isSharedCheck_569_ == 0)
{
v___x_564_ = v___x_541_;
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_541_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_569_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_567_; 
if (v_isShared_565_ == 0)
{
v___x_567_ = v___x_564_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_a_562_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
return v___x_567_;
}
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_dec(v_a_533_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_517_);
v_a_570_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_538_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_538_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_object* v_a_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_585_; 
lean_dec(v_a_531_);
lean_dec_ref(v_a_517_);
v_a_578_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_585_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_585_ == 0)
{
v___x_580_ = v___x_532_;
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_a_578_);
lean_dec(v___x_532_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_585_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_583_; 
if (v_isShared_581_ == 0)
{
v___x_583_ = v___x_580_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_a_578_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
}
else
{
lean_object* v_a_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_593_; 
lean_dec_ref(v_a_517_);
v_a_586_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_593_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_593_ == 0)
{
v___x_588_ = v___x_530_;
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_a_586_);
lean_dec(v___x_530_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_593_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_591_; 
if (v_isShared_589_ == 0)
{
v___x_591_ = v___x_588_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_a_586_);
v___x_591_ = v_reuseFailAlloc_592_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
return v___x_591_;
}
}
}
}
else
{
lean_object* v_a_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_601_; 
lean_dec_ref(v_a_517_);
v_a_594_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_601_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_601_ == 0)
{
v___x_596_ = v___x_529_;
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_a_594_);
lean_dec(v___x_529_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_601_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_599_; 
if (v_isShared_597_ == 0)
{
v___x_599_ = v___x_596_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v_a_594_);
v___x_599_ = v_reuseFailAlloc_600_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
return v___x_599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object* v_a_602_, lean_object* v_sz_603_, lean_object* v___x_604_, lean_object* v___x_605_, lean_object* v___x_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
size_t v_sz_boxed_614_; size_t v___x_43839__boxed_615_; lean_object* v_res_616_; 
v_sz_boxed_614_ = lean_unbox_usize(v_sz_603_);
lean_dec(v_sz_603_);
v___x_43839__boxed_615_ = lean_unbox_usize(v___x_604_);
lean_dec(v___x_604_);
v_res_616_ = l_Lean_Elab_wfRecursion___lam__0(v_a_602_, v_sz_boxed_614_, v___x_43839__boxed_615_, v___x_605_, v___x_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v___y_608_);
lean_dec_ref(v___y_607_);
lean_dec_ref(v___x_606_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* v_snd_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_617_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_ref_626_; uint8_t v_kind_627_; lean_object* v_levelParams_628_; lean_object* v_modifiers_629_; lean_object* v_declName_630_; lean_object* v_binders_631_; lean_object* v_numSectionVars_632_; lean_object* v_type_633_; lean_object* v_value_634_; lean_object* v_termination_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_661_; 
lean_dec_ref_known(v___x_625_, 1);
v_ref_626_ = lean_ctor_get(v_snd_617_, 0);
v_kind_627_ = lean_ctor_get_uint8(v_snd_617_, sizeof(void*)*9);
v_levelParams_628_ = lean_ctor_get(v_snd_617_, 1);
v_modifiers_629_ = lean_ctor_get(v_snd_617_, 2);
v_declName_630_ = lean_ctor_get(v_snd_617_, 3);
v_binders_631_ = lean_ctor_get(v_snd_617_, 4);
v_numSectionVars_632_ = lean_ctor_get(v_snd_617_, 5);
v_type_633_ = lean_ctor_get(v_snd_617_, 6);
v_value_634_ = lean_ctor_get(v_snd_617_, 7);
v_termination_635_ = lean_ctor_get(v_snd_617_, 8);
v_isSharedCheck_661_ = !lean_is_exclusive(v_snd_617_);
if (v_isSharedCheck_661_ == 0)
{
v___x_637_ = v_snd_617_;
v_isShared_638_ = v_isSharedCheck_661_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_termination_635_);
lean_inc(v_value_634_);
lean_inc(v_type_633_);
lean_inc(v_numSectionVars_632_);
lean_inc(v_binders_631_);
lean_inc(v_declName_630_);
lean_inc(v_modifiers_629_);
lean_inc(v_levelParams_628_);
lean_inc(v_ref_626_);
lean_dec(v_snd_617_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_661_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Elab_WF_preprocess(v_value_634_, v___y_620_, v___y_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_652_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_652_ == 0)
{
v___x_642_ = v___x_639_;
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_639_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_652_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_expr_644_; lean_object* v___x_646_; 
v_expr_644_ = lean_ctor_get(v_a_640_, 0);
lean_inc_ref(v_expr_644_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 7, v_expr_644_);
v___x_646_ = v___x_637_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_ref_626_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_levelParams_628_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_modifiers_629_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v_declName_630_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v_binders_631_);
lean_ctor_set(v_reuseFailAlloc_651_, 5, v_numSectionVars_632_);
lean_ctor_set(v_reuseFailAlloc_651_, 6, v_type_633_);
lean_ctor_set(v_reuseFailAlloc_651_, 7, v_expr_644_);
lean_ctor_set(v_reuseFailAlloc_651_, 8, v_termination_635_);
lean_ctor_set_uint8(v_reuseFailAlloc_651_, sizeof(void*)*9, v_kind_627_);
v___x_646_ = v_reuseFailAlloc_651_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v_a_640_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_647_);
v___x_649_ = v___x_642_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_660_; 
lean_del_object(v___x_637_);
lean_dec_ref(v_termination_635_);
lean_dec_ref(v_type_633_);
lean_dec(v_numSectionVars_632_);
lean_dec(v_binders_631_);
lean_dec(v_declName_630_);
lean_dec_ref(v_modifiers_629_);
lean_dec(v_levelParams_628_);
lean_dec(v_ref_626_);
v_a_653_ = lean_ctor_get(v___x_639_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_639_);
if (v_isSharedCheck_660_ == 0)
{
v___x_655_ = v___x_639_;
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_639_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_660_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_658_; 
if (v_isShared_656_ == 0)
{
v___x_658_ = v___x_655_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_a_653_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
}
else
{
lean_object* v_a_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_669_; 
lean_dec_ref(v_snd_617_);
v_a_662_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_669_ == 0)
{
v___x_664_ = v___x_625_;
v_isShared_665_ = v_isSharedCheck_669_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_a_662_);
lean_dec(v___x_625_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* v_snd_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Elab_wfRecursion___lam__1(v_snd_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* v___x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_toCold_690_; lean_object* v_options_691_; uint8_t v_hasTrace_692_; 
v_toCold_690_ = lean_ctor_get(v___y_687_, 0);
v_options_691_ = lean_ctor_get(v_toCold_690_, 2);
v_hasTrace_692_ = lean_ctor_get_uint8(v_options_691_, sizeof(void*)*1);
if (v_hasTrace_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec(v___x_682_);
v___x_693_ = lean_box(v_hasTrace_692_);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
else
{
lean_object* v_inheritedTraceOptions_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_inheritedTraceOptions_695_ = lean_ctor_get(v_toCold_690_, 11);
v___x_696_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__1));
v___x_697_ = l_Lean_Name_append(v___x_696_, v___x_682_);
v___x_698_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_695_, v_options_691_, v___x_697_);
lean_dec(v___x_697_);
v___x_699_ = lean_box(v___x_698_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
return v___x_700_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object* v___x_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_Lean_Elab_wfRecursion___lam__2(v___x_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_709_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(uint8_t v_suppressElabErrors_717_, uint8_t v___y_718_, lean_object* v_x_719_){
_start:
{
if (lean_obj_tag(v_x_719_) == 1)
{
lean_object* v_pre_720_; 
v_pre_720_ = lean_ctor_get(v_x_719_, 0);
switch(lean_obj_tag(v_pre_720_))
{
case 1:
{
lean_object* v_pre_721_; 
v_pre_721_ = lean_ctor_get(v_pre_720_, 0);
switch(lean_obj_tag(v_pre_721_))
{
case 0:
{
lean_object* v_str_722_; lean_object* v_str_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_str_722_ = lean_ctor_get(v_x_719_, 1);
v_str_723_ = lean_ctor_get(v_pre_720_, 1);
v___x_724_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0));
v___x_725_ = lean_string_dec_eq(v_str_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1));
v___x_727_ = lean_string_dec_eq(v_str_723_, v___x_726_);
if (v___x_727_ == 0)
{
return v___x_727_;
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2));
v___x_729_ = lean_string_dec_eq(v_str_722_, v___x_728_);
if (v___x_729_ == 0)
{
return v___x_729_;
}
else
{
return v_suppressElabErrors_717_;
}
}
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3));
v___x_731_ = lean_string_dec_eq(v_str_722_, v___x_730_);
if (v___x_731_ == 0)
{
return v___x_731_;
}
else
{
return v_suppressElabErrors_717_;
}
}
}
case 1:
{
lean_object* v_pre_732_; 
v_pre_732_ = lean_ctor_get(v_pre_721_, 0);
if (lean_obj_tag(v_pre_732_) == 0)
{
lean_object* v_str_733_; lean_object* v_str_734_; lean_object* v_str_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v_str_733_ = lean_ctor_get(v_x_719_, 1);
v_str_734_ = lean_ctor_get(v_pre_720_, 1);
v_str_735_ = lean_ctor_get(v_pre_721_, 1);
v___x_736_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4));
v___x_737_ = lean_string_dec_eq(v_str_735_, v___x_736_);
if (v___x_737_ == 0)
{
return v___x_737_;
}
else
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5));
v___x_739_ = lean_string_dec_eq(v_str_734_, v___x_738_);
if (v___x_739_ == 0)
{
return v___x_739_;
}
else
{
lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_740_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6));
v___x_741_ = lean_string_dec_eq(v_str_733_, v___x_740_);
if (v___x_741_ == 0)
{
return v___x_741_;
}
else
{
return v_suppressElabErrors_717_;
}
}
}
}
else
{
return v___y_718_;
}
}
default: 
{
return v___y_718_;
}
}
}
case 0:
{
lean_object* v_str_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_str_742_ = lean_ctor_get(v_x_719_, 1);
v___x_743_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__0));
v___x_744_ = lean_string_dec_eq(v_str_742_, v___x_743_);
if (v___x_744_ == 0)
{
return v___x_744_;
}
else
{
return v_suppressElabErrors_717_;
}
}
default: 
{
return v___y_718_;
}
}
}
else
{
return v___y_718_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(lean_object* v_suppressElabErrors_745_, lean_object* v___y_746_, lean_object* v_x_747_){
_start:
{
uint8_t v_suppressElabErrors_boxed_748_; uint8_t v___y_44169__boxed_749_; uint8_t v_res_750_; lean_object* v_r_751_; 
v_suppressElabErrors_boxed_748_ = lean_unbox(v_suppressElabErrors_745_);
v___y_44169__boxed_749_ = lean_unbox(v___y_746_);
v_res_750_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v_suppressElabErrors_boxed_748_, v___y_44169__boxed_749_, v_x_747_);
lean_dec(v_x_747_);
v_r_751_ = lean_box(v_res_750_);
return v_r_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(lean_object* v_ref_753_, lean_object* v_msgData_754_, uint8_t v_severity_755_, uint8_t v_isSilent_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___y_763_; uint8_t v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; uint8_t v___y_769_; lean_object* v_currNamespace_770_; lean_object* v_openDecls_771_; lean_object* v___y_772_; lean_object* v___y_798_; lean_object* v___y_799_; lean_object* v___y_800_; lean_object* v___y_801_; uint8_t v___y_802_; lean_object* v___y_803_; uint8_t v___y_804_; lean_object* v___y_805_; uint8_t v___y_806_; lean_object* v___y_807_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; uint8_t v___y_830_; lean_object* v___y_831_; uint8_t v___y_832_; uint8_t v___y_833_; lean_object* v___y_834_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; uint8_t v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; uint8_t v___y_845_; uint8_t v___y_846_; uint8_t v___x_851_; lean_object* v___y_853_; lean_object* v___y_854_; lean_object* v___y_855_; lean_object* v___y_856_; lean_object* v___y_857_; uint8_t v___y_858_; lean_object* v___y_859_; uint8_t v___y_860_; uint8_t v___y_861_; uint8_t v___y_863_; uint8_t v___x_881_; 
v___x_851_ = 2;
v___x_881_ = l_Lean_instBEqMessageSeverity_beq(v_severity_755_, v___x_851_);
if (v___x_881_ == 0)
{
v___y_863_ = v___x_881_;
goto v___jp_862_;
}
else
{
uint8_t v___x_882_; 
lean_inc_ref(v_msgData_754_);
v___x_882_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_754_);
v___y_863_ = v___x_882_;
goto v___jp_862_;
}
v___jp_762_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v_env_777_; lean_object* v_nextMacroScope_778_; lean_object* v_ngen_779_; lean_object* v_auxDeclNGen_780_; lean_object* v_traceState_781_; lean_object* v_cache_782_; lean_object* v_messages_783_; lean_object* v_infoState_784_; lean_object* v_snapshotTasks_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_796_; 
lean_inc(v_openDecls_771_);
lean_inc(v_currNamespace_770_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_currNamespace_770_);
lean_ctor_set(v___x_773_, 1, v_openDecls_771_);
v___x_774_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___y_767_);
lean_inc_ref(v___y_768_);
lean_inc_ref(v___y_766_);
v___x_775_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_775_, 0, v___y_766_);
lean_ctor_set(v___x_775_, 1, v___y_765_);
lean_ctor_set(v___x_775_, 2, v___y_763_);
lean_ctor_set(v___x_775_, 3, v___y_768_);
lean_ctor_set(v___x_775_, 4, v___x_774_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*5, v___y_764_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*5 + 1, v___y_769_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*5 + 2, v_isSilent_756_);
v___x_776_ = lean_st_ref_take(v___y_772_);
v_env_777_ = lean_ctor_get(v___x_776_, 0);
v_nextMacroScope_778_ = lean_ctor_get(v___x_776_, 1);
v_ngen_779_ = lean_ctor_get(v___x_776_, 2);
v_auxDeclNGen_780_ = lean_ctor_get(v___x_776_, 3);
v_traceState_781_ = lean_ctor_get(v___x_776_, 4);
v_cache_782_ = lean_ctor_get(v___x_776_, 5);
v_messages_783_ = lean_ctor_get(v___x_776_, 6);
v_infoState_784_ = lean_ctor_get(v___x_776_, 7);
v_snapshotTasks_785_ = lean_ctor_get(v___x_776_, 8);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_796_ == 0)
{
v___x_787_ = v___x_776_;
v_isShared_788_ = v_isSharedCheck_796_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_snapshotTasks_785_);
lean_inc(v_infoState_784_);
lean_inc(v_messages_783_);
lean_inc(v_cache_782_);
lean_inc(v_traceState_781_);
lean_inc(v_auxDeclNGen_780_);
lean_inc(v_ngen_779_);
lean_inc(v_nextMacroScope_778_);
lean_inc(v_env_777_);
lean_dec(v___x_776_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_796_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_789_ = lean_box(0);
v___x_790_ = l_Lean_MessageLog_add(v___x_775_, v_messages_783_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 6, v___x_790_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_env_777_);
lean_ctor_set(v_reuseFailAlloc_795_, 1, v_nextMacroScope_778_);
lean_ctor_set(v_reuseFailAlloc_795_, 2, v_ngen_779_);
lean_ctor_set(v_reuseFailAlloc_795_, 3, v_auxDeclNGen_780_);
lean_ctor_set(v_reuseFailAlloc_795_, 4, v_traceState_781_);
lean_ctor_set(v_reuseFailAlloc_795_, 5, v_cache_782_);
lean_ctor_set(v_reuseFailAlloc_795_, 6, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_795_, 7, v_infoState_784_);
lean_ctor_set(v_reuseFailAlloc_795_, 8, v_snapshotTasks_785_);
v___x_792_ = v_reuseFailAlloc_795_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_st_ref_put(v___y_772_, v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_789_);
return v___x_794_;
}
}
}
v___jp_797_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_823_; 
v___x_808_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_754_);
v___x_809_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_808_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_823_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_823_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_823_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_inc_ref_n(v___y_801_, 2);
v___x_814_ = l_Lean_FileMap_toPosition(v___y_801_, v___y_805_);
lean_dec(v___y_805_);
v___x_815_ = l_Lean_FileMap_toPosition(v___y_801_, v___y_807_);
lean_dec(v___y_807_);
v___x_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
v___x_817_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
if (v___y_804_ == 0)
{
lean_del_object(v___x_812_);
lean_dec_ref(v___y_798_);
v___y_763_ = v___x_816_;
v___y_764_ = v___y_802_;
v___y_765_ = v___x_814_;
v___y_766_ = v___y_803_;
v___y_767_ = v_a_810_;
v___y_768_ = v___x_817_;
v___y_769_ = v___y_806_;
v_currNamespace_770_ = v___y_800_;
v_openDecls_771_ = v___y_799_;
v___y_772_ = v___y_760_;
goto v___jp_762_;
}
else
{
uint8_t v___x_818_; 
lean_inc(v_a_810_);
v___x_818_ = l_Lean_MessageData_hasTag(v___y_798_, v_a_810_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_821_; 
lean_dec_ref_known(v___x_816_, 1);
lean_dec_ref(v___x_814_);
lean_dec(v_a_810_);
v___x_819_ = lean_box(0);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v___x_819_);
v___x_821_ = v___x_812_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_del_object(v___x_812_);
v___y_763_ = v___x_816_;
v___y_764_ = v___y_802_;
v___y_765_ = v___x_814_;
v___y_766_ = v___y_803_;
v___y_767_ = v_a_810_;
v___y_768_ = v___x_817_;
v___y_769_ = v___y_806_;
v_currNamespace_770_ = v___y_800_;
v_openDecls_771_ = v___y_799_;
v___y_772_ = v___y_760_;
goto v___jp_762_;
}
}
}
}
v___jp_824_:
{
lean_object* v___x_835_; 
v___x_835_ = l_Lean_Syntax_getTailPos_x3f(v___y_829_, v___y_830_);
lean_dec(v___y_829_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_inc(v___y_834_);
v___y_798_ = v___y_825_;
v___y_799_ = v___y_826_;
v___y_800_ = v___y_827_;
v___y_801_ = v___y_828_;
v___y_802_ = v___y_830_;
v___y_803_ = v___y_831_;
v___y_804_ = v___y_832_;
v___y_805_ = v___y_834_;
v___y_806_ = v___y_833_;
v___y_807_ = v___y_834_;
goto v___jp_797_;
}
else
{
lean_object* v_val_836_; 
v_val_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_val_836_);
lean_dec_ref_known(v___x_835_, 1);
v___y_798_ = v___y_825_;
v___y_799_ = v___y_826_;
v___y_800_ = v___y_827_;
v___y_801_ = v___y_828_;
v___y_802_ = v___y_830_;
v___y_803_ = v___y_831_;
v___y_804_ = v___y_832_;
v___y_805_ = v___y_834_;
v___y_806_ = v___y_833_;
v___y_807_ = v_val_836_;
goto v___jp_797_;
}
}
v___jp_837_:
{
lean_object* v_ref_847_; lean_object* v___x_848_; 
v_ref_847_ = l_Lean_replaceRef(v_ref_753_, v___y_843_);
v___x_848_ = l_Lean_Syntax_getPos_x3f(v_ref_847_, v___y_842_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v___x_849_; 
v___x_849_ = lean_unsigned_to_nat(0u);
v___y_825_ = v___y_838_;
v___y_826_ = v___y_839_;
v___y_827_ = v___y_840_;
v___y_828_ = v___y_841_;
v___y_829_ = v_ref_847_;
v___y_830_ = v___y_842_;
v___y_831_ = v___y_844_;
v___y_832_ = v___y_845_;
v___y_833_ = v___y_846_;
v___y_834_ = v___x_849_;
goto v___jp_824_;
}
else
{
lean_object* v_val_850_; 
v_val_850_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v___x_848_, 1);
v___y_825_ = v___y_838_;
v___y_826_ = v___y_839_;
v___y_827_ = v___y_840_;
v___y_828_ = v___y_841_;
v___y_829_ = v_ref_847_;
v___y_830_ = v___y_842_;
v___y_831_ = v___y_844_;
v___y_832_ = v___y_845_;
v___y_833_ = v___y_846_;
v___y_834_ = v_val_850_;
goto v___jp_824_;
}
}
v___jp_852_:
{
if (v___y_861_ == 0)
{
v___y_838_ = v___y_855_;
v___y_839_ = v___y_856_;
v___y_840_ = v___y_857_;
v___y_841_ = v___y_853_;
v___y_842_ = v___y_858_;
v___y_843_ = v___y_859_;
v___y_844_ = v___y_854_;
v___y_845_ = v___y_860_;
v___y_846_ = v_severity_755_;
goto v___jp_837_;
}
else
{
v___y_838_ = v___y_855_;
v___y_839_ = v___y_856_;
v___y_840_ = v___y_857_;
v___y_841_ = v___y_853_;
v___y_842_ = v___y_858_;
v___y_843_ = v___y_859_;
v___y_844_ = v___y_854_;
v___y_845_ = v___y_860_;
v___y_846_ = v___x_851_;
goto v___jp_837_;
}
}
v___jp_862_:
{
if (v___y_863_ == 0)
{
lean_object* v_toCold_864_; lean_object* v_ref_865_; uint8_t v_suppressElabErrors_866_; lean_object* v_fileName_867_; lean_object* v_fileMap_868_; lean_object* v_options_869_; lean_object* v_currNamespace_870_; lean_object* v_openDecls_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___f_874_; uint8_t v___x_875_; uint8_t v___x_876_; 
v_toCold_864_ = lean_ctor_get(v___y_759_, 0);
v_ref_865_ = lean_ctor_get(v___y_759_, 2);
v_suppressElabErrors_866_ = lean_ctor_get_uint8(v___y_759_, sizeof(void*)*3 + 1);
v_fileName_867_ = lean_ctor_get(v_toCold_864_, 0);
v_fileMap_868_ = lean_ctor_get(v_toCold_864_, 1);
v_options_869_ = lean_ctor_get(v_toCold_864_, 2);
v_currNamespace_870_ = lean_ctor_get(v_toCold_864_, 4);
v_openDecls_871_ = lean_ctor_get(v_toCold_864_, 5);
v___x_872_ = lean_box(v_suppressElabErrors_866_);
v___x_873_ = lean_box(v___y_863_);
v___f_874_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_874_, 0, v___x_872_);
lean_closure_set(v___f_874_, 1, v___x_873_);
v___x_875_ = 1;
v___x_876_ = l_Lean_instBEqMessageSeverity_beq(v_severity_755_, v___x_875_);
if (v___x_876_ == 0)
{
v___y_853_ = v_fileMap_868_;
v___y_854_ = v_fileName_867_;
v___y_855_ = v___f_874_;
v___y_856_ = v_openDecls_871_;
v___y_857_ = v_currNamespace_870_;
v___y_858_ = v___y_863_;
v___y_859_ = v_ref_865_;
v___y_860_ = v_suppressElabErrors_866_;
v___y_861_ = v___x_876_;
goto v___jp_852_;
}
else
{
lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_877_ = l_Lean_warningAsError;
v___x_878_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_869_, v___x_877_);
v___y_853_ = v_fileMap_868_;
v___y_854_ = v_fileName_867_;
v___y_855_ = v___f_874_;
v___y_856_ = v_openDecls_871_;
v___y_857_ = v_currNamespace_870_;
v___y_858_ = v___y_863_;
v___y_859_ = v_ref_865_;
v___y_860_ = v_suppressElabErrors_866_;
v___y_861_ = v___x_878_;
goto v___jp_852_;
}
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; 
lean_dec_ref(v_msgData_754_);
v___x_879_ = lean_box(0);
v___x_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
return v___x_880_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(lean_object* v_ref_883_, lean_object* v_msgData_884_, lean_object* v_severity_885_, lean_object* v_isSilent_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_){
_start:
{
uint8_t v_severity_boxed_892_; uint8_t v_isSilent_boxed_893_; lean_object* v_res_894_; 
v_severity_boxed_892_ = lean_unbox(v_severity_885_);
v_isSilent_boxed_893_ = lean_unbox(v_isSilent_886_);
v_res_894_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_883_, v_msgData_884_, v_severity_boxed_892_, v_isSilent_boxed_893_, v___y_887_, v___y_888_, v___y_889_, v___y_890_);
lean_dec(v___y_890_);
lean_dec_ref(v___y_889_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v_ref_883_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(lean_object* v_ref_895_, lean_object* v_msgData_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
uint8_t v___x_904_; uint8_t v___x_905_; lean_object* v___x_906_; 
v___x_904_ = 1;
v___x_905_ = 0;
v___x_906_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_895_, v_msgData_896_, v___x_904_, v___x_905_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(lean_object* v_ref_907_, lean_object* v_msgData_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v_res_916_; 
v_res_916_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_ref_907_, v_msgData_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v_ref_907_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(lean_object* v___x_925_, lean_object* v_as_926_, size_t v_i_927_, size_t v_stop_928_, lean_object* v_b_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_a_938_; uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_eq(v_i_927_, v_stop_928_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v_name_944_; lean_object* v_stx_945_; uint8_t v___y_947_; lean_object* v___x_957_; uint8_t v___x_958_; 
v___x_943_ = lean_array_uget_borrowed(v_as_926_, v_i_927_);
v_name_944_ = lean_ctor_get(v___x_943_, 0);
v_stx_945_ = lean_ctor_get(v___x_943_, 1);
v___x_957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3));
v___x_958_ = lean_name_eq(v_name_944_, v___x_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5));
v___x_960_ = lean_name_eq(v_name_944_, v___x_959_);
if (v___x_960_ == 0)
{
lean_object* v___x_961_; 
v___x_961_ = lean_box(0);
v_a_938_ = v___x_961_;
goto v___jp_937_;
}
else
{
v___y_947_ = v___x_960_;
goto v___jp_946_;
}
}
else
{
lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_nat_dec_lt(v___x_962_, v___x_925_);
v___y_947_ = v___x_963_;
goto v___jp_946_;
}
v___jp_946_:
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0));
lean_inc(v_name_944_);
v___x_949_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_944_, v___y_947_);
v___x_950_ = lean_string_append(v___x_948_, v___x_949_);
lean_dec_ref(v___x_949_);
v___x_951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1));
v___x_952_ = lean_string_append(v___x_950_, v___x_951_);
v___x_953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_953_, 0, v___x_952_);
v___x_954_ = l_Lean_MessageData_ofFormat(v___x_953_);
v___x_955_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(v_stx_945_, v___x_954_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v_a_938_ = v_a_956_;
goto v___jp_937_;
}
else
{
return v___x_955_;
}
}
}
else
{
lean_object* v___x_964_; 
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_b_929_);
return v___x_964_;
}
v___jp_937_:
{
size_t v___x_939_; size_t v___x_940_; 
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_add(v_i_927_, v___x_939_);
v_i_927_ = v___x_940_;
v_b_929_ = v_a_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(lean_object* v___x_965_, lean_object* v_as_966_, lean_object* v_i_967_, lean_object* v_stop_968_, lean_object* v_b_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_){
_start:
{
size_t v_i_boxed_977_; size_t v_stop_boxed_978_; lean_object* v_res_979_; 
v_i_boxed_977_ = lean_unbox_usize(v_i_967_);
lean_dec(v_i_967_);
v_stop_boxed_978_ = lean_unbox_usize(v_stop_968_);
lean_dec(v_stop_968_);
v_res_979_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_965_, v_as_966_, v_i_boxed_977_, v_stop_boxed_978_, v_b_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec_ref(v_as_966_);
lean_dec(v___x_965_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(lean_object* v___x_980_, lean_object* v_as_981_, size_t v_i_982_, size_t v_stop_983_, lean_object* v_b_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_a_993_; lean_object* v___y_998_; uint8_t v___x_1000_; 
v___x_1000_ = lean_usize_dec_eq(v_i_982_, v_stop_983_);
if (v___x_1000_ == 0)
{
lean_object* v___x_1001_; lean_object* v_modifiers_1002_; lean_object* v_attrs_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1001_ = lean_array_uget_borrowed(v_as_981_, v_i_982_);
v_modifiers_1002_ = lean_ctor_get(v___x_1001_, 2);
v_attrs_1003_ = lean_ctor_get(v_modifiers_1002_, 2);
v___x_1004_ = lean_unsigned_to_nat(0u);
v___x_1005_ = lean_array_get_size(v_attrs_1003_);
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_nat_dec_lt(v___x_1004_, v___x_1005_);
if (v___x_1007_ == 0)
{
v_a_993_ = v___x_1006_;
goto v___jp_992_;
}
else
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_nat_dec_le(v___x_1005_, v___x_1005_);
if (v___x_1008_ == 0)
{
if (v___x_1007_ == 0)
{
v_a_993_ = v___x_1006_;
goto v___jp_992_;
}
else
{
size_t v___x_1009_; size_t v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = lean_usize_of_nat(v___x_1005_);
v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_980_, v_attrs_1003_, v___x_1009_, v___x_1010_, v___x_1006_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
v___y_998_ = v___x_1011_;
goto v___jp_997_;
}
}
else
{
size_t v___x_1012_; size_t v___x_1013_; lean_object* v___x_1014_; 
v___x_1012_ = ((size_t)0ULL);
v___x_1013_ = lean_usize_of_nat(v___x_1005_);
v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v___x_980_, v_attrs_1003_, v___x_1012_, v___x_1013_, v___x_1006_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
v___y_998_ = v___x_1014_;
goto v___jp_997_;
}
}
}
else
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v_b_984_);
return v___x_1015_;
}
v___jp_992_:
{
size_t v___x_994_; size_t v___x_995_; 
v___x_994_ = ((size_t)1ULL);
v___x_995_ = lean_usize_add(v_i_982_, v___x_994_);
v_i_982_ = v___x_995_;
v_b_984_ = v_a_993_;
goto _start;
}
v___jp_997_:
{
if (lean_obj_tag(v___y_998_) == 0)
{
lean_object* v_a_999_; 
v_a_999_ = lean_ctor_get(v___y_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___y_998_, 1);
v_a_993_ = v_a_999_;
goto v___jp_992_;
}
else
{
return v___y_998_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(lean_object* v___x_1016_, lean_object* v_as_1017_, lean_object* v_i_1018_, lean_object* v_stop_1019_, lean_object* v_b_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
size_t v_i_boxed_1028_; size_t v_stop_boxed_1029_; lean_object* v_res_1030_; 
v_i_boxed_1028_ = lean_unbox_usize(v_i_1018_);
lean_dec(v_i_1018_);
v_stop_boxed_1029_ = lean_unbox_usize(v_stop_1019_);
lean_dec(v_stop_1019_);
v_res_1030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1016_, v_as_1017_, v_i_boxed_1028_, v_stop_boxed_1029_, v_b_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec_ref(v_as_1017_);
lean_dec(v___x_1016_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(size_t v_sz_1031_, size_t v_i_1032_, lean_object* v_bs_1033_){
_start:
{
uint8_t v___x_1034_; 
v___x_1034_ = lean_usize_dec_lt(v_i_1032_, v_sz_1031_);
if (v___x_1034_ == 0)
{
return v_bs_1033_;
}
else
{
lean_object* v_v_1035_; lean_object* v_termination_1036_; lean_object* v_decreasingBy_x3f_1037_; lean_object* v___x_1038_; lean_object* v_bs_x27_1039_; size_t v___x_1040_; size_t v___x_1041_; lean_object* v___x_1042_; 
v_v_1035_ = lean_array_uget_borrowed(v_bs_1033_, v_i_1032_);
v_termination_1036_ = lean_ctor_get(v_v_1035_, 8);
v_decreasingBy_x3f_1037_ = lean_ctor_get(v_termination_1036_, 4);
lean_inc(v_decreasingBy_x3f_1037_);
v___x_1038_ = lean_unsigned_to_nat(0u);
v_bs_x27_1039_ = lean_array_uset(v_bs_1033_, v_i_1032_, v___x_1038_);
v___x_1040_ = ((size_t)1ULL);
v___x_1041_ = lean_usize_add(v_i_1032_, v___x_1040_);
v___x_1042_ = lean_array_uset(v_bs_x27_1039_, v_i_1032_, v_decreasingBy_x3f_1037_);
v_i_1032_ = v___x_1041_;
v_bs_1033_ = v___x_1042_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(lean_object* v_sz_1044_, lean_object* v_i_1045_, lean_object* v_bs_1046_){
_start:
{
size_t v_sz_boxed_1047_; size_t v_i_boxed_1048_; lean_object* v_res_1049_; 
v_sz_boxed_1047_ = lean_unbox_usize(v_sz_1044_);
lean_dec(v_sz_1044_);
v_i_boxed_1048_ = lean_unbox_usize(v_i_1045_);
lean_dec(v_i_1045_);
v_res_1049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_1047_, v_i_boxed_1048_, v_bs_1046_);
return v_res_1049_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_1050_; double v___x_1051_; 
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1051_ = lean_float_of_nat(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(lean_object* v_cls_1054_, lean_object* v_msg_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_ref_1061_; lean_object* v___x_1062_; lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1107_; 
v_ref_1061_ = lean_ctor_get(v___y_1058_, 2);
v___x_1062_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1107_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1107_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v_traceState_1068_; lean_object* v_env_1069_; lean_object* v_nextMacroScope_1070_; lean_object* v_ngen_1071_; lean_object* v_auxDeclNGen_1072_; lean_object* v_cache_1073_; lean_object* v_messages_1074_; lean_object* v_infoState_1075_; lean_object* v_snapshotTasks_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1106_; 
v___x_1067_ = lean_st_ref_take(v___y_1059_);
v_traceState_1068_ = lean_ctor_get(v___x_1067_, 4);
v_env_1069_ = lean_ctor_get(v___x_1067_, 0);
v_nextMacroScope_1070_ = lean_ctor_get(v___x_1067_, 1);
v_ngen_1071_ = lean_ctor_get(v___x_1067_, 2);
v_auxDeclNGen_1072_ = lean_ctor_get(v___x_1067_, 3);
v_cache_1073_ = lean_ctor_get(v___x_1067_, 5);
v_messages_1074_ = lean_ctor_get(v___x_1067_, 6);
v_infoState_1075_ = lean_ctor_get(v___x_1067_, 7);
v_snapshotTasks_1076_ = lean_ctor_get(v___x_1067_, 8);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1078_ = v___x_1067_;
v_isShared_1079_ = v_isSharedCheck_1106_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_snapshotTasks_1076_);
lean_inc(v_infoState_1075_);
lean_inc(v_messages_1074_);
lean_inc(v_cache_1073_);
lean_inc(v_traceState_1068_);
lean_inc(v_auxDeclNGen_1072_);
lean_inc(v_ngen_1071_);
lean_inc(v_nextMacroScope_1070_);
lean_inc(v_env_1069_);
lean_dec(v___x_1067_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1106_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
uint64_t v_tid_1080_; lean_object* v_traces_1081_; lean_object* v___x_1083_; uint8_t v_isShared_1084_; uint8_t v_isSharedCheck_1105_; 
v_tid_1080_ = lean_ctor_get_uint64(v_traceState_1068_, sizeof(void*)*1);
v_traces_1081_ = lean_ctor_get(v_traceState_1068_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_traceState_1068_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1083_ = v_traceState_1068_;
v_isShared_1084_ = v_isSharedCheck_1105_;
goto v_resetjp_1082_;
}
else
{
lean_inc(v_traces_1081_);
lean_dec(v_traceState_1068_);
v___x_1083_ = lean_box(0);
v_isShared_1084_ = v_isSharedCheck_1105_;
goto v_resetjp_1082_;
}
v_resetjp_1082_:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; double v___x_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_box(0);
v___x_1087_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0);
v___x_1088_ = 0;
v___x_1089_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0));
v___x_1090_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1090_, 0, v_cls_1054_);
lean_ctor_set(v___x_1090_, 1, v___x_1086_);
lean_ctor_set(v___x_1090_, 2, v___x_1089_);
lean_ctor_set_float(v___x_1090_, sizeof(void*)*3, v___x_1087_);
lean_ctor_set_float(v___x_1090_, sizeof(void*)*3 + 8, v___x_1087_);
lean_ctor_set_uint8(v___x_1090_, sizeof(void*)*3 + 16, v___x_1088_);
v___x_1091_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1));
v___x_1092_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v_a_1063_);
lean_ctor_set(v___x_1092_, 2, v___x_1091_);
lean_inc(v_ref_1061_);
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_ref_1061_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_PersistentArray_push___redArg(v_traces_1081_, v___x_1093_);
if (v_isShared_1084_ == 0)
{
lean_ctor_set(v___x_1083_, 0, v___x_1094_);
v___x_1096_ = v___x_1083_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1094_);
lean_ctor_set_uint64(v_reuseFailAlloc_1104_, sizeof(void*)*1, v_tid_1080_);
v___x_1096_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1098_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 4, v___x_1096_);
v___x_1098_ = v___x_1078_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_env_1069_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_nextMacroScope_1070_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v_ngen_1071_);
lean_ctor_set(v_reuseFailAlloc_1103_, 3, v_auxDeclNGen_1072_);
lean_ctor_set(v_reuseFailAlloc_1103_, 4, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1103_, 5, v_cache_1073_);
lean_ctor_set(v_reuseFailAlloc_1103_, 6, v_messages_1074_);
lean_ctor_set(v_reuseFailAlloc_1103_, 7, v_infoState_1075_);
lean_ctor_set(v_reuseFailAlloc_1103_, 8, v_snapshotTasks_1076_);
v___x_1098_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = lean_st_ref_put(v___y_1059_, v___x_1098_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1085_);
v___x_1101_ = v___x_1065_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1085_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(lean_object* v_cls_1108_, lean_object* v_msg_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_1108_, v_msg_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
lean_dec(v___y_1113_);
lean_dec_ref(v___y_1112_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
return v_res_1115_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__3___closed__0));
v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(lean_object* v_fst_1119_, lean_object* v_snd_1120_, size_t v_sz_1121_, size_t v___x_1122_, lean_object* v_a_1123_, lean_object* v_fixedArgs_1124_, lean_object* v_fst_1125_, lean_object* v___x_1126_, lean_object* v___x_1127_, lean_object* v___x_1128_, lean_object* v_wfRel_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v___y_1138_; lean_object* v___y_1139_; lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v___y_1142_; lean_object* v___y_1143_; lean_object* v___y_1144_; lean_object* v_a_1145_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v_toCold_1294_; lean_object* v_options_1295_; uint8_t v_hasTrace_1296_; 
v_toCold_1294_ = lean_ctor_get(v___y_1134_, 0);
v_options_1295_ = lean_ctor_get(v_toCold_1294_, 2);
v_hasTrace_1296_ = lean_ctor_get_uint8(v_options_1295_, sizeof(void*)*1);
if (v_hasTrace_1296_ == 0)
{
lean_dec(v___x_1128_);
v___y_1270_ = v___y_1130_;
v___y_1271_ = v___y_1131_;
v___y_1272_ = v___y_1132_;
v___y_1273_ = v___y_1133_;
v___y_1274_ = v___y_1134_;
v___y_1275_ = v___y_1135_;
goto v___jp_1269_;
}
else
{
lean_object* v_inheritedTraceOptions_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v_inheritedTraceOptions_1297_ = lean_ctor_get(v_toCold_1294_, 11);
v___x_1298_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__2___closed__1));
lean_inc(v___x_1128_);
v___x_1299_ = l_Lean_Name_append(v___x_1298_, v___x_1128_);
v___x_1300_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1297_, v_options_1295_, v___x_1299_);
lean_dec(v___x_1299_);
if (v___x_1300_ == 0)
{
lean_dec(v___x_1128_);
v___y_1270_ = v___y_1130_;
v___y_1271_ = v___y_1131_;
v___y_1272_ = v___y_1132_;
v___y_1273_ = v___y_1133_;
v___y_1274_ = v___y_1134_;
v___y_1275_ = v___y_1135_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1301_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__3___closed__1, &l_Lean_Elab_wfRecursion___lam__3___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__3___closed__1);
lean_inc_ref(v_wfRel_1129_);
v___x_1302_ = l_Lean_MessageData_ofExpr(v_wfRel_1129_);
v___x_1303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1301_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1128_, v___x_1303_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_dec_ref_known(v___x_1304_, 1);
v___y_1270_ = v___y_1130_;
v___y_1271_ = v___y_1131_;
v___y_1272_ = v___y_1132_;
v___y_1273_ = v___y_1133_;
v___y_1274_ = v___y_1134_;
v___y_1275_ = v___y_1135_;
goto v___jp_1269_;
}
else
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1312_; 
lean_dec_ref(v_wfRel_1129_);
lean_dec_ref(v___x_1126_);
lean_dec_ref(v_fst_1125_);
lean_dec_ref(v_fixedArgs_1124_);
lean_dec_ref(v_a_1123_);
lean_dec_ref(v_fst_1119_);
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1312_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1312_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1312_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
}
}
}
v___jp_1137_:
{
lean_object* v___x_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1153_; 
v___x_1146_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1143_, v___y_1141_, v___y_1142_);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1153_ == 0)
{
lean_object* v_unused_1154_; 
v_unused_1154_ = lean_ctor_get(v___x_1146_, 0);
lean_dec(v_unused_1154_);
v___x_1148_ = v___x_1146_;
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
else
{
lean_dec(v___x_1146_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1153_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 1);
lean_ctor_set(v___x_1148_, 0, v_a_1145_);
v___x_1151_ = v___x_1148_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_a_1145_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
v___jp_1155_:
{
if (lean_obj_tag(v___y_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1165_; lean_object* v_env_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_a_1164_ = lean_ctor_get(v___y_1163_, 0);
lean_inc(v_a_1164_);
lean_dec_ref_known(v___y_1163_, 1);
v___x_1165_ = lean_st_ref_get(v___y_1160_);
v_env_1166_ = lean_ctor_get(v___x_1165_, 0);
lean_inc_ref_n(v_env_1166_, 2);
lean_dec(v___x_1165_);
v___x_1167_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v___y_1161_, v___y_1159_, v___y_1160_);
lean_dec_ref(v___x_1167_);
v___x_1168_ = l_Lean_Meta_unfoldDeclsFrom(v_env_1166_, v_a_1164_, v___y_1162_, v___y_1160_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1228_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1171_ = v___x_1168_;
v_isShared_1172_ = v_isSharedCheck_1228_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1168_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1228_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1173_; lean_object* v_env_1174_; lean_object* v_nextMacroScope_1175_; lean_object* v_ngen_1176_; lean_object* v_auxDeclNGen_1177_; lean_object* v_traceState_1178_; lean_object* v_messages_1179_; lean_object* v_infoState_1180_; lean_object* v_snapshotTasks_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1226_; 
v___x_1173_ = lean_st_ref_take(v___y_1160_);
v_env_1174_ = lean_ctor_get(v___x_1173_, 0);
v_nextMacroScope_1175_ = lean_ctor_get(v___x_1173_, 1);
v_ngen_1176_ = lean_ctor_get(v___x_1173_, 2);
v_auxDeclNGen_1177_ = lean_ctor_get(v___x_1173_, 3);
v_traceState_1178_ = lean_ctor_get(v___x_1173_, 4);
v_messages_1179_ = lean_ctor_get(v___x_1173_, 6);
v_infoState_1180_ = lean_ctor_get(v___x_1173_, 7);
v_snapshotTasks_1181_ = lean_ctor_get(v___x_1173_, 8);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v___x_1173_, 5);
lean_dec(v_unused_1227_);
v___x_1183_ = v___x_1173_;
v_isShared_1184_ = v_isSharedCheck_1226_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_snapshotTasks_1181_);
lean_inc(v_infoState_1180_);
lean_inc(v_messages_1179_);
lean_inc(v_traceState_1178_);
lean_inc(v_auxDeclNGen_1177_);
lean_inc(v_ngen_1176_);
lean_inc(v_nextMacroScope_1175_);
lean_inc(v_env_1174_);
lean_dec(v___x_1173_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1226_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1185_ = l_Lean_copyExtraModUses(v_env_1166_, v_env_1174_);
v___x_1186_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 5, v___x_1186_);
lean_ctor_set(v___x_1183_, 0, v___x_1185_);
v___x_1188_ = v___x_1183_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_nextMacroScope_1175_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v_ngen_1176_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v_auxDeclNGen_1177_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v_traceState_1178_);
lean_ctor_set(v_reuseFailAlloc_1225_, 5, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1225_, 6, v_messages_1179_);
lean_ctor_set(v_reuseFailAlloc_1225_, 7, v_infoState_1180_);
lean_ctor_set(v_reuseFailAlloc_1225_, 8, v_snapshotTasks_1181_);
v___x_1188_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_mctx_1191_; lean_object* v_zetaDeltaFVarIds_1192_; lean_object* v_postponed_1193_; lean_object* v_diag_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1223_; 
v___x_1189_ = lean_st_ref_put(v___y_1160_, v___x_1188_);
v___x_1190_ = lean_st_ref_take(v___y_1159_);
v_mctx_1191_ = lean_ctor_get(v___x_1190_, 0);
v_zetaDeltaFVarIds_1192_ = lean_ctor_get(v___x_1190_, 2);
v_postponed_1193_ = lean_ctor_get(v___x_1190_, 3);
v_diag_1194_ = lean_ctor_get(v___x_1190_, 4);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1223_ == 0)
{
lean_object* v_unused_1224_; 
v_unused_1224_ = lean_ctor_get(v___x_1190_, 1);
lean_dec(v_unused_1224_);
v___x_1196_ = v___x_1190_;
v_isShared_1197_ = v_isSharedCheck_1223_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_diag_1194_);
lean_inc(v_postponed_1193_);
lean_inc(v_zetaDeltaFVarIds_1192_);
lean_inc(v_mctx_1191_);
lean_dec(v___x_1190_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1223_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1200_; 
v___x_1198_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v___x_1198_);
v___x_1200_ = v___x_1196_;
goto v_reusejp_1199_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_mctx_1191_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_zetaDeltaFVarIds_1192_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_postponed_1193_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_diag_1194_);
v___x_1200_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1199_;
}
v_reusejp_1199_:
{
lean_object* v___x_1201_; lean_object* v_ref_1202_; uint8_t v_kind_1203_; lean_object* v_levelParams_1204_; lean_object* v_modifiers_1205_; lean_object* v_declName_1206_; lean_object* v_binders_1207_; lean_object* v_numSectionVars_1208_; lean_object* v_type_1209_; lean_object* v_termination_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1220_; 
v___x_1201_ = lean_st_ref_put(v___y_1159_, v___x_1200_);
v_ref_1202_ = lean_ctor_get(v_fst_1119_, 0);
v_kind_1203_ = lean_ctor_get_uint8(v_fst_1119_, sizeof(void*)*9);
v_levelParams_1204_ = lean_ctor_get(v_fst_1119_, 1);
v_modifiers_1205_ = lean_ctor_get(v_fst_1119_, 2);
v_declName_1206_ = lean_ctor_get(v_fst_1119_, 3);
v_binders_1207_ = lean_ctor_get(v_fst_1119_, 4);
v_numSectionVars_1208_ = lean_ctor_get(v_fst_1119_, 5);
v_type_1209_ = lean_ctor_get(v_fst_1119_, 6);
v_termination_1210_ = lean_ctor_get(v_fst_1119_, 8);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_fst_1119_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_fst_1119_, 7);
lean_dec(v_unused_1221_);
v___x_1212_ = v_fst_1119_;
v_isShared_1213_ = v_isSharedCheck_1220_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_termination_1210_);
lean_inc(v_type_1209_);
lean_inc(v_numSectionVars_1208_);
lean_inc(v_binders_1207_);
lean_inc(v_declName_1206_);
lean_inc(v_modifiers_1205_);
lean_inc(v_levelParams_1204_);
lean_inc(v_ref_1202_);
lean_dec(v_fst_1119_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1220_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 7, v_a_1169_);
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_ref_1202_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_levelParams_1204_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_modifiers_1205_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v_declName_1206_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v_binders_1207_);
lean_ctor_set(v_reuseFailAlloc_1219_, 5, v_numSectionVars_1208_);
lean_ctor_set(v_reuseFailAlloc_1219_, 6, v_type_1209_);
lean_ctor_set(v_reuseFailAlloc_1219_, 7, v_a_1169_);
lean_ctor_set(v_reuseFailAlloc_1219_, 8, v_termination_1210_);
lean_ctor_set_uint8(v_reuseFailAlloc_1219_, sizeof(void*)*9, v_kind_1203_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1217_; 
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 0, v___x_1215_);
v___x_1217_ = v___x_1171_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1215_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
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
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec_ref(v_env_1166_);
lean_dec_ref(v_fst_1119_);
v_a_1229_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1168_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1168_);
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
lean_object* v_a_1237_; 
lean_dec_ref(v_fst_1119_);
v_a_1237_ = lean_ctor_get(v___y_1163_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___y_1163_, 1);
v___y_1138_ = v___y_1156_;
v___y_1139_ = v___y_1157_;
v___y_1140_ = v___y_1158_;
v___y_1141_ = v___y_1159_;
v___y_1142_ = v___y_1160_;
v___y_1143_ = v___y_1161_;
v___y_1144_ = v___y_1162_;
v_a_1145_ = v_a_1237_;
goto v___jp_1137_;
}
}
v___jp_1238_:
{
lean_object* v___x_1245_; lean_object* v_env_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_st_ref_get(v___y_1244_);
v_env_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc_ref(v_env_1246_);
lean_dec(v___x_1245_);
v___x_1247_ = l_Lean_Elab_addAsAxiom___redArg(v_snd_1120_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_dec_ref_known(v___x_1247_, 1);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_1121_, v___x_1122_, v_a_1123_);
lean_inc_ref(v_fst_1119_);
v___x_1249_ = l_Lean_Elab_WF_mkFix(v_fst_1119_, v_fixedArgs_1124_, v_fst_1125_, v_wfRel_1129_, v___x_1126_, v___x_1248_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; lean_object* v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_1250_, v___y_1243_, v___y_1244_);
v___y_1156_ = v___y_1239_;
v___y_1157_ = v___y_1241_;
v___y_1158_ = v___y_1240_;
v___y_1159_ = v___y_1242_;
v___y_1160_ = v___y_1244_;
v___y_1161_ = v_env_1246_;
v___y_1162_ = v___y_1243_;
v___y_1163_ = v___x_1251_;
goto v___jp_1155_;
}
else
{
v___y_1156_ = v___y_1239_;
v___y_1157_ = v___y_1241_;
v___y_1158_ = v___y_1240_;
v___y_1159_ = v___y_1242_;
v___y_1160_ = v___y_1244_;
v___y_1161_ = v_env_1246_;
v___y_1162_ = v___y_1243_;
v___y_1163_ = v___x_1249_;
goto v___jp_1155_;
}
}
else
{
lean_object* v_a_1252_; 
lean_dec_ref(v_wfRel_1129_);
lean_dec_ref(v___x_1126_);
lean_dec_ref(v_fst_1125_);
lean_dec_ref(v_fixedArgs_1124_);
lean_dec_ref(v_a_1123_);
lean_dec_ref(v_fst_1119_);
v_a_1252_ = lean_ctor_get(v___x_1247_, 0);
lean_inc(v_a_1252_);
lean_dec_ref_known(v___x_1247_, 1);
v___y_1138_ = v___y_1239_;
v___y_1139_ = v___y_1241_;
v___y_1140_ = v___y_1240_;
v___y_1141_ = v___y_1242_;
v___y_1142_ = v___y_1244_;
v___y_1143_ = v_env_1246_;
v___y_1144_ = v___y_1243_;
v_a_1145_ = v_a_1252_;
goto v___jp_1137_;
}
}
v___jp_1253_:
{
if (lean_obj_tag(v___y_1260_) == 0)
{
lean_dec_ref_known(v___y_1260_, 1);
v___y_1239_ = v___y_1256_;
v___y_1240_ = v___y_1259_;
v___y_1241_ = v___y_1257_;
v___y_1242_ = v___y_1254_;
v___y_1243_ = v___y_1258_;
v___y_1244_ = v___y_1255_;
goto v___jp_1238_;
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec_ref(v_wfRel_1129_);
lean_dec_ref(v___x_1126_);
lean_dec_ref(v_fst_1125_);
lean_dec_ref(v_fixedArgs_1124_);
lean_dec_ref(v_a_1123_);
lean_dec_ref(v_fst_1119_);
v_a_1261_ = lean_ctor_get(v___y_1260_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___y_1260_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___y_1260_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___y_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
v___jp_1269_:
{
lean_object* v___x_1276_; 
lean_inc_ref(v_wfRel_1129_);
v___x_1276_ = l_Lean_Elab_WF_isNatLtWF(v_wfRel_1129_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
if (lean_obj_tag(v___x_1276_) == 0)
{
lean_object* v_a_1277_; 
v_a_1277_ = lean_ctor_get(v___x_1276_, 0);
lean_inc(v_a_1277_);
lean_dec_ref_known(v___x_1276_, 1);
if (lean_obj_tag(v_a_1277_) == 0)
{
lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_array_get_size(v_a_1123_);
v___x_1280_ = lean_nat_dec_lt(v___x_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
v___y_1239_ = v___y_1270_;
v___y_1240_ = v___y_1271_;
v___y_1241_ = v___y_1272_;
v___y_1242_ = v___y_1273_;
v___y_1243_ = v___y_1274_;
v___y_1244_ = v___y_1275_;
goto v___jp_1238_;
}
else
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_nat_dec_le(v___x_1279_, v___x_1279_);
if (v___x_1281_ == 0)
{
if (v___x_1280_ == 0)
{
v___y_1239_ = v___y_1270_;
v___y_1240_ = v___y_1271_;
v___y_1241_ = v___y_1272_;
v___y_1242_ = v___y_1273_;
v___y_1243_ = v___y_1274_;
v___y_1244_ = v___y_1275_;
goto v___jp_1238_;
}
else
{
size_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_usize_of_nat(v___x_1279_);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1279_, v_a_1123_, v___x_1122_, v___x_1282_, v___x_1127_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
v___y_1254_ = v___y_1273_;
v___y_1255_ = v___y_1275_;
v___y_1256_ = v___y_1270_;
v___y_1257_ = v___y_1272_;
v___y_1258_ = v___y_1274_;
v___y_1259_ = v___y_1271_;
v___y_1260_ = v___x_1283_;
goto v___jp_1253_;
}
}
else
{
size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_usize_of_nat(v___x_1279_);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v___x_1279_, v_a_1123_, v___x_1122_, v___x_1284_, v___x_1127_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_, v___y_1274_, v___y_1275_);
v___y_1254_ = v___y_1273_;
v___y_1255_ = v___y_1275_;
v___y_1256_ = v___y_1270_;
v___y_1257_ = v___y_1272_;
v___y_1258_ = v___y_1274_;
v___y_1259_ = v___y_1271_;
v___y_1260_ = v___x_1285_;
goto v___jp_1253_;
}
}
}
else
{
lean_dec_ref_known(v_a_1277_, 1);
v___y_1239_ = v___y_1270_;
v___y_1240_ = v___y_1271_;
v___y_1241_ = v___y_1272_;
v___y_1242_ = v___y_1273_;
v___y_1243_ = v___y_1274_;
v___y_1244_ = v___y_1275_;
goto v___jp_1238_;
}
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
lean_dec_ref(v_wfRel_1129_);
lean_dec_ref(v___x_1126_);
lean_dec_ref(v_fst_1125_);
lean_dec_ref(v_fixedArgs_1124_);
lean_dec_ref(v_a_1123_);
lean_dec_ref(v_fst_1119_);
v_a_1286_ = lean_ctor_get(v___x_1276_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1276_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1276_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args){
lean_object* v_fst_1313_ = _args[0];
lean_object* v_snd_1314_ = _args[1];
lean_object* v_sz_1315_ = _args[2];
lean_object* v___x_1316_ = _args[3];
lean_object* v_a_1317_ = _args[4];
lean_object* v_fixedArgs_1318_ = _args[5];
lean_object* v_fst_1319_ = _args[6];
lean_object* v___x_1320_ = _args[7];
lean_object* v___x_1321_ = _args[8];
lean_object* v___x_1322_ = _args[9];
lean_object* v_wfRel_1323_ = _args[10];
lean_object* v___y_1324_ = _args[11];
lean_object* v___y_1325_ = _args[12];
lean_object* v___y_1326_ = _args[13];
lean_object* v___y_1327_ = _args[14];
lean_object* v___y_1328_ = _args[15];
lean_object* v___y_1329_ = _args[16];
lean_object* v___y_1330_ = _args[17];
_start:
{
size_t v_sz_boxed_1331_; size_t v___x_44799__boxed_1332_; lean_object* v_res_1333_; 
v_sz_boxed_1331_ = lean_unbox_usize(v_sz_1315_);
lean_dec(v_sz_1315_);
v___x_44799__boxed_1332_ = lean_unbox_usize(v___x_1316_);
lean_dec(v___x_1316_);
v_res_1333_ = l_Lean_Elab_wfRecursion___lam__3(v_fst_1313_, v_snd_1314_, v_sz_boxed_1331_, v___x_44799__boxed_1332_, v_a_1317_, v_fixedArgs_1318_, v_fst_1319_, v___x_1320_, v___x_1321_, v___x_1322_, v_wfRel_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec_ref(v_snd_1314_);
return v_res_1333_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l_Lean_Elab_wfRecursion___lam__4___closed__0));
v___x_1336_ = l_Lean_stringToMessageData(v___x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4(size_t v_sz_1337_, size_t v___x_1338_, lean_object* v_a_1339_, lean_object* v_fst_1340_, lean_object* v_snd_1341_, lean_object* v_fst_1342_, lean_object* v___x_1343_, lean_object* v___x_1344_, lean_object* v_declName_1345_, lean_object* v_fst_1346_, lean_object* v_wf_1347_, lean_object* v_fixedArgs_1348_, lean_object* v_type_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = l_Lean_Meta_whnfForall(v_type_1349_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint8_t v___x_1372_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
lean_inc(v_a_1358_);
lean_dec_ref_known(v___x_1357_, 1);
v___x_1372_ = l_Lean_Expr_isForall(v_a_1358_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref(v_fixedArgs_1348_);
lean_dec_ref(v_wf_1347_);
lean_dec_ref(v_fst_1346_);
lean_dec(v_declName_1345_);
lean_dec(v___x_1344_);
lean_dec_ref(v_fst_1342_);
lean_dec_ref(v_snd_1341_);
lean_dec_ref(v_fst_1340_);
lean_dec_ref(v_a_1339_);
v___x_1373_ = lean_obj_once(&l_Lean_Elab_wfRecursion___lam__4___closed__1, &l_Lean_Elab_wfRecursion___lam__4___closed__1_once, _init_l_Lean_Elab_wfRecursion___lam__4___closed__1);
v___x_1374_ = l_Lean_MessageData_ofExpr(v_a_1358_);
v___x_1375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v___x_1375_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
else
{
v___y_1360_ = v___y_1350_;
v___y_1361_ = v___y_1351_;
v___y_1362_ = v___y_1352_;
v___y_1363_ = v___y_1353_;
v___y_1364_ = v___y_1354_;
v___y_1365_ = v___y_1355_;
goto v___jp_1359_;
}
v___jp_1359_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___f_1370_; lean_object* v___x_1371_; 
v___x_1366_ = l_Lean_Expr_bindingDomain_x21(v_a_1358_);
lean_dec(v_a_1358_);
lean_inc_ref(v_a_1339_);
v___x_1367_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_sz_1337_, v___x_1338_, v_a_1339_);
v___x_1368_ = lean_box_usize(v_sz_1337_);
v___x_1369_ = lean_box_usize(v___x_1338_);
lean_inc_ref(v___x_1367_);
lean_inc_ref(v_fst_1342_);
lean_inc_ref(v_fixedArgs_1348_);
v___f_1370_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 18, 10);
lean_closure_set(v___f_1370_, 0, v_fst_1340_);
lean_closure_set(v___f_1370_, 1, v_snd_1341_);
lean_closure_set(v___f_1370_, 2, v___x_1368_);
lean_closure_set(v___f_1370_, 3, v___x_1369_);
lean_closure_set(v___f_1370_, 4, v_a_1339_);
lean_closure_set(v___f_1370_, 5, v_fixedArgs_1348_);
lean_closure_set(v___f_1370_, 6, v_fst_1342_);
lean_closure_set(v___f_1370_, 7, v___x_1367_);
lean_closure_set(v___f_1370_, 8, v___x_1343_);
lean_closure_set(v___f_1370_, 9, v___x_1344_);
v___x_1371_ = l_Lean_Elab_WF_elabWFRel___redArg(v___x_1367_, v_declName_1345_, v_fst_1346_, v_fixedArgs_1348_, v_fst_1342_, v___x_1366_, v_wf_1347_, v___f_1370_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v___x_1371_;
}
}
else
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_dec_ref(v_fixedArgs_1348_);
lean_dec_ref(v_wf_1347_);
lean_dec_ref(v_fst_1346_);
lean_dec(v_declName_1345_);
lean_dec(v___x_1344_);
lean_dec_ref(v_fst_1342_);
lean_dec_ref(v_snd_1341_);
lean_dec_ref(v_fst_1340_);
lean_dec_ref(v_a_1339_);
v_a_1385_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1357_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1357_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__4___boxed(lean_object** _args){
lean_object* v_sz_1393_ = _args[0];
lean_object* v___x_1394_ = _args[1];
lean_object* v_a_1395_ = _args[2];
lean_object* v_fst_1396_ = _args[3];
lean_object* v_snd_1397_ = _args[4];
lean_object* v_fst_1398_ = _args[5];
lean_object* v___x_1399_ = _args[6];
lean_object* v___x_1400_ = _args[7];
lean_object* v_declName_1401_ = _args[8];
lean_object* v_fst_1402_ = _args[9];
lean_object* v_wf_1403_ = _args[10];
lean_object* v_fixedArgs_1404_ = _args[11];
lean_object* v_type_1405_ = _args[12];
lean_object* v___y_1406_ = _args[13];
lean_object* v___y_1407_ = _args[14];
lean_object* v___y_1408_ = _args[15];
lean_object* v___y_1409_ = _args[16];
lean_object* v___y_1410_ = _args[17];
lean_object* v___y_1411_ = _args[18];
lean_object* v___y_1412_ = _args[19];
_start:
{
size_t v_sz_boxed_1413_; size_t v___x_45158__boxed_1414_; lean_object* v_res_1415_; 
v_sz_boxed_1413_ = lean_unbox_usize(v_sz_1393_);
lean_dec(v_sz_1393_);
v___x_45158__boxed_1414_ = lean_unbox_usize(v___x_1394_);
lean_dec(v___x_1394_);
v_res_1415_ = l_Lean_Elab_wfRecursion___lam__4(v_sz_boxed_1413_, v___x_45158__boxed_1414_, v_a_1395_, v_fst_1396_, v_snd_1397_, v_fst_1398_, v___x_1399_, v___x_1400_, v_declName_1401_, v_fst_1402_, v_wf_1403_, v_fixedArgs_1404_, v_type_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
lean_dec(v___y_1411_);
lean_dec_ref(v___y_1410_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5(lean_object* v_a_1416_, lean_object* v_fst_1417_, lean_object* v_fst_1418_, lean_object* v_fst_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_Elab_WF_guessLex(v_a_1416_, v_fst_1417_, v_fst_1418_, v_fst_1419_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__5___boxed(lean_object* v_a_1428_, lean_object* v_fst_1429_, lean_object* v_fst_1430_, lean_object* v_fst_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Lean_Elab_wfRecursion___lam__5(v_a_1428_, v_fst_1429_, v_fst_1430_, v_fst_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
lean_dec(v___y_1437_);
lean_dec_ref(v___y_1436_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(lean_object* v_env_1440_, lean_object* v_x_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v___x_1449_; lean_object* v_env_1450_; lean_object* v_a_1452_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1449_ = lean_st_ref_get(v___y_1447_);
v_env_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc_ref(v_env_1450_);
lean_dec(v___x_1449_);
v___x_1462_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1440_, v___y_1445_, v___y_1447_);
lean_dec_ref(v___x_1462_);
lean_inc(v___y_1447_);
lean_inc_ref(v___y_1446_);
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
v___x_1463_ = lean_apply_7(v_x_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, lean_box(0));
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; lean_object* v___x_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
v___x_1465_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1450_, v___y_1445_, v___y_1447_);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1465_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; 
v_unused_1473_ = lean_ctor_get(v___x_1465_, 0);
lean_dec(v_unused_1473_);
v___x_1467_ = v___x_1465_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_dec(v___x_1465_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v_a_1464_);
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1464_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
else
{
lean_object* v_a_1474_; 
v_a_1474_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1474_);
lean_dec_ref_known(v___x_1463_, 1);
v_a_1452_ = v_a_1474_;
goto v___jp_1451_;
}
v___jp_1451_:
{
lean_object* v___x_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1460_; 
v___x_1453_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(v_env_1450_, v___y_1445_, v___y_1447_);
v_isSharedCheck_1460_ = !lean_is_exclusive(v___x_1453_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v___x_1453_, 0);
lean_dec(v_unused_1461_);
v___x_1455_ = v___x_1453_;
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
else
{
lean_dec(v___x_1453_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1460_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set_tag(v___x_1455_, 1);
lean_ctor_set(v___x_1455_, 0, v_a_1452_);
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_a_1452_);
v___x_1458_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
return v___x_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg___boxed(lean_object* v_env_1475_, lean_object* v_x_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_1475_, v_x_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(lean_object* v___y_1485_, uint8_t v_isExporting_1486_, lean_object* v___x_1487_, lean_object* v___y_1488_, lean_object* v___x_1489_, lean_object* v_a_x3f_1490_){
_start:
{
lean_object* v___x_1492_; lean_object* v_env_1493_; lean_object* v_nextMacroScope_1494_; lean_object* v_ngen_1495_; lean_object* v_auxDeclNGen_1496_; lean_object* v_traceState_1497_; lean_object* v_messages_1498_; lean_object* v_infoState_1499_; lean_object* v_snapshotTasks_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1525_; 
v___x_1492_ = lean_st_ref_take(v___y_1485_);
v_env_1493_ = lean_ctor_get(v___x_1492_, 0);
v_nextMacroScope_1494_ = lean_ctor_get(v___x_1492_, 1);
v_ngen_1495_ = lean_ctor_get(v___x_1492_, 2);
v_auxDeclNGen_1496_ = lean_ctor_get(v___x_1492_, 3);
v_traceState_1497_ = lean_ctor_get(v___x_1492_, 4);
v_messages_1498_ = lean_ctor_get(v___x_1492_, 6);
v_infoState_1499_ = lean_ctor_get(v___x_1492_, 7);
v_snapshotTasks_1500_ = lean_ctor_get(v___x_1492_, 8);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1492_);
if (v_isSharedCheck_1525_ == 0)
{
lean_object* v_unused_1526_; 
v_unused_1526_ = lean_ctor_get(v___x_1492_, 5);
lean_dec(v_unused_1526_);
v___x_1502_ = v___x_1492_;
v_isShared_1503_ = v_isSharedCheck_1525_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_snapshotTasks_1500_);
lean_inc(v_infoState_1499_);
lean_inc(v_messages_1498_);
lean_inc(v_traceState_1497_);
lean_inc(v_auxDeclNGen_1496_);
lean_inc(v_ngen_1495_);
lean_inc(v_nextMacroScope_1494_);
lean_inc(v_env_1493_);
lean_dec(v___x_1492_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1525_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = l_Lean_Environment_setExporting(v_env_1493_, v_isExporting_1486_);
if (v_isShared_1503_ == 0)
{
lean_ctor_set(v___x_1502_, 5, v___x_1487_);
lean_ctor_set(v___x_1502_, 0, v___x_1504_);
v___x_1506_ = v___x_1502_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_nextMacroScope_1494_);
lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_ngen_1495_);
lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_auxDeclNGen_1496_);
lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_traceState_1497_);
lean_ctor_set(v_reuseFailAlloc_1524_, 5, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1524_, 6, v_messages_1498_);
lean_ctor_set(v_reuseFailAlloc_1524_, 7, v_infoState_1499_);
lean_ctor_set(v_reuseFailAlloc_1524_, 8, v_snapshotTasks_1500_);
v___x_1506_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v_mctx_1509_; lean_object* v_zetaDeltaFVarIds_1510_; lean_object* v_postponed_1511_; lean_object* v_diag_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1522_; 
v___x_1507_ = lean_st_ref_put(v___y_1485_, v___x_1506_);
v___x_1508_ = lean_st_ref_take(v___y_1488_);
v_mctx_1509_ = lean_ctor_get(v___x_1508_, 0);
v_zetaDeltaFVarIds_1510_ = lean_ctor_get(v___x_1508_, 2);
v_postponed_1511_ = lean_ctor_get(v___x_1508_, 3);
v_diag_1512_ = lean_ctor_get(v___x_1508_, 4);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1522_ == 0)
{
lean_object* v_unused_1523_; 
v_unused_1523_ = lean_ctor_get(v___x_1508_, 1);
lean_dec(v_unused_1523_);
v___x_1514_ = v___x_1508_;
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_diag_1512_);
lean_inc(v_postponed_1511_);
lean_inc(v_zetaDeltaFVarIds_1510_);
lean_inc(v_mctx_1509_);
lean_dec(v___x_1508_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1522_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1516_; lean_object* v___x_1518_; 
v___x_1516_ = lean_box(0);
if (v_isShared_1515_ == 0)
{
lean_ctor_set(v___x_1514_, 1, v___x_1489_);
v___x_1518_ = v___x_1514_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_mctx_1509_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1521_, 2, v_zetaDeltaFVarIds_1510_);
lean_ctor_set(v_reuseFailAlloc_1521_, 3, v_postponed_1511_);
lean_ctor_set(v_reuseFailAlloc_1521_, 4, v_diag_1512_);
v___x_1518_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = lean_st_ref_put(v___y_1488_, v___x_1518_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1516_);
return v___x_1520_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(lean_object* v___y_1527_, lean_object* v_isExporting_1528_, lean_object* v___x_1529_, lean_object* v___y_1530_, lean_object* v___x_1531_, lean_object* v_a_x3f_1532_, lean_object* v___y_1533_){
_start:
{
uint8_t v_isExporting_boxed_1534_; lean_object* v_res_1535_; 
v_isExporting_boxed_1534_ = lean_unbox(v_isExporting_1528_);
v_res_1535_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1527_, v_isExporting_boxed_1534_, v___x_1529_, v___y_1530_, v___x_1531_, v_a_x3f_1532_);
lean_dec(v_a_x3f_1532_);
lean_dec(v___y_1530_);
lean_dec(v___y_1527_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(lean_object* v_x_1536_, uint8_t v_isExporting_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v_env_1546_; lean_object* v___x_1547_; uint8_t v_isModule_1548_; 
v___x_1545_ = lean_st_ref_get(v___y_1543_);
v_env_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc_ref(v_env_1546_);
lean_dec(v___x_1545_);
v___x_1547_ = l_Lean_Environment_header(v_env_1546_);
v_isModule_1548_ = lean_ctor_get_uint8(v___x_1547_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1547_);
if (v_isModule_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_dec_ref(v_env_1546_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
v___x_1549_ = lean_apply_7(v_x_1536_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, lean_box(0));
return v___x_1549_;
}
else
{
uint8_t v_isExporting_1550_; 
v_isExporting_1550_ = lean_ctor_get_uint8(v_env_1546_, sizeof(void*)*8);
lean_dec_ref(v_env_1546_);
if (v_isExporting_1537_ == 0)
{
if (v_isExporting_1550_ == 0)
{
lean_object* v___x_1616_; 
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
v___x_1616_ = lean_apply_7(v_x_1536_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, lean_box(0));
return v___x_1616_;
}
else
{
goto v___jp_1551_;
}
}
else
{
if (v_isExporting_1550_ == 0)
{
goto v___jp_1551_;
}
else
{
lean_object* v___x_1617_; 
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
v___x_1617_ = lean_apply_7(v_x_1536_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, lean_box(0));
return v___x_1617_;
}
}
v___jp_1551_:
{
lean_object* v___x_1552_; lean_object* v_env_1553_; lean_object* v_nextMacroScope_1554_; lean_object* v_ngen_1555_; lean_object* v_auxDeclNGen_1556_; lean_object* v_traceState_1557_; lean_object* v_messages_1558_; lean_object* v_infoState_1559_; lean_object* v_snapshotTasks_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1614_; 
v___x_1552_ = lean_st_ref_take(v___y_1543_);
v_env_1553_ = lean_ctor_get(v___x_1552_, 0);
v_nextMacroScope_1554_ = lean_ctor_get(v___x_1552_, 1);
v_ngen_1555_ = lean_ctor_get(v___x_1552_, 2);
v_auxDeclNGen_1556_ = lean_ctor_get(v___x_1552_, 3);
v_traceState_1557_ = lean_ctor_get(v___x_1552_, 4);
v_messages_1558_ = lean_ctor_get(v___x_1552_, 6);
v_infoState_1559_ = lean_ctor_get(v___x_1552_, 7);
v_snapshotTasks_1560_ = lean_ctor_get(v___x_1552_, 8);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; 
v_unused_1615_ = lean_ctor_get(v___x_1552_, 5);
lean_dec(v_unused_1615_);
v___x_1562_ = v___x_1552_;
v_isShared_1563_ = v_isSharedCheck_1614_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_snapshotTasks_1560_);
lean_inc(v_infoState_1559_);
lean_inc(v_messages_1558_);
lean_inc(v_traceState_1557_);
lean_inc(v_auxDeclNGen_1556_);
lean_inc(v_ngen_1555_);
lean_inc(v_nextMacroScope_1554_);
lean_inc(v_env_1553_);
lean_dec(v___x_1552_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1614_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1567_; 
v___x_1564_ = l_Lean_Environment_setExporting(v_env_1553_, v_isExporting_1537_);
v___x_1565_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 5, v___x_1565_);
lean_ctor_set(v___x_1562_, 0, v___x_1564_);
v___x_1567_ = v___x_1562_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_nextMacroScope_1554_);
lean_ctor_set(v_reuseFailAlloc_1613_, 2, v_ngen_1555_);
lean_ctor_set(v_reuseFailAlloc_1613_, 3, v_auxDeclNGen_1556_);
lean_ctor_set(v_reuseFailAlloc_1613_, 4, v_traceState_1557_);
lean_ctor_set(v_reuseFailAlloc_1613_, 5, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1613_, 6, v_messages_1558_);
lean_ctor_set(v_reuseFailAlloc_1613_, 7, v_infoState_1559_);
lean_ctor_set(v_reuseFailAlloc_1613_, 8, v_snapshotTasks_1560_);
v___x_1567_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v_mctx_1570_; lean_object* v_zetaDeltaFVarIds_1571_; lean_object* v_postponed_1572_; lean_object* v_diag_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1611_; 
v___x_1568_ = lean_st_ref_put(v___y_1543_, v___x_1567_);
v___x_1569_ = lean_st_ref_take(v___y_1541_);
v_mctx_1570_ = lean_ctor_get(v___x_1569_, 0);
v_zetaDeltaFVarIds_1571_ = lean_ctor_get(v___x_1569_, 2);
v_postponed_1572_ = lean_ctor_get(v___x_1569_, 3);
v_diag_1573_ = lean_ctor_get(v___x_1569_, 4);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1611_ == 0)
{
lean_object* v_unused_1612_; 
v_unused_1612_ = lean_ctor_get(v___x_1569_, 1);
lean_dec(v_unused_1612_);
v___x_1575_ = v___x_1569_;
v_isShared_1576_ = v_isSharedCheck_1611_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_diag_1573_);
lean_inc(v_postponed_1572_);
lean_inc(v_zetaDeltaFVarIds_1571_);
lean_inc(v_mctx_1570_);
lean_dec(v___x_1569_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1611_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3, &l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v___x_1577_);
v___x_1579_ = v___x_1575_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_mctx_1570_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1610_, 2, v_zetaDeltaFVarIds_1571_);
lean_ctor_set(v_reuseFailAlloc_1610_, 3, v_postponed_1572_);
lean_ctor_set(v_reuseFailAlloc_1610_, 4, v_diag_1573_);
v___x_1579_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
lean_object* v___x_1580_; lean_object* v_r_1581_; 
v___x_1580_ = lean_st_ref_put(v___y_1541_, v___x_1579_);
lean_inc(v___y_1543_);
lean_inc_ref(v___y_1542_);
lean_inc(v___y_1541_);
lean_inc_ref(v___y_1540_);
lean_inc(v___y_1539_);
lean_inc_ref(v___y_1538_);
v_r_1581_ = lean_apply_7(v_x_1536_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, lean_box(0));
if (lean_obj_tag(v_r_1581_) == 0)
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1598_; 
v_a_1582_ = lean_ctor_get(v_r_1581_, 0);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_r_1581_);
if (v_isSharedCheck_1598_ == 0)
{
v___x_1584_ = v_r_1581_;
v_isShared_1585_ = v_isSharedCheck_1598_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v_r_1581_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1598_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
lean_inc(v_a_1582_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set_tag(v___x_1584_, 1);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v___x_1588_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1543_, v_isExporting_1550_, v___x_1565_, v___y_1541_, v___x_1577_, v___x_1587_);
lean_dec_ref(v___x_1587_);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; 
v_unused_1596_ = lean_ctor_get(v___x_1588_, 0);
lean_dec(v_unused_1596_);
v___x_1590_ = v___x_1588_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_dec(v___x_1588_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 0, v_a_1582_);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1582_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
else
{
lean_object* v_a_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1599_ = lean_ctor_get(v_r_1581_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v_r_1581_, 1);
v___x_1600_ = lean_box(0);
v___x_1601_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_1543_, v_isExporting_1550_, v___x_1565_, v___y_1541_, v___x_1577_, v___x_1600_);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v___x_1601_, 0);
lean_dec(v_unused_1609_);
v___x_1603_ = v___x_1601_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v___x_1601_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 1);
lean_ctor_set(v___x_1603_, 0, v_a_1599_);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1599_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(lean_object* v_x_1618_, lean_object* v_isExporting_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
uint8_t v_isExporting_boxed_1627_; lean_object* v_res_1628_; 
v_isExporting_boxed_1627_ = lean_unbox(v_isExporting_1619_);
v_res_1628_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1618_, v_isExporting_boxed_1627_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
return v_res_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(lean_object* v_x_1629_, uint8_t v_when_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_){
_start:
{
if (v_when_1630_ == 0)
{
lean_object* v___x_1638_; 
lean_inc(v___y_1636_);
lean_inc_ref(v___y_1635_);
lean_inc(v___y_1634_);
lean_inc_ref(v___y_1633_);
lean_inc(v___y_1632_);
lean_inc_ref(v___y_1631_);
v___x_1638_ = lean_apply_7(v_x_1629_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, lean_box(0));
return v___x_1638_;
}
else
{
uint8_t v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = 0;
v___x_1640_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_1629_, v___x_1639_, v___y_1631_, v___y_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(lean_object* v_x_1641_, lean_object* v_when_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
uint8_t v_when_boxed_1650_; lean_object* v_res_1651_; 
v_when_boxed_1650_ = lean_unbox(v_when_1642_);
v_res_1651_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_1641_, v_when_boxed_1650_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
lean_dec(v___y_1646_);
lean_dec_ref(v___y_1645_);
lean_dec(v___y_1644_);
lean_dec_ref(v___y_1643_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(size_t v_sz_1652_, size_t v_i_1653_, lean_object* v_bs_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
uint8_t v___x_1658_; 
v___x_1658_ = lean_usize_dec_lt(v_i_1653_, v_sz_1652_);
if (v___x_1658_ == 0)
{
lean_object* v___x_1659_; 
v___x_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1659_, 0, v_bs_1654_);
return v___x_1659_;
}
else
{
lean_object* v_v_1660_; lean_object* v_ref_1661_; uint8_t v_kind_1662_; lean_object* v_levelParams_1663_; lean_object* v_modifiers_1664_; lean_object* v_declName_1665_; lean_object* v_binders_1666_; lean_object* v_numSectionVars_1667_; lean_object* v_type_1668_; lean_object* v_value_1669_; lean_object* v_termination_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1693_; 
v_v_1660_ = lean_array_uget(v_bs_1654_, v_i_1653_);
v_ref_1661_ = lean_ctor_get(v_v_1660_, 0);
v_kind_1662_ = lean_ctor_get_uint8(v_v_1660_, sizeof(void*)*9);
v_levelParams_1663_ = lean_ctor_get(v_v_1660_, 1);
v_modifiers_1664_ = lean_ctor_get(v_v_1660_, 2);
v_declName_1665_ = lean_ctor_get(v_v_1660_, 3);
v_binders_1666_ = lean_ctor_get(v_v_1660_, 4);
v_numSectionVars_1667_ = lean_ctor_get(v_v_1660_, 5);
v_type_1668_ = lean_ctor_get(v_v_1660_, 6);
v_value_1669_ = lean_ctor_get(v_v_1660_, 7);
v_termination_1670_ = lean_ctor_get(v_v_1660_, 8);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_v_1660_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1672_ = v_v_1660_;
v_isShared_1673_ = v_isSharedCheck_1693_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_termination_1670_);
lean_inc(v_value_1669_);
lean_inc(v_type_1668_);
lean_inc(v_numSectionVars_1667_);
lean_inc(v_binders_1666_);
lean_inc(v_declName_1665_);
lean_inc(v_modifiers_1664_);
lean_inc(v_levelParams_1663_);
lean_inc(v_ref_1661_);
lean_dec(v_v_1660_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1693_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v_bs_x27_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_unsigned_to_nat(0u);
v_bs_x27_1675_ = lean_array_uset(v_bs_1654_, v_i_1653_, v___x_1674_);
v___x_1676_ = l_Lean_Elab_WF_floatRecApp(v_value_1669_, v___y_1655_, v___y_1656_);
if (lean_obj_tag(v___x_1676_) == 0)
{
lean_object* v_a_1677_; lean_object* v___x_1679_; 
v_a_1677_ = lean_ctor_get(v___x_1676_, 0);
lean_inc(v_a_1677_);
lean_dec_ref_known(v___x_1676_, 1);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 7, v_a_1677_);
v___x_1679_ = v___x_1672_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_ref_1661_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_levelParams_1663_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_modifiers_1664_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_declName_1665_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_binders_1666_);
lean_ctor_set(v_reuseFailAlloc_1684_, 5, v_numSectionVars_1667_);
lean_ctor_set(v_reuseFailAlloc_1684_, 6, v_type_1668_);
lean_ctor_set(v_reuseFailAlloc_1684_, 7, v_a_1677_);
lean_ctor_set(v_reuseFailAlloc_1684_, 8, v_termination_1670_);
lean_ctor_set_uint8(v_reuseFailAlloc_1684_, sizeof(void*)*9, v_kind_1662_);
v___x_1679_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
size_t v___x_1680_; size_t v___x_1681_; lean_object* v___x_1682_; 
v___x_1680_ = ((size_t)1ULL);
v___x_1681_ = lean_usize_add(v_i_1653_, v___x_1680_);
v___x_1682_ = lean_array_uset(v_bs_x27_1675_, v_i_1653_, v___x_1679_);
v_i_1653_ = v___x_1681_;
v_bs_1654_ = v___x_1682_;
goto _start;
}
}
else
{
lean_object* v_a_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1692_; 
lean_dec_ref(v_bs_x27_1675_);
lean_del_object(v___x_1672_);
lean_dec_ref(v_termination_1670_);
lean_dec_ref(v_type_1668_);
lean_dec(v_numSectionVars_1667_);
lean_dec(v_binders_1666_);
lean_dec(v_declName_1665_);
lean_dec_ref(v_modifiers_1664_);
lean_dec(v_levelParams_1663_);
lean_dec(v_ref_1661_);
v_a_1685_ = lean_ctor_get(v___x_1676_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1676_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1687_ = v___x_1676_;
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_a_1685_);
lean_dec(v___x_1676_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1692_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1690_; 
if (v_isShared_1688_ == 0)
{
v___x_1690_ = v___x_1687_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_a_1685_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* v_sz_1694_, lean_object* v_i_1695_, lean_object* v_bs_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
size_t v_sz_boxed_1700_; size_t v_i_boxed_1701_; lean_object* v_res_1702_; 
v_sz_boxed_1700_ = lean_unbox_usize(v_sz_1694_);
lean_dec(v_sz_1694_);
v_i_boxed_1701_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_boxed_1700_, v_i_boxed_1701_, v_bs_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(size_t v_sz_1703_, size_t v_i_1704_, lean_object* v_bs_1705_){
_start:
{
uint8_t v___x_1706_; 
v___x_1706_ = lean_usize_dec_lt(v_i_1704_, v_sz_1703_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v_bs_1705_);
return v___x_1707_;
}
else
{
lean_object* v_v_1708_; 
v_v_1708_ = lean_array_uget_borrowed(v_bs_1705_, v_i_1704_);
if (lean_obj_tag(v_v_1708_) == 0)
{
lean_object* v___x_1709_; 
lean_dec_ref(v_bs_1705_);
v___x_1709_ = lean_box(0);
return v___x_1709_;
}
else
{
lean_object* v_val_1710_; lean_object* v___x_1711_; lean_object* v_bs_x27_1712_; size_t v___x_1713_; size_t v___x_1714_; lean_object* v___x_1715_; 
v_val_1710_ = lean_ctor_get(v_v_1708_, 0);
lean_inc(v_val_1710_);
v___x_1711_ = lean_unsigned_to_nat(0u);
v_bs_x27_1712_ = lean_array_uset(v_bs_1705_, v_i_1704_, v___x_1711_);
v___x_1713_ = ((size_t)1ULL);
v___x_1714_ = lean_usize_add(v_i_1704_, v___x_1713_);
v___x_1715_ = lean_array_uset(v_bs_x27_1712_, v_i_1704_, v_val_1710_);
v_i_1704_ = v___x_1714_;
v_bs_1705_ = v___x_1715_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(lean_object* v_sz_1717_, lean_object* v_i_1718_, lean_object* v_bs_1719_){
_start:
{
size_t v_sz_boxed_1720_; size_t v_i_boxed_1721_; lean_object* v_res_1722_; 
v_sz_boxed_1720_ = lean_unbox_usize(v_sz_1717_);
lean_dec(v_sz_1717_);
v_i_boxed_1721_ = lean_unbox_usize(v_i_1718_);
lean_dec(v_i_1718_);
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_1720_, v_i_boxed_1721_, v_bs_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(size_t v_sz_1723_, size_t v_i_1724_, lean_object* v_bs_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_usize_dec_lt(v_i_1724_, v_sz_1723_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; 
v___x_1732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1732_, 0, v_bs_1725_);
return v___x_1732_;
}
else
{
uint8_t v___x_1733_; lean_object* v_v_1734_; lean_object* v___x_1735_; lean_object* v_bs_x27_1736_; lean_object* v___x_1737_; 
v___x_1733_ = 0;
v_v_1734_ = lean_array_uget(v_bs_1725_, v_i_1724_);
v___x_1735_ = lean_unsigned_to_nat(0u);
v_bs_x27_1736_ = lean_array_uset(v_bs_1725_, v_i_1724_, v___x_1735_);
v___x_1737_ = l_Lean_Elab_Mutual_cleanPreDef(v_v_1734_, v___x_1733_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; size_t v___x_1739_; size_t v___x_1740_; lean_object* v___x_1741_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref_known(v___x_1737_, 1);
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_add(v_i_1724_, v___x_1739_);
v___x_1741_ = lean_array_uset(v_bs_x27_1736_, v_i_1724_, v_a_1738_);
v_i_1724_ = v___x_1740_;
v_bs_1725_ = v___x_1741_;
goto _start;
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec_ref(v_bs_x27_1736_);
v_a_1743_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1737_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1737_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(lean_object* v_sz_1751_, lean_object* v_i_1752_, lean_object* v_bs_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
size_t v_sz_boxed_1759_; size_t v_i_boxed_1760_; lean_object* v_res_1761_; 
v_sz_boxed_1759_ = lean_unbox_usize(v_sz_1751_);
lean_dec(v_sz_1751_);
v_i_boxed_1760_ = lean_unbox_usize(v_i_1752_);
lean_dec(v_i_1752_);
v_res_1761_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_boxed_1759_, v_i_boxed_1760_, v_bs_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_);
lean_dec(v___y_1757_);
lean_dec_ref(v___y_1756_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(lean_object* v___x_1762_, lean_object* v_as_1763_, size_t v_sz_1764_, size_t v_i_1765_, lean_object* v_b_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_){
_start:
{
lean_object* v_a_1773_; uint8_t v___x_1777_; 
v___x_1777_ = lean_usize_dec_lt(v_i_1765_, v_sz_1764_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_dec(v___x_1762_);
v___x_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1778_, 0, v_b_1766_);
return v___x_1778_;
}
else
{
lean_object* v_a_1779_; uint8_t v_kind_1780_; lean_object* v_declName_1781_; lean_object* v_type_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v_a_1779_ = lean_array_uget_borrowed(v_as_1763_, v_i_1765_);
v_kind_1780_ = lean_ctor_get_uint8(v_a_1779_, sizeof(void*)*9);
v_declName_1781_ = lean_ctor_get(v_a_1779_, 3);
v_type_1782_ = lean_ctor_get(v_a_1779_, 6);
v___x_1783_ = lean_box(0);
v___x_1784_ = lean_name_eq(v_declName_1781_, v___x_1762_);
if (v___x_1784_ == 0)
{
uint8_t v___x_1785_; 
v___x_1785_ = l_Lean_Elab_DefKind_isTheorem(v_kind_1780_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; 
lean_inc_ref(v_type_1782_);
v___x_1786_ = l_Lean_Meta_isProp(v_type_1782_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_object* v_a_1787_; uint8_t v___x_1788_; 
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref_known(v___x_1786_, 1);
v___x_1788_ = lean_unbox(v_a_1787_);
lean_dec(v_a_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; 
lean_inc(v___x_1762_);
lean_inc(v_a_1779_);
v___x_1789_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(v_a_1779_, v___x_1762_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_dec_ref_known(v___x_1789_, 1);
v_a_1773_ = v___x_1783_;
goto v___jp_1772_;
}
else
{
lean_dec(v___x_1762_);
return v___x_1789_;
}
}
else
{
v_a_1773_ = v___x_1783_;
goto v___jp_1772_;
}
}
else
{
lean_object* v_a_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1797_; 
lean_dec(v___x_1762_);
v_a_1790_ = lean_ctor_get(v___x_1786_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1786_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1792_ = v___x_1786_;
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_a_1790_);
lean_dec(v___x_1786_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1797_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v___x_1795_; 
if (v_isShared_1793_ == 0)
{
v___x_1795_ = v___x_1792_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v_a_1790_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
else
{
v_a_1773_ = v___x_1783_;
goto v___jp_1772_;
}
}
else
{
v_a_1773_ = v___x_1783_;
goto v___jp_1772_;
}
}
v___jp_1772_:
{
size_t v___x_1774_; size_t v___x_1775_; 
v___x_1774_ = ((size_t)1ULL);
v___x_1775_ = lean_usize_add(v_i_1765_, v___x_1774_);
v_i_1765_ = v___x_1775_;
v_b_1766_ = v_a_1773_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(lean_object* v___x_1798_, lean_object* v_as_1799_, lean_object* v_sz_1800_, lean_object* v_i_1801_, lean_object* v_b_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
size_t v_sz_boxed_1808_; size_t v_i_boxed_1809_; lean_object* v_res_1810_; 
v_sz_boxed_1808_ = lean_unbox_usize(v_sz_1800_);
lean_dec(v_sz_1800_);
v_i_boxed_1809_ = lean_unbox_usize(v_i_1801_);
lean_dec(v_i_1801_);
v_res_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_1798_, v_as_1799_, v_sz_boxed_1808_, v_i_boxed_1809_, v_b_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
lean_dec(v___y_1804_);
lean_dec_ref(v___y_1803_);
lean_dec_ref(v_as_1799_);
return v_res_1810_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__4(void){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__3));
v___x_1819_ = l_Lean_stringToMessageData(v___x_1818_);
return v___x_1819_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__6(void){
_start:
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__5));
v___x_1822_ = l_Lean_stringToMessageData(v___x_1821_);
return v___x_1822_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__8(void){
_start:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__7));
v___x_1825_ = l_Lean_stringToMessageData(v___x_1824_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lean_Elab_wfRecursion___closed__10(void){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1827_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__9));
v___x_1828_ = l_Lean_stringToMessageData(v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* v_docCtx_1831_, lean_object* v_preDefs_1832_, lean_object* v_termMeasure_x3fs_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v___x_1841_; size_t v_sz_1842_; size_t v___x_1843_; lean_object* v_termMeasures_x3f_1844_; size_t v_sz_1845_; lean_object* v___x_1846_; 
v___x_1841_ = l_Lean_Elab_instInhabitedPreDefinition_default;
v_sz_1842_ = lean_array_size(v_termMeasure_x3fs_1833_);
v___x_1843_ = ((size_t)0ULL);
v_termMeasures_x3f_1844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_1842_, v___x_1843_, v_termMeasure_x3fs_1833_);
v_sz_1845_ = lean_array_size(v_preDefs_1832_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_1845_, v___x_1843_, v_preDefs_1832_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; size_t v_sz_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___f_1865_; lean_object* v___x_1866_; lean_object* v_env_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc_n(v_a_1847_, 2);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1848_ = lean_box(0);
v_sz_1862_ = lean_array_size(v_a_1847_);
v___x_1863_ = lean_box_usize(v_sz_1862_);
v___x_1864_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
v___f_1865_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(v___f_1865_, 0, v_a_1847_);
lean_closure_set(v___f_1865_, 1, v___x_1863_);
lean_closure_set(v___f_1865_, 2, v___x_1864_);
lean_closure_set(v___f_1865_, 3, v___x_1848_);
lean_closure_set(v___f_1865_, 4, v___x_1841_);
v___x_1866_ = lean_st_ref_get(v_a_1839_);
v_env_1867_ = lean_ctor_get(v___x_1866_, 0);
lean_inc_ref(v_env_1867_);
lean_dec(v___x_1866_);
v___x_1868_ = l_Lean_Environment_unlockAsync(v_env_1867_);
v___x_1869_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_1868_, v___f_1865_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v_snd_1871_; lean_object* v_fst_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_2057_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v_snd_1871_ = lean_ctor_get(v_a_1870_, 1);
v_fst_1872_ = lean_ctor_get(v_a_1870_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_a_1870_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_1874_ = v_a_1870_;
v_isShared_1875_ = v_isSharedCheck_2057_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_snd_1871_);
lean_inc(v_fst_1872_);
lean_dec(v_a_1870_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_2057_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_fst_1876_; lean_object* v_snd_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_2056_; 
v_fst_1876_ = lean_ctor_get(v_snd_1871_, 0);
v_snd_1877_ = lean_ctor_get(v_snd_1871_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_snd_1871_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_1879_ = v_snd_1871_;
v_isShared_1880_ = v_isSharedCheck_2056_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_snd_1877_);
lean_inc(v_fst_1876_);
lean_dec(v_snd_1871_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_2056_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___y_1882_; lean_object* v___y_1883_; uint8_t v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v___f_1940_; lean_object* v___x_1941_; lean_object* v___y_1943_; lean_object* v___y_1944_; lean_object* v_wf_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v___y_1949_; lean_object* v___y_1950_; lean_object* v___y_1951_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___x_2047_; lean_object* v_a_2048_; uint8_t v___x_2049_; 
lean_inc(v_snd_1877_);
v___f_1940_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__1___boxed), 8, 1);
lean_closure_set(v___f_1940_, 0, v_snd_1877_);
v___x_1941_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2047_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1941_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
v___x_2049_ = lean_unbox(v_a_2048_);
lean_dec(v_a_2048_);
if (v___x_2049_ == 0)
{
v___y_2010_ = v_a_1834_;
v___y_2011_ = v_a_1835_;
v___y_2012_ = v_a_1836_;
v___y_2013_ = v_a_1837_;
v___y_2014_ = v_a_1838_;
v___y_2015_ = v_a_1839_;
goto v___jp_2009_;
}
else
{
lean_object* v_value_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_value_2050_ = lean_ctor_get(v_snd_1877_, 7);
v___x_2051_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__10, &l_Lean_Elab_wfRecursion___closed__10_once, _init_l_Lean_Elab_wfRecursion___closed__10);
lean_inc_ref(v_value_2050_);
v___x_2052_ = l_Lean_MessageData_ofExpr(v_value_2050_);
v___x_2053_ = l_Lean_indentD(v___x_2052_);
v___x_2054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2051_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1941_, v___x_2054_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_dec_ref_known(v___x_2055_, 1);
v___y_2010_ = v_a_1834_;
v___y_2011_ = v_a_1835_;
v___y_2012_ = v_a_1836_;
v___y_2013_ = v_a_1837_;
v___y_2014_ = v_a_1838_;
v___y_2015_ = v_a_1839_;
goto v___jp_2009_;
}
else
{
lean_dec_ref(v___f_1940_);
lean_del_object(v___x_1879_);
lean_dec(v_snd_1877_);
lean_dec(v_fst_1876_);
lean_del_object(v___x_1874_);
lean_dec(v_fst_1872_);
lean_dec(v_a_1847_);
lean_dec(v_termMeasures_x3f_1844_);
lean_dec_ref(v_docCtx_1831_);
return v___x_2055_;
}
}
v___jp_1881_:
{
lean_object* v___x_1891_; 
lean_inc_ref(v___y_1882_);
lean_inc(v_a_1847_);
lean_inc(v_fst_1876_);
lean_inc(v_fst_1872_);
v___x_1891_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(v_fst_1872_, v_fst_1876_, v_a_1847_, v___y_1882_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1891_, 1);
lean_inc_ref(v___y_1882_);
lean_inc(v_a_1847_);
lean_inc_ref(v_docCtx_1831_);
v___x_1893_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(v_docCtx_1831_, v_a_1847_, v_a_1892_, v___y_1882_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
lean_dec(v_a_1892_);
if (lean_obj_tag(v___x_1893_) == 0)
{
lean_object* v___x_1894_; 
lean_dec_ref_known(v___x_1893_, 1);
lean_inc(v_a_1847_);
v___x_1894_ = l_Lean_Elab_addAndCompilePartialRec(v_docCtx_1831_, v_a_1847_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v___x_1895_; 
lean_dec_ref_known(v___x_1894_, 1);
v___x_1895_ = l_Lean_Elab_Mutual_cleanPreDef(v_snd_1877_, v___y_1884_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; lean_object* v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_1862_, v___x_1843_, v_a_1847_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; lean_object* v_declName_1899_; lean_object* v___x_1900_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc_n(v_a_1898_, 2);
lean_dec_ref_known(v___x_1897_, 1);
v_declName_1899_ = lean_ctor_get(v___y_1882_, 3);
lean_inc_n(v_declName_1899_, 2);
lean_dec_ref(v___y_1882_);
v___x_1900_ = l_Lean_Elab_WF_registerEqnsInfo(v_a_1898_, v_declName_1899_, v_fst_1872_, v_fst_1876_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_declName_1901_; lean_object* v_type_1902_; lean_object* v___x_1903_; 
lean_dec_ref_known(v___x_1900_, 1);
v_declName_1901_ = lean_ctor_get(v_a_1896_, 3);
v_type_1902_ = lean_ctor_get(v_a_1896_, 6);
lean_inc(v_declName_1901_);
v___x_1903_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_1901_, v___y_1890_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v___x_1904_; 
lean_dec_ref_known(v___x_1903_, 1);
lean_inc_ref(v_type_1902_);
v___x_1904_ = l_Lean_Meta_isProp(v_type_1902_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v_a_1905_; uint8_t v___x_1906_; 
v_a_1905_ = lean_ctor_get(v___x_1904_, 0);
lean_inc(v_a_1905_);
lean_dec_ref_known(v___x_1904_, 1);
v___x_1906_ = lean_unbox(v_a_1905_);
lean_dec(v_a_1905_);
if (v___x_1906_ == 0)
{
lean_object* v___x_1907_; 
lean_inc(v_declName_1899_);
v___x_1907_ = l_Lean_Elab_WF_mkUnfoldEq(v_a_1896_, v_declName_1899_, v___y_1883_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_dec_ref_known(v___x_1907_, 1);
v___y_1850_ = v_a_1898_;
v___y_1851_ = v_declName_1899_;
v___y_1852_ = v___y_1885_;
v___y_1853_ = v___y_1886_;
v___y_1854_ = v___y_1887_;
v___y_1855_ = v___y_1888_;
v___y_1856_ = v___y_1889_;
v___y_1857_ = v___y_1890_;
goto v___jp_1849_;
}
else
{
lean_dec(v_declName_1899_);
lean_dec(v_a_1898_);
return v___x_1907_;
}
}
else
{
lean_dec(v_a_1896_);
lean_dec_ref(v___y_1883_);
v___y_1850_ = v_a_1898_;
v___y_1851_ = v_declName_1899_;
v___y_1852_ = v___y_1885_;
v___y_1853_ = v___y_1886_;
v___y_1854_ = v___y_1887_;
v___y_1855_ = v___y_1888_;
v___y_1856_ = v___y_1889_;
v___y_1857_ = v___y_1890_;
goto v___jp_1849_;
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_declName_1899_);
lean_dec(v_a_1898_);
lean_dec(v_a_1896_);
lean_dec_ref(v___y_1883_);
v_a_1908_ = lean_ctor_get(v___x_1904_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1904_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1904_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1904_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
else
{
lean_dec(v_declName_1899_);
lean_dec(v_a_1898_);
lean_dec(v_a_1896_);
lean_dec_ref(v___y_1883_);
return v___x_1903_;
}
}
else
{
lean_dec(v_declName_1899_);
lean_dec(v_a_1898_);
lean_dec(v_a_1896_);
lean_dec_ref(v___y_1883_);
return v___x_1900_;
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1896_);
lean_dec_ref(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v_fst_1876_);
lean_dec(v_fst_1872_);
v_a_1916_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1897_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1897_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
else
{
lean_object* v_a_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1931_; 
lean_dec_ref(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v_fst_1876_);
lean_dec(v_fst_1872_);
lean_dec(v_a_1847_);
v_a_1924_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1931_ == 0)
{
v___x_1926_ = v___x_1895_;
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_a_1924_);
lean_dec(v___x_1895_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1931_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1929_; 
if (v_isShared_1927_ == 0)
{
v___x_1929_ = v___x_1926_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
else
{
lean_dec_ref(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v_snd_1877_);
lean_dec(v_fst_1876_);
lean_dec(v_fst_1872_);
lean_dec(v_a_1847_);
return v___x_1894_;
}
}
else
{
lean_dec_ref(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v_snd_1877_);
lean_dec(v_fst_1876_);
lean_dec(v_fst_1872_);
lean_dec(v_a_1847_);
lean_dec_ref(v_docCtx_1831_);
return v___x_1893_;
}
}
else
{
lean_object* v_a_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1939_; 
lean_dec_ref(v___y_1883_);
lean_dec_ref(v___y_1882_);
lean_dec(v_snd_1877_);
lean_dec(v_fst_1876_);
lean_dec(v_fst_1872_);
lean_dec(v_a_1847_);
lean_dec_ref(v_docCtx_1831_);
v_a_1932_ = lean_ctor_get(v___x_1891_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1891_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1934_ = v___x_1891_;
v_isShared_1935_ = v_isSharedCheck_1939_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_a_1932_);
lean_dec(v___x_1891_);
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
v___jp_1942_:
{
lean_object* v_declName_1952_; lean_object* v_type_1953_; lean_object* v_numFixed_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; 
v_declName_1952_ = lean_ctor_get(v_snd_1877_, 3);
v_type_1953_ = lean_ctor_get(v_snd_1877_, 6);
v_numFixed_1954_ = lean_ctor_get(v_fst_1872_, 0);
v___x_1955_ = lean_box_usize(v_sz_1862_);
v___x_1956_ = ((lean_object*)(l_Lean_Elab_wfRecursion___boxed__const__1));
lean_inc(v_fst_1872_);
lean_inc(v_declName_1952_);
lean_inc(v_fst_1876_);
lean_inc(v_snd_1877_);
lean_inc(v_a_1847_);
v___f_1957_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__4___boxed), 20, 11);
lean_closure_set(v___f_1957_, 0, v___x_1955_);
lean_closure_set(v___f_1957_, 1, v___x_1956_);
lean_closure_set(v___f_1957_, 2, v_a_1847_);
lean_closure_set(v___f_1957_, 3, v___y_1943_);
lean_closure_set(v___f_1957_, 4, v_snd_1877_);
lean_closure_set(v___f_1957_, 5, v_fst_1876_);
lean_closure_set(v___f_1957_, 6, v___x_1848_);
lean_closure_set(v___f_1957_, 7, v___x_1941_);
lean_closure_set(v___f_1957_, 8, v_declName_1952_);
lean_closure_set(v___f_1957_, 9, v_fst_1872_);
lean_closure_set(v___f_1957_, 10, v_wf_1945_);
lean_inc(v_numFixed_1954_);
v___x_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1958_, 0, v_numFixed_1954_);
v___x_1959_ = 0;
lean_inc_ref(v_type_1953_);
v___x_1960_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_1953_, v___x_1958_, v___f_1957_, v___x_1959_, v___x_1959_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v_a_1961_; lean_object* v___x_1962_; lean_object* v_a_1963_; uint8_t v___x_1964_; 
v_a_1961_ = lean_ctor_get(v___x_1960_, 0);
lean_inc(v_a_1961_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1962_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1941_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref(v___x_1962_);
v___x_1964_ = lean_unbox(v_a_1963_);
lean_dec(v_a_1963_);
if (v___x_1964_ == 0)
{
lean_del_object(v___x_1879_);
lean_del_object(v___x_1874_);
v___y_1882_ = v_a_1961_;
v___y_1883_ = v___y_1944_;
v___y_1884_ = v___x_1959_;
v___y_1885_ = v___y_1946_;
v___y_1886_ = v___y_1947_;
v___y_1887_ = v___y_1948_;
v___y_1888_ = v___y_1949_;
v___y_1889_ = v___y_1950_;
v___y_1890_ = v___y_1951_;
goto v___jp_1881_;
}
else
{
lean_object* v_declName_1965_; lean_object* v_value_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v_declName_1965_ = lean_ctor_get(v_a_1961_, 3);
v_value_1966_ = lean_ctor_get(v_a_1961_, 7);
v___x_1967_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__4, &l_Lean_Elab_wfRecursion___closed__4_once, _init_l_Lean_Elab_wfRecursion___closed__4);
lean_inc(v_declName_1965_);
v___x_1968_ = l_Lean_MessageData_ofName(v_declName_1965_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 7);
lean_ctor_set(v___x_1879_, 1, v___x_1968_);
lean_ctor_set(v___x_1879_, 0, v___x_1967_);
v___x_1970_ = v___x_1879_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; lean_object* v___x_1973_; 
v___x_1971_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__6, &l_Lean_Elab_wfRecursion___closed__6_once, _init_l_Lean_Elab_wfRecursion___closed__6);
if (v_isShared_1875_ == 0)
{
lean_ctor_set_tag(v___x_1874_, 7);
lean_ctor_set(v___x_1874_, 1, v___x_1971_);
lean_ctor_set(v___x_1874_, 0, v___x_1970_);
v___x_1973_ = v___x_1874_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v___x_1970_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v___x_1971_);
v___x_1973_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_inc_ref(v_value_1966_);
v___x_1974_ = l_Lean_MessageData_ofExpr(v_value_1966_);
v___x_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1941_, v___x_1975_, v___y_1948_, v___y_1949_, v___y_1950_, v___y_1951_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_dec_ref_known(v___x_1976_, 1);
v___y_1882_ = v_a_1961_;
v___y_1883_ = v___y_1944_;
v___y_1884_ = v___x_1959_;
v___y_1885_ = v___y_1946_;
v___y_1886_ = v___y_1947_;
v___y_1887_ = v___y_1948_;
v___y_1888_ = v___y_1949_;
v___y_1889_ = v___y_1950_;
v___y_1890_ = v___y_1951_;
goto v___jp_1881_;
}
else
{
lean_dec(v_a_1961_);
lean_dec_ref(v___y_1944_);
lean_dec(v_snd_1877_);
lean_dec(v_fst_1876_);
lean_dec(v_fst_1872_);
lean_dec(v_a_1847_);
lean_dec_ref(v_docCtx_1831_);
return v___x_1976_;
}
}
}
}
}
else
{
lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1986_; 
lean_dec_ref(v___y_1944_);
lean_del_object(v___x_1879_);
lean_dec(v_snd_1877_);
lean_dec(v_fst_1876_);
lean_del_object(v___x_1874_);
lean_dec(v_fst_1872_);
lean_dec(v_a_1847_);
lean_dec_ref(v_docCtx_1831_);
v_a_1979_ = lean_ctor_get(v___x_1960_, 0);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1986_ == 0)
{
v___x_1981_ = v___x_1960_;
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_dec(v___x_1960_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1986_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_a_1979_);
v___x_1984_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
return v___x_1984_;
}
}
}
}
v___jp_1987_:
{
if (lean_obj_tag(v_termMeasures_x3f_1844_) == 1)
{
lean_object* v_val_1997_; 
lean_dec_ref(v___y_1990_);
v_val_1997_ = lean_ctor_get(v_termMeasures_x3f_1844_, 0);
lean_inc(v_val_1997_);
lean_dec_ref_known(v_termMeasures_x3f_1844_, 1);
v___y_1943_ = v___y_1989_;
v___y_1944_ = v___y_1988_;
v_wf_1945_ = v_val_1997_;
v___y_1946_ = v___y_1991_;
v___y_1947_ = v___y_1992_;
v___y_1948_ = v___y_1993_;
v___y_1949_ = v___y_1994_;
v___y_1950_ = v___y_1995_;
v___y_1951_ = v___y_1996_;
goto v___jp_1942_;
}
else
{
uint8_t v___x_1998_; lean_object* v___x_1999_; 
lean_dec(v_termMeasures_x3f_1844_);
v___x_1998_ = 1;
v___x_1999_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v___y_1990_, v___x_1998_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_, v___y_1996_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
v___y_1943_ = v___y_1989_;
v___y_1944_ = v___y_1988_;
v_wf_1945_ = v_a_2000_;
v___y_1946_ = v___y_1991_;
v___y_1947_ = v___y_1992_;
v___y_1948_ = v___y_1993_;
v___y_1949_ = v___y_1994_;
v___y_1950_ = v___y_1995_;
v___y_1951_ = v___y_1996_;
goto v___jp_1942_;
}
else
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2008_; 
lean_dec_ref(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_del_object(v___x_1879_);
lean_dec(v_snd_1877_);
lean_dec(v_fst_1876_);
lean_del_object(v___x_1874_);
lean_dec(v_fst_1872_);
lean_dec(v_a_1847_);
lean_dec_ref(v_docCtx_1831_);
v_a_2001_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2003_ = v___x_1999_;
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_1999_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2008_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2001_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
v___jp_2009_:
{
lean_object* v___x_2016_; lean_object* v_env_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2016_ = lean_st_ref_get(v___y_2015_);
v_env_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc_ref(v_env_2017_);
lean_dec(v___x_2016_);
v___x_2018_ = l_Lean_Environment_unlockAsync(v_env_2017_);
v___x_2019_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v___x_2018_, v___f_1940_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; lean_object* v_fst_2021_; lean_object* v_snd_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2038_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v_fst_2021_ = lean_ctor_get(v_a_2020_, 0);
v_snd_2022_ = lean_ctor_get(v_a_2020_, 1);
v_isSharedCheck_2038_ = !lean_is_exclusive(v_a_2020_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2024_ = v_a_2020_;
v_isShared_2025_ = v_isSharedCheck_2038_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_snd_2022_);
lean_inc(v_fst_2021_);
lean_dec(v_a_2020_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2038_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___f_2026_; lean_object* v___x_2027_; lean_object* v_a_2028_; uint8_t v___x_2029_; 
lean_inc(v_fst_1876_);
lean_inc(v_fst_1872_);
lean_inc(v_fst_2021_);
lean_inc(v_a_1847_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__5___boxed), 11, 4);
lean_closure_set(v___f_2026_, 0, v_a_1847_);
lean_closure_set(v___f_2026_, 1, v_fst_2021_);
lean_closure_set(v___f_2026_, 2, v_fst_1872_);
lean_closure_set(v___f_2026_, 3, v_fst_1876_);
v___x_2027_ = l_Lean_Elab_wfRecursion___lam__2(v___x_1941_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v___x_2029_ = lean_unbox(v_a_2028_);
lean_dec(v_a_2028_);
if (v___x_2029_ == 0)
{
lean_del_object(v___x_2024_);
v___y_1988_ = v_snd_2022_;
v___y_1989_ = v_fst_2021_;
v___y_1990_ = v___f_2026_;
v___y_1991_ = v___y_2010_;
v___y_1992_ = v___y_2011_;
v___y_1993_ = v___y_2012_;
v___y_1994_ = v___y_2013_;
v___y_1995_ = v___y_2014_;
v___y_1996_ = v___y_2015_;
goto v___jp_1987_;
}
else
{
lean_object* v_value_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v_value_2030_ = lean_ctor_get(v_snd_1877_, 7);
v___x_2031_ = lean_obj_once(&l_Lean_Elab_wfRecursion___closed__8, &l_Lean_Elab_wfRecursion___closed__8_once, _init_l_Lean_Elab_wfRecursion___closed__8);
lean_inc_ref(v_value_2030_);
v___x_2032_ = l_Lean_MessageData_ofExpr(v_value_2030_);
v___x_2033_ = l_Lean_indentD(v___x_2032_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set_tag(v___x_2024_, 7);
lean_ctor_set(v___x_2024_, 1, v___x_2033_);
lean_ctor_set(v___x_2024_, 0, v___x_2031_);
v___x_2035_ = v___x_2024_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2037_, 1, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v___x_1941_, v___x_2035_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_dec_ref_known(v___x_2036_, 1);
v___y_1988_ = v_snd_2022_;
v___y_1989_ = v_fst_2021_;
v___y_1990_ = v___f_2026_;
v___y_1991_ = v___y_2010_;
v___y_1992_ = v___y_2011_;
v___y_1993_ = v___y_2012_;
v___y_1994_ = v___y_2013_;
v___y_1995_ = v___y_2014_;
v___y_1996_ = v___y_2015_;
goto v___jp_1987_;
}
else
{
lean_dec_ref(v___f_2026_);
lean_dec(v_snd_2022_);
lean_dec(v_fst_2021_);
lean_del_object(v___x_1879_);
lean_dec(v_snd_1877_);
lean_dec(v_fst_1876_);
lean_del_object(v___x_1874_);
lean_dec(v_fst_1872_);
lean_dec(v_a_1847_);
lean_dec(v_termMeasures_x3f_1844_);
lean_dec_ref(v_docCtx_1831_);
return v___x_2036_;
}
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_del_object(v___x_1879_);
lean_dec(v_snd_1877_);
lean_dec(v_fst_1876_);
lean_del_object(v___x_1874_);
lean_dec(v_fst_1872_);
lean_dec(v_a_1847_);
lean_dec(v_termMeasures_x3f_1844_);
lean_dec_ref(v_docCtx_1831_);
v_a_2039_ = lean_ctor_get(v___x_2019_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2019_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2019_);
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
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_1847_);
lean_dec(v_termMeasures_x3f_1844_);
lean_dec_ref(v_docCtx_1831_);
v_a_2058_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_1869_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_1869_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2063_; 
if (v_isShared_2061_ == 0)
{
v___x_2063_ = v___x_2060_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
}
v___jp_1849_:
{
size_t v_sz_1858_; lean_object* v___x_1859_; 
v_sz_1858_ = lean_array_size(v___y_1850_);
lean_inc(v___y_1851_);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___y_1851_, v___y_1850_, v_sz_1858_, v___x_1843_, v___x_1848_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v___x_1860_; 
lean_dec_ref_known(v___x_1859_, 1);
v___x_1860_ = l_Lean_enableRealizationsForConst(v___y_1851_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref_known(v___x_1860_, 1);
v___x_1861_ = l_Lean_Elab_Mutual_addPreDefAttributes(v___y_1850_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
return v___x_1861_;
}
else
{
lean_dec_ref(v___y_1850_);
return v___x_1860_;
}
}
else
{
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v___x_1859_;
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec(v_termMeasures_x3f_1844_);
lean_dec_ref(v_docCtx_1831_);
v_a_2066_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_1846_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_1846_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___boxed(lean_object* v_docCtx_2074_, lean_object* v_preDefs_2075_, lean_object* v_termMeasure_x3fs_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Lean_Elab_wfRecursion(v_docCtx_2074_, v_preDefs_2075_, v_termMeasure_x3fs_2076_, v_a_2077_, v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_);
lean_dec(v_a_2082_);
lean_dec_ref(v_a_2081_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_a_2077_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(lean_object* v_00_u03b1_2085_, lean_object* v_msg_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(v_msg_2086_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_, v___y_2091_, v___y_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(lean_object* v_00_u03b1_2095_, lean_object* v_msg_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(v_00_u03b1_2095_, v_msg_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(size_t v_sz_2105_, size_t v_i_2106_, lean_object* v_bs_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_sz_2105_, v_i_2106_, v_bs_2107_, v___y_2112_, v___y_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2___boxed(lean_object* v_sz_2116_, lean_object* v_i_2117_, lean_object* v_bs_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
size_t v_sz_boxed_2126_; size_t v_i_boxed_2127_; lean_object* v_res_2128_; 
v_sz_boxed_2126_ = lean_unbox_usize(v_sz_2116_);
lean_dec(v_sz_2116_);
v_i_boxed_2127_ = lean_unbox_usize(v_i_2117_);
lean_dec(v_i_2117_);
v_res_2128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__2(v_sz_boxed_2126_, v_i_boxed_2127_, v_bs_2118_, v___y_2119_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
lean_dec(v___y_2120_);
lean_dec_ref(v___y_2119_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(lean_object* v_as_2129_, size_t v_sz_2130_, size_t v_i_2131_, lean_object* v_b_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___redArg(v_as_2129_, v_sz_2130_, v_i_2131_, v_b_2132_, v___y_2137_, v___y_2138_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3___boxed(lean_object* v_as_2141_, lean_object* v_sz_2142_, lean_object* v_i_2143_, lean_object* v_b_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
size_t v_sz_boxed_2152_; size_t v_i_boxed_2153_; lean_object* v_res_2154_; 
v_sz_boxed_2152_ = lean_unbox_usize(v_sz_2142_);
lean_dec(v_sz_2142_);
v_i_boxed_2153_ = lean_unbox_usize(v_i_2143_);
lean_dec(v_i_2143_);
v_res_2154_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__3(v_as_2141_, v_sz_boxed_2152_, v_i_boxed_2153_, v_b_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec_ref(v_as_2141_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(lean_object* v_a_2155_, lean_object* v_as_2156_, size_t v_sz_2157_, size_t v_i_2158_, lean_object* v_bs_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___redArg(v_a_2155_, v_sz_2157_, v_i_2158_, v_bs_2159_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4___boxed(lean_object* v_a_2168_, lean_object* v_as_2169_, lean_object* v_sz_2170_, lean_object* v_i_2171_, lean_object* v_bs_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
size_t v_sz_boxed_2180_; size_t v_i_boxed_2181_; lean_object* v_res_2182_; 
v_sz_boxed_2180_ = lean_unbox_usize(v_sz_2170_);
lean_dec(v_sz_2170_);
v_i_boxed_2181_ = lean_unbox_usize(v_i_2171_);
lean_dec(v_i_2171_);
v_res_2182_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__4(v_a_2168_, v_as_2169_, v_sz_boxed_2180_, v_i_boxed_2181_, v_bs_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
lean_dec(v___y_2174_);
lean_dec_ref(v___y_2173_);
lean_dec_ref(v_as_2169_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(lean_object* v_a_2183_, lean_object* v___x_2184_, size_t v_sz_2185_, size_t v_i_2186_, lean_object* v_bs_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___redArg(v_a_2183_, v___x_2184_, v_sz_2185_, v_i_2186_, v_bs_2187_, v___y_2192_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7___boxed(lean_object* v_a_2196_, lean_object* v___x_2197_, lean_object* v_sz_2198_, lean_object* v_i_2199_, lean_object* v_bs_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
size_t v_sz_boxed_2208_; size_t v_i_boxed_2209_; lean_object* v_res_2210_; 
v_sz_boxed_2208_ = lean_unbox_usize(v_sz_2198_);
lean_dec(v_sz_2198_);
v_i_boxed_2209_ = lean_unbox_usize(v_i_2199_);
lean_dec(v_i_2199_);
v_res_2210_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__7(v_a_2196_, v___x_2197_, v_sz_boxed_2208_, v_i_boxed_2209_, v_bs_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(lean_object* v_00_u03b1_2211_, lean_object* v_env_2212_, lean_object* v_x_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___redArg(v_env_2212_, v_x_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8___boxed(lean_object* v_00_u03b1_2222_, lean_object* v_env_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__8(v_00_u03b1_2222_, v_env_2223_, v_x_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(lean_object* v_cls_2233_, lean_object* v_msg_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(v_cls_2233_, v_msg_2234_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(lean_object* v_cls_2243_, lean_object* v_msg_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(v_cls_2243_, v_msg_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v___y_2245_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(size_t v_sz_2253_, size_t v_i_2254_, lean_object* v_bs_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v___x_2263_; 
v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_2253_, v_i_2254_, v_bs_2255_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(lean_object* v_sz_2264_, lean_object* v_i_2265_, lean_object* v_bs_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
size_t v_sz_boxed_2274_; size_t v_i_boxed_2275_; lean_object* v_res_2276_; 
v_sz_boxed_2274_ = lean_unbox_usize(v_sz_2264_);
lean_dec(v_sz_2264_);
v_i_boxed_2275_ = lean_unbox_usize(v_i_2265_);
lean_dec(v_i_2265_);
v_res_2276_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_boxed_2274_, v_i_boxed_2275_, v_bs_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(lean_object* v___x_2277_, lean_object* v_as_2278_, size_t v_sz_2279_, size_t v_i_2280_, lean_object* v_b_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_2277_, v_as_2278_, v_sz_2279_, v_i_2280_, v_b_2281_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(lean_object* v___x_2290_, lean_object* v_as_2291_, lean_object* v_sz_2292_, lean_object* v_i_2293_, lean_object* v_b_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
size_t v_sz_boxed_2302_; size_t v_i_boxed_2303_; lean_object* v_res_2304_; 
v_sz_boxed_2302_ = lean_unbox_usize(v_sz_2292_);
lean_dec(v_sz_2292_);
v_i_boxed_2303_ = lean_unbox_usize(v_i_2293_);
lean_dec(v_i_2293_);
v_res_2304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_2290_, v_as_2291_, v_sz_boxed_2302_, v_i_boxed_2303_, v_b_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec_ref(v_as_2291_);
return v_res_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(lean_object* v_00_u03b1_2305_, lean_object* v_x_2306_, uint8_t v_isExporting_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_2306_, v_isExporting_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(lean_object* v_00_u03b1_2316_, lean_object* v_x_2317_, lean_object* v_isExporting_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v_isExporting_boxed_2326_; lean_object* v_res_2327_; 
v_isExporting_boxed_2326_ = lean_unbox(v_isExporting_2318_);
v_res_2327_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(v_00_u03b1_2316_, v_x_2317_, v_isExporting_boxed_2326_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(lean_object* v_00_u03b1_2328_, lean_object* v_x_2329_, uint8_t v_when_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(v_x_2329_, v_when_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(lean_object* v_00_u03b1_2339_, lean_object* v_x_2340_, lean_object* v_when_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
uint8_t v_when_boxed_2349_; lean_object* v_res_2350_; 
v_when_boxed_2349_ = lean_unbox(v_when_2341_);
v_res_2350_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(v_00_u03b1_2339_, v_x_2340_, v_when_boxed_2349_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(lean_object* v_msgData_2351_, lean_object* v_macroStack_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2351_, v_macroStack_2352_, v___y_2357_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(lean_object* v_msgData_2361_, lean_object* v_macroStack_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_2361_, v_macroStack_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec_ref(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(lean_object* v_ref_2371_, lean_object* v_msgData_2372_, uint8_t v_severity_2373_, uint8_t v_isSilent_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_2371_, v_msgData_2372_, v_severity_2373_, v_isSilent_2374_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(lean_object* v_ref_2383_, lean_object* v_msgData_2384_, lean_object* v_severity_2385_, lean_object* v_isSilent_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
uint8_t v_severity_boxed_2394_; uint8_t v_isSilent_boxed_2395_; lean_object* v_res_2396_; 
v_severity_boxed_2394_ = lean_unbox(v_severity_2385_);
v_isSilent_boxed_2395_ = lean_unbox(v_isSilent_2386_);
v_res_2396_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(v_ref_2383_, v_msgData_2384_, v_severity_boxed_2394_, v_isSilent_boxed_2395_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v_ref_2383_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2467_ = ((lean_object*)(l_Lean_Elab_wfRecursion___closed__2));
v___x_2468_ = 0;
v___x_2469_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_));
v___x_2470_ = l_Lean_registerTraceClass(v___x_2467_, v___x_2468_, v___x_2469_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(lean_object* v_a_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
return v_res_2472_;
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
