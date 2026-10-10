// Lean compiler output
// Module: Lean.Elab.ConfigEval.Extra
// Imports: public import Lean.Elab.ConfigEval.Instances
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
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instBool;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instBool;
extern lean_object* l_Lean_KVMap_instValueBool;
extern lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instNat;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instNat;
extern lean_object* l_Lean_KVMap_instValueNat;
extern lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instInt;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instInt;
extern lean_object* l_Lean_KVMap_instValueInt;
extern lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instString;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instString;
extern lean_object* l_Lean_KVMap_instValueString;
extern lean_object* l_Lean_Elab_ConfigEval_EvalTerm_instName;
extern lean_object* l_Lean_Elab_ConfigEval_EvalExpr_instName;
extern lean_object* l_Lean_KVMap_instValueName;
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Options_set___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl(lean_object*);
lean_object* l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1_value;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Cannot set `Syntax` option `"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3;
static const lean_string_object l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4 = (const lean_object*)&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4_value;
static lean_once_cell_t l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(lean_object* v_t_1_, lean_object* v___y_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_infoState_5_; uint8_t v_enabled_6_; 
v___x_4_ = lean_st_ref_get(v___y_2_);
v_infoState_5_ = lean_ctor_get(v___x_4_, 8);
lean_inc_ref(v_infoState_5_);
lean_dec(v___x_4_);
v_enabled_6_ = lean_ctor_get_uint8(v_infoState_5_, sizeof(void*)*3);
lean_dec_ref(v_infoState_5_);
if (v_enabled_6_ == 0)
{
lean_object* v___x_7_; lean_object* v___x_8_; 
lean_dec_ref(v_t_1_);
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
return v___x_8_;
}
else
{
lean_object* v___x_9_; lean_object* v_infoState_10_; lean_object* v_env_11_; lean_object* v_nextMacroScope_12_; lean_object* v_ngen_13_; lean_object* v_auxDeclNGen_14_; lean_object* v_traceState_15_; lean_object* v_cache_16_; lean_object* v_recordedDeps_17_; lean_object* v_messages_18_; lean_object* v_snapshotTasks_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_41_; 
v___x_9_ = lean_st_ref_take(v___y_2_);
v_infoState_10_ = lean_ctor_get(v___x_9_, 8);
v_env_11_ = lean_ctor_get(v___x_9_, 0);
v_nextMacroScope_12_ = lean_ctor_get(v___x_9_, 1);
v_ngen_13_ = lean_ctor_get(v___x_9_, 2);
v_auxDeclNGen_14_ = lean_ctor_get(v___x_9_, 3);
v_traceState_15_ = lean_ctor_get(v___x_9_, 4);
v_cache_16_ = lean_ctor_get(v___x_9_, 5);
v_recordedDeps_17_ = lean_ctor_get(v___x_9_, 6);
v_messages_18_ = lean_ctor_get(v___x_9_, 7);
v_snapshotTasks_19_ = lean_ctor_get(v___x_9_, 9);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_41_ == 0)
{
v___x_21_ = v___x_9_;
v_isShared_22_ = v_isSharedCheck_41_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_snapshotTasks_19_);
lean_inc(v_infoState_10_);
lean_inc(v_messages_18_);
lean_inc(v_recordedDeps_17_);
lean_inc(v_cache_16_);
lean_inc(v_traceState_15_);
lean_inc(v_auxDeclNGen_14_);
lean_inc(v_ngen_13_);
lean_inc(v_nextMacroScope_12_);
lean_inc(v_env_11_);
lean_dec(v___x_9_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_41_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
uint8_t v_enabled_23_; lean_object* v_assignment_24_; lean_object* v_lazyAssignment_25_; lean_object* v_trees_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_40_; 
v_enabled_23_ = lean_ctor_get_uint8(v_infoState_10_, sizeof(void*)*3);
v_assignment_24_ = lean_ctor_get(v_infoState_10_, 0);
v_lazyAssignment_25_ = lean_ctor_get(v_infoState_10_, 1);
v_trees_26_ = lean_ctor_get(v_infoState_10_, 2);
v_isSharedCheck_40_ = !lean_is_exclusive(v_infoState_10_);
if (v_isSharedCheck_40_ == 0)
{
v___x_28_ = v_infoState_10_;
v_isShared_29_ = v_isSharedCheck_40_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_trees_26_);
lean_inc(v_lazyAssignment_25_);
lean_inc(v_assignment_24_);
lean_dec(v_infoState_10_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_40_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_30_ = lean_box(0);
v___x_31_ = l_Lean_PersistentArray_push___redArg(v_trees_26_, v_t_1_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 2, v___x_31_);
v___x_33_ = v___x_28_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_assignment_24_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_lazyAssignment_25_);
lean_ctor_set(v_reuseFailAlloc_39_, 2, v___x_31_);
lean_ctor_set_uint8(v_reuseFailAlloc_39_, sizeof(void*)*3, v_enabled_23_);
v___x_33_ = v_reuseFailAlloc_39_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
lean_object* v___x_35_; 
if (v_isShared_22_ == 0)
{
lean_ctor_set(v___x_21_, 8, v___x_33_);
v___x_35_ = v___x_21_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_env_11_);
lean_ctor_set(v_reuseFailAlloc_38_, 1, v_nextMacroScope_12_);
lean_ctor_set(v_reuseFailAlloc_38_, 2, v_ngen_13_);
lean_ctor_set(v_reuseFailAlloc_38_, 3, v_auxDeclNGen_14_);
lean_ctor_set(v_reuseFailAlloc_38_, 4, v_traceState_15_);
lean_ctor_set(v_reuseFailAlloc_38_, 5, v_cache_16_);
lean_ctor_set(v_reuseFailAlloc_38_, 6, v_recordedDeps_17_);
lean_ctor_set(v_reuseFailAlloc_38_, 7, v_messages_18_);
lean_ctor_set(v_reuseFailAlloc_38_, 8, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_38_, 9, v_snapshotTasks_19_);
v___x_35_ = v_reuseFailAlloc_38_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_st_ref_put(v___y_2_, v___x_35_);
v___x_37_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_30_);
return v___x_37_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_42_;
v_res_42_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v_t_1_, v___y_2_);
stack->m_obj
 = v_res_42_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg___boxed(lean_object* v_t_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v_t_43_, v___y_44_);
lean_dec(v___y_44_);
return v_res_46_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = lean_unsigned_to_nat(32u);
v___x_48_ = lean_mk_empty_array_with_capacity(v___x_47_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1(void){
_start:
{
size_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_50_ = ((size_t)5ULL);
v___x_51_ = lean_unsigned_to_nat(0u);
v___x_52_ = lean_unsigned_to_nat(32u);
v___x_53_ = lean_mk_empty_array_with_capacity(v___x_52_);
v___x_54_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0);
v___x_55_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v___x_53_);
lean_ctor_set(v___x_55_, 2, v___x_51_);
lean_ctor_set(v___x_55_, 3, v___x_51_);
lean_ctor_set_usize(v___x_55_, 4, v___x_50_);
return v___x_55_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(lean_object* v_t_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v___x_64_; lean_object* v_infoState_65_; uint8_t v_enabled_66_; 
v___x_64_ = lean_st_ref_get(v___y_62_);
v_infoState_65_ = lean_ctor_get(v___x_64_, 8);
lean_inc_ref(v_infoState_65_);
lean_dec(v___x_64_);
v_enabled_66_ = lean_ctor_get_uint8(v_infoState_65_, sizeof(void*)*3);
lean_dec_ref(v_infoState_65_);
if (v_enabled_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec_ref(v_t_56_);
v___x_67_ = lean_box(0);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1);
v___x_70_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_70_, 0, v_t_56_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v___x_70_, v___y_62_);
return v___x_71_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_56_ = stack[0].m_obj;
lean_object* v___y_57_ = stack[1].m_obj;
lean_object* v___y_58_ = stack[2].m_obj;
lean_object* v___y_59_ = stack[3].m_obj;
lean_object* v___y_60_ = stack[4].m_obj;
lean_object* v___y_61_ = stack[5].m_obj;
lean_object* v___y_62_ = stack[6].m_obj;
lean_object* v_res_72_;
v_res_72_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v_t_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
stack->m_obj
 = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___boxed(lean_object* v_t_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v_t_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
return v_res_81_;
}
}
lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(lean_object* v_info_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_90_, 0, v_info_82_);
v___x_91_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v___x_90_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
return v___x_91_;
}
}
LEAN_EXPORT void l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_82_ = stack[0].m_obj;
lean_object* v___y_83_ = stack[1].m_obj;
lean_object* v___y_84_ = stack[2].m_obj;
lean_object* v___y_85_ = stack[3].m_obj;
lean_object* v___y_86_ = stack[4].m_obj;
lean_object* v___y_87_ = stack[5].m_obj;
lean_object* v___y_88_ = stack[6].m_obj;
lean_object* v_res_92_;
v_res_92_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(v_info_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_, v___y_87_, v___y_88_);
stack->m_obj
 = v_res_92_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0___boxed(lean_object* v_info_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(v_info_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
lean_dec_ref(v___y_94_);
return v_res_101_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v___x_108_; lean_object* v_env_109_; uint8_t v___x_110_; lean_object* v_env_111_; lean_object* v___x_112_; lean_object* v_toCold_113_; lean_object* v_mctx_114_; lean_object* v_lctx_115_; lean_object* v_options_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_108_ = lean_st_ref_get(v___y_106_);
v_env_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc_ref(v_env_109_);
lean_dec(v___x_108_);
v___x_110_ = 0;
v_env_111_ = l_Lean_Environment_setRecordingDeps(v_env_109_, v___x_110_);
v___x_112_ = lean_st_ref_get(v___y_104_);
v_toCold_113_ = lean_ctor_get(v___y_105_, 0);
v_mctx_114_ = lean_ctor_get(v___x_112_, 0);
lean_inc_ref(v_mctx_114_);
lean_dec(v___x_112_);
v_lctx_115_ = lean_ctor_get(v___y_103_, 2);
v_options_116_ = lean_ctor_get(v_toCold_113_, 2);
lean_inc_ref(v_options_116_);
lean_inc_ref(v_lctx_115_);
v___x_117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_117_, 0, v_env_111_);
lean_ctor_set(v___x_117_, 1, v_mctx_114_);
lean_ctor_set(v___x_117_, 2, v_lctx_115_);
lean_ctor_set(v___x_117_, 3, v_options_116_);
v___x_118_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_msgData_102_);
v___x_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
return v___x_119_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_102_ = stack[0].m_obj;
lean_object* v___y_103_ = stack[1].m_obj;
lean_object* v___y_104_ = stack[2].m_obj;
lean_object* v___y_105_ = stack[3].m_obj;
lean_object* v___y_106_ = stack[4].m_obj;
lean_object* v_res_120_;
v_res_120_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(v_msgData_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(v_msgData_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
return v_res_127_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_box(1);
v___x_129_ = l_Lean_MessageData_ofFormat(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_133_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2));
v___x_134_ = l_Lean_MessageData_ofFormat(v___x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7(lean_object* v_x_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
return v_x_135_;
}
else
{
lean_object* v_head_137_; lean_object* v_tail_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_160_; 
v_head_137_ = lean_ctor_get(v_x_136_, 0);
v_tail_138_ = lean_ctor_get(v_x_136_, 1);
v_isSharedCheck_160_ = !lean_is_exclusive(v_x_136_);
if (v_isSharedCheck_160_ == 0)
{
v___x_140_ = v_x_136_;
v_isShared_141_ = v_isSharedCheck_160_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_tail_138_);
lean_inc(v_head_137_);
lean_dec(v_x_136_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_160_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_before_142_; lean_object* v___x_144_; uint8_t v_isShared_145_; uint8_t v_isSharedCheck_158_; 
v_before_142_ = lean_ctor_get(v_head_137_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v_head_137_);
if (v_isSharedCheck_158_ == 0)
{
lean_object* v_unused_159_; 
v_unused_159_ = lean_ctor_get(v_head_137_, 1);
lean_dec(v_unused_159_);
v___x_144_ = v_head_137_;
v_isShared_145_ = v_isSharedCheck_158_;
goto v_resetjp_143_;
}
else
{
lean_inc(v_before_142_);
lean_dec(v_head_137_);
v___x_144_ = lean_box(0);
v_isShared_145_ = v_isSharedCheck_158_;
goto v_resetjp_143_;
}
v_resetjp_143_:
{
lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_146_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0);
if (v_isShared_145_ == 0)
{
lean_ctor_set_tag(v___x_144_, 7);
lean_ctor_set(v___x_144_, 1, v___x_146_);
lean_ctor_set(v___x_144_, 0, v_x_135_);
v___x_148_ = v___x_144_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_x_135_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___x_146_);
v___x_148_ = v_reuseFailAlloc_157_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3);
if (v_isShared_141_ == 0)
{
lean_ctor_set_tag(v___x_140_, 7);
lean_ctor_set(v___x_140_, 1, v___x_149_);
lean_ctor_set(v___x_140_, 0, v___x_148_);
v___x_151_ = v___x_140_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_148_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_149_);
v___x_151_ = v_reuseFailAlloc_156_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = l_Lean_MessageData_ofSyntax(v_before_142_);
v___x_153_ = l_Lean_indentD(v___x_152_);
v___x_154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_151_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v_x_135_ = v___x_154_;
v_x_136_ = v_tail_138_;
goto _start;
}
}
}
}
}
}
}
uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(lean_object* v_opts_161_, lean_object* v_opt_162_){
_start:
{
lean_object* v_name_163_; lean_object* v_defValue_164_; lean_object* v_map_165_; lean_object* v___x_166_; 
v_name_163_ = lean_ctor_get(v_opt_162_, 0);
v_defValue_164_ = lean_ctor_get(v_opt_162_, 1);
v_map_165_ = lean_ctor_get(v_opts_161_, 0);
v___x_166_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_165_, v_name_163_);
if (lean_obj_tag(v___x_166_) == 0)
{
uint8_t v___x_167_; 
v___x_167_ = lean_unbox(v_defValue_164_);
return v___x_167_;
}
else
{
lean_object* v_val_168_; 
v_val_168_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_val_168_);
lean_dec_ref_known(v___x_166_, 1);
if (lean_obj_tag(v_val_168_) == 1)
{
uint8_t v_v_169_; 
v_v_169_ = lean_ctor_get_uint8(v_val_168_, 0);
lean_dec_ref_known(v_val_168_, 0);
return v_v_169_;
}
else
{
uint8_t v___x_170_; 
lean_dec(v_val_168_);
v___x_170_ = lean_unbox(v_defValue_164_);
return v___x_170_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_161_ = stack[0].m_obj;
lean_object* v_opt_162_ = stack[1].m_obj;
uint8_t v_res_171_;
v_res_171_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(v_opts_161_, v_opt_162_);
stack->m_num = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_opts_172_, lean_object* v_opt_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(v_opts_172_, v_opt_173_);
lean_dec_ref(v_opt_173_);
lean_dec_ref(v_opts_172_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1));
v___x_180_ = l_Lean_MessageData_ofFormat(v___x_179_);
return v___x_180_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(lean_object* v_msgData_181_, lean_object* v_macroStack_182_, lean_object* v___y_183_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_183_);
v___x_186_ = l_Lean_Elab_pp_macroStack;
v___x_187_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(v___x_185_, v___x_186_);
lean_dec_ref(v___x_185_);
if (v___x_187_ == 0)
{
lean_object* v___x_188_; 
lean_dec(v_macroStack_182_);
v___x_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_188_, 0, v_msgData_181_);
return v___x_188_;
}
else
{
if (lean_obj_tag(v_macroStack_182_) == 0)
{
lean_object* v___x_189_; 
v___x_189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_189_, 0, v_msgData_181_);
return v___x_189_;
}
else
{
lean_object* v_head_190_; lean_object* v_after_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_206_; 
v_head_190_ = lean_ctor_get(v_macroStack_182_, 0);
lean_inc(v_head_190_);
v_after_191_ = lean_ctor_get(v_head_190_, 1);
v_isSharedCheck_206_ = !lean_is_exclusive(v_head_190_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v_head_190_, 0);
lean_dec(v_unused_207_);
v___x_193_ = v_head_190_;
v_isShared_194_ = v_isSharedCheck_206_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_after_191_);
lean_dec(v_head_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_206_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_195_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0);
if (v_isShared_194_ == 0)
{
lean_ctor_set_tag(v___x_193_, 7);
lean_ctor_set(v___x_193_, 1, v___x_195_);
lean_ctor_set(v___x_193_, 0, v_msgData_181_);
v___x_197_ = v___x_193_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_msgData_181_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_195_);
v___x_197_ = v_reuseFailAlloc_205_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v_msgData_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_198_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2);
v___x_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = l_Lean_MessageData_ofSyntax(v_after_191_);
v___x_201_ = l_Lean_indentD(v___x_200_);
v_msgData_202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_202_, 0, v___x_199_);
lean_ctor_set(v_msgData_202_, 1, v___x_201_);
v___x_203_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7(v_msgData_202_, v_macroStack_182_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_181_ = stack[0].m_obj;
lean_object* v_macroStack_182_ = stack[1].m_obj;
lean_object* v___y_183_ = stack[2].m_obj;
lean_object* v_res_208_;
v_res_208_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_msgData_181_, v_macroStack_182_, v___y_183_);
stack->m_obj
 = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_209_, lean_object* v_macroStack_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_msgData_209_, v_macroStack_210_, v___y_211_);
lean_dec_ref(v___y_211_);
return v_res_213_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(lean_object* v_msg_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v_ref_222_; lean_object* v_macroStack_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v_a_226_; lean_object* v___x_227_; lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_236_; 
v_ref_222_ = lean_ctor_get(v___y_219_, 2);
v_macroStack_223_ = lean_ctor_get(v___y_215_, 1);
v___x_224_ = l_Lean_Elab_getBetterRef(v_ref_222_, v_macroStack_223_);
v___x_225_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(v_msg_214_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref(v___x_225_);
lean_inc(v_macroStack_223_);
v___x_227_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_a_226_, v_macroStack_223_, v___y_219_);
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_236_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_236_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_236_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_224_);
lean_ctor_set(v___x_232_, 1, v_a_228_);
if (v_isShared_231_ == 0)
{
lean_ctor_set_tag(v___x_230_, 1);
lean_ctor_set(v___x_230_, 0, v___x_232_);
v___x_234_ = v___x_230_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_235_; 
v_reuseFailAlloc_235_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_214_ = stack[0].m_obj;
lean_object* v___y_215_ = stack[1].m_obj;
lean_object* v___y_216_ = stack[2].m_obj;
lean_object* v___y_217_ = stack[3].m_obj;
lean_object* v___y_218_ = stack[4].m_obj;
lean_object* v___y_219_ = stack[5].m_obj;
lean_object* v___y_220_ = stack[6].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg___boxed(lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec_ref(v___y_239_);
return v_res_246_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(lean_object* v_ref_247_, lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_toCold_256_; lean_object* v_currRecDepth_257_; lean_object* v_ref_258_; uint16_t v_optionFlags_259_; uint8_t v_suppressElabErrors_260_; uint8_t v_isRecordingDeps_261_; lean_object* v_ref_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_toCold_256_ = lean_ctor_get(v___y_253_, 0);
v_currRecDepth_257_ = lean_ctor_get(v___y_253_, 1);
v_ref_258_ = lean_ctor_get(v___y_253_, 2);
v_optionFlags_259_ = lean_ctor_get_uint16(v___y_253_, sizeof(void*)*3);
v_suppressElabErrors_260_ = lean_ctor_get_uint8(v___y_253_, sizeof(void*)*3 + 2);
v_isRecordingDeps_261_ = lean_ctor_get_uint8(v___y_253_, sizeof(void*)*3 + 3);
v_ref_262_ = l_Lean_replaceRef(v_ref_247_, v_ref_258_);
lean_inc(v_currRecDepth_257_);
lean_inc_ref(v_toCold_256_);
v___x_263_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_263_, 0, v_toCold_256_);
lean_ctor_set(v___x_263_, 1, v_currRecDepth_257_);
lean_ctor_set(v___x_263_, 2, v_ref_262_);
lean_ctor_set_uint16(v___x_263_, sizeof(void*)*3, v_optionFlags_259_);
lean_ctor_set_uint8(v___x_263_, sizeof(void*)*3 + 2, v_suppressElabErrors_260_);
lean_ctor_set_uint8(v___x_263_, sizeof(void*)*3 + 3, v_isRecordingDeps_261_);
v___x_264_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___x_263_, v___y_254_);
lean_dec_ref_known(v___x_263_, 3);
return v___x_264_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_247_ = stack[0].m_obj;
lean_object* v_msg_248_ = stack[1].m_obj;
lean_object* v___y_249_ = stack[2].m_obj;
lean_object* v___y_250_ = stack[3].m_obj;
lean_object* v___y_251_ = stack[4].m_obj;
lean_object* v___y_252_ = stack[5].m_obj;
lean_object* v___y_253_ = stack[6].m_obj;
lean_object* v___y_254_ = stack[7].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_ref_247_, v_msg_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg___boxed(lean_object* v_ref_266_, lean_object* v_msg_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_ref_266_, v_msg_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v_ref_266_);
return v_res_275_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2));
v___x_281_ = l_Lean_stringToMessageData(v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4));
v___x_284_ = l_Lean_stringToMessageData(v___x_283_);
return v___x_284_;
}
}
lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(lean_object* v_optionPrefix_285_, lean_object* v_opts_286_, lean_object* v_item_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_option_310_; lean_object* v_value_311_; lean_object* v_optionComps_312_; lean_object* v___x_313_; lean_object* v_optName_314_; lean_object* v_inst_316_; lean_object* v_inst_317_; lean_object* v_inst_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_321_; lean_object* v___y_322_; lean_object* v___y_323_; lean_object* v___y_324_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_424_; 
v___x_295_ = l_Lean_Elab_ConfigEval_EvalTerm_instBool;
v___x_296_ = l_Lean_Elab_ConfigEval_EvalExpr_instBool;
v___x_297_ = l_Lean_KVMap_instValueBool;
v___x_298_ = l_Lean_Elab_ConfigEval_EvalTerm_instNat;
v___x_299_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
v___x_300_ = l_Lean_KVMap_instValueNat;
v___x_301_ = l_Lean_Elab_ConfigEval_EvalTerm_instInt;
v___x_302_ = l_Lean_Elab_ConfigEval_EvalExpr_instInt;
v___x_303_ = l_Lean_KVMap_instValueInt;
v___x_304_ = l_Lean_Elab_ConfigEval_EvalTerm_instString;
v___x_305_ = l_Lean_Elab_ConfigEval_EvalExpr_instString;
v___x_306_ = l_Lean_KVMap_instValueString;
v___x_307_ = l_Lean_Elab_ConfigEval_EvalTerm_instName;
v___x_308_ = l_Lean_Elab_ConfigEval_EvalExpr_instName;
v___x_309_ = l_Lean_KVMap_instValueName;
v_option_310_ = lean_ctor_get(v_item_287_, 1);
v_value_311_ = lean_ctor_get(v_item_287_, 2);
lean_inc(v_value_311_);
v_optionComps_312_ = lean_ctor_get(v_item_287_, 5);
lean_inc_ref(v_item_287_);
v___x_313_ = l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(v_item_287_);
v_optName_314_ = l_Lean_Name_append(v_optionPrefix_285_, v___x_313_);
v___x_343_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_287_);
lean_inc(v_optionComps_312_);
v___x_344_ = lean_array_mk(v_optionComps_312_);
v___x_345_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1));
v___x_346_ = lean_box(2);
v___x_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
lean_ctor_set(v___x_347_, 2, v___x_344_);
v___x_348_ = lean_unsigned_to_nat(2u);
v___x_349_ = lean_mk_empty_array_with_capacity(v___x_348_);
v___x_350_ = lean_array_push(v___x_349_, v___x_343_);
v___x_351_ = lean_array_push(v___x_350_, v___x_347_);
v___x_352_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_352_, 0, v___x_346_);
lean_ctor_set(v___x_352_, 1, v___x_345_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
v___x_353_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
v___x_354_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(v___x_353_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; 
v_unused_425_ = lean_ctor_get(v___x_354_, 0);
lean_dec(v_unused_425_);
v___x_356_ = v___x_354_;
v_isShared_357_ = v_isSharedCheck_424_;
goto v_resetjp_355_;
}
else
{
lean_dec(v___x_354_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_424_;
goto v_resetjp_355_;
}
v___jp_315_:
{
lean_object* v___x_325_; 
lean_inc_ref(v_inst_317_);
lean_inc_ref(v_inst_316_);
v___x_325_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_316_, v_inst_317_, v_value_311_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_334_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_334_ == 0)
{
v___x_328_ = v___x_325_;
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_325_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_334_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; lean_object* v___x_332_; 
lean_inc_ref(v_inst_318_);
v___x_330_ = l_Lean_Options_set___redArg(v_inst_318_, v_opts_286_, v_optName_314_, v_a_326_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 0, v___x_330_);
v___x_332_ = v___x_328_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_330_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
lean_dec(v_optName_314_);
lean_dec_ref(v_opts_286_);
v_a_335_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_325_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_325_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
v_resetjp_355_:
{
lean_object* v_ref_358_; lean_object* v___x_359_; 
v_ref_358_ = lean_ctor_get(v_a_292_, 2);
lean_inc(v_optName_314_);
v___x_359_ = l_Lean_getOptionDecl(v_optName_314_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v_declName_361_; lean_object* v_defValue_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v___x_359_, 1);
v_declName_361_ = lean_ctor_get(v_a_360_, 1);
lean_inc(v_declName_361_);
v_defValue_362_ = lean_ctor_get(v_a_360_, 2);
lean_inc_ref(v_defValue_362_);
lean_dec(v_a_360_);
lean_inc(v_optName_314_);
lean_inc(v_option_310_);
v___x_363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_363_, 0, v_option_310_);
lean_ctor_set(v___x_363_, 1, v_optName_314_);
lean_ctor_set(v___x_363_, 2, v_declName_361_);
if (v_isShared_357_ == 0)
{
lean_ctor_set_tag(v___x_356_, 5);
lean_ctor_set(v___x_356_, 0, v___x_363_);
v___x_365_ = v___x_356_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_363_);
v___x_365_ = v_reuseFailAlloc_409_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_366_; 
v___x_366_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v___x_365_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec_ref(v___x_366_);
switch(lean_obj_tag(v_defValue_362_))
{
case 0:
{
lean_object* v___x_367_; 
lean_dec_ref_known(v_defValue_362_, 1);
v___x_367_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_dec_ref_known(v___x_367_, 1);
v_inst_316_ = v___x_304_;
v_inst_317_ = v___x_305_;
v_inst_318_ = v___x_306_;
v___y_319_ = v_a_288_;
v___y_320_ = v_a_289_;
v___y_321_ = v_a_290_;
v___y_322_ = v_a_291_;
v___y_323_ = v_a_292_;
v___y_324_ = v_a_293_;
goto v___jp_315_;
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec(v_optName_314_);
lean_dec(v_value_311_);
lean_dec_ref(v_opts_286_);
v_a_368_ = lean_ctor_get(v___x_367_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_367_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_367_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
case 1:
{
lean_dec_ref_known(v_defValue_362_, 0);
lean_dec_ref(v_item_287_);
v_inst_316_ = v___x_295_;
v_inst_317_ = v___x_296_;
v_inst_318_ = v___x_297_;
v___y_319_ = v_a_288_;
v___y_320_ = v_a_289_;
v___y_321_ = v_a_290_;
v___y_322_ = v_a_291_;
v___y_323_ = v_a_292_;
v___y_324_ = v_a_293_;
goto v___jp_315_;
}
case 2:
{
lean_object* v___x_376_; 
lean_dec_ref_known(v_defValue_362_, 1);
v___x_376_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_dec_ref_known(v___x_376_, 1);
v_inst_316_ = v___x_307_;
v_inst_317_ = v___x_308_;
v_inst_318_ = v___x_309_;
v___y_319_ = v_a_288_;
v___y_320_ = v_a_289_;
v___y_321_ = v_a_290_;
v___y_322_ = v_a_291_;
v___y_323_ = v_a_292_;
v___y_324_ = v_a_293_;
goto v___jp_315_;
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec(v_optName_314_);
lean_dec(v_value_311_);
lean_dec_ref(v_opts_286_);
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
case 3:
{
lean_object* v___x_385_; 
lean_dec_ref_known(v_defValue_362_, 1);
v___x_385_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_dec_ref_known(v___x_385_, 1);
v_inst_316_ = v___x_298_;
v_inst_317_ = v___x_299_;
v_inst_318_ = v___x_300_;
v___y_319_ = v_a_288_;
v___y_320_ = v_a_289_;
v___y_321_ = v_a_290_;
v___y_322_ = v_a_291_;
v___y_323_ = v_a_292_;
v___y_324_ = v_a_293_;
goto v___jp_315_;
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
lean_dec(v_optName_314_);
lean_dec(v_value_311_);
lean_dec_ref(v_opts_286_);
v_a_386_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_385_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_385_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
case 4:
{
lean_object* v___x_394_; 
lean_dec_ref_known(v_defValue_362_, 1);
v___x_394_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_dec_ref_known(v___x_394_, 1);
v_inst_316_ = v___x_301_;
v_inst_317_ = v___x_302_;
v_inst_318_ = v___x_303_;
v___y_319_ = v_a_288_;
v___y_320_ = v_a_289_;
v___y_321_ = v_a_290_;
v___y_322_ = v_a_291_;
v___y_323_ = v_a_292_;
v___y_324_ = v_a_293_;
goto v___jp_315_;
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec(v_optName_314_);
lean_dec(v_value_311_);
lean_dec_ref(v_opts_286_);
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
default: 
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
lean_inc(v_option_310_);
lean_dec_ref_known(v_defValue_362_, 1);
lean_dec(v_value_311_);
lean_dec_ref(v_item_287_);
lean_dec_ref(v_opts_286_);
v___x_403_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3, &l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3);
v___x_404_ = l_Lean_MessageData_ofName(v_optName_314_);
v___x_405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_403_);
lean_ctor_set(v___x_405_, 1, v___x_404_);
v___x_406_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5, &l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5);
v___x_407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_405_);
lean_ctor_set(v___x_407_, 1, v___x_406_);
v___x_408_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_option_310_, v___x_407_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
lean_dec(v_option_310_);
return v___x_408_;
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_423_; 
lean_dec(v_optName_314_);
lean_dec(v_value_311_);
lean_dec_ref(v_item_287_);
lean_dec_ref(v_opts_286_);
v_a_410_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_423_ == 0)
{
v___x_412_ = v___x_359_;
v_isShared_413_ = v_isSharedCheck_423_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_359_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_423_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_io_error_to_string(v_a_410_);
if (v_isShared_357_ == 0)
{
lean_ctor_set_tag(v___x_356_, 3);
lean_ctor_set(v___x_356_, 0, v___x_414_);
v___x_416_ = v___x_356_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_422_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_420_; 
v___x_417_ = l_Lean_MessageData_ofFormat(v___x_416_);
lean_inc(v_ref_358_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v_ref_358_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_418_);
v___x_420_ = v___x_412_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_optionPrefix_285_ = stack[0].m_obj;
lean_object* v_opts_286_ = stack[1].m_obj;
lean_object* v_item_287_ = stack[2].m_obj;
lean_object* v_a_288_ = stack[3].m_obj;
lean_object* v_a_289_ = stack[4].m_obj;
lean_object* v_a_290_ = stack[5].m_obj;
lean_object* v_a_291_ = stack[6].m_obj;
lean_object* v_a_292_ = stack[7].m_obj;
lean_object* v_a_293_ = stack[8].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(v_optionPrefix_285_, v_opts_286_, v_item_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___boxed(lean_object* v_optionPrefix_427_, lean_object* v_opts_428_, lean_object* v_item_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(v_optionPrefix_427_, v_opts_428_, v_item_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
return v_res_437_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(lean_object* v_t_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v_t_438_, v___y_444_);
return v___x_446_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_438_ = stack[0].m_obj;
lean_object* v___y_439_ = stack[1].m_obj;
lean_object* v___y_440_ = stack[2].m_obj;
lean_object* v___y_441_ = stack[3].m_obj;
lean_object* v___y_442_ = stack[4].m_obj;
lean_object* v___y_443_ = stack[5].m_obj;
lean_object* v___y_444_ = stack[6].m_obj;
lean_object* v_res_447_;
v_res_447_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(v_t_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___boxed(lean_object* v_t_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(v_t_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
return v_res_456_;
}
}
lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(lean_object* v_00_u03b1_457_, lean_object* v_ref_458_, lean_object* v_msg_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_ref_458_, v_msg_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
return v___x_467_;
}
}
LEAN_EXPORT void l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_458_ = stack[1].m_obj;
lean_object* v_msg_459_ = stack[2].m_obj;
lean_object* v___y_460_ = stack[3].m_obj;
lean_object* v___y_461_ = stack[4].m_obj;
lean_object* v___y_462_ = stack[5].m_obj;
lean_object* v___y_463_ = stack[6].m_obj;
lean_object* v___y_464_ = stack[7].m_obj;
lean_object* v___y_465_ = stack[8].m_obj;
lean_object* v_res_468_;
v_res_468_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(lean_box(0), v_ref_458_, v_msg_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
stack->m_obj
 = v_res_468_;
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___boxed(lean_object* v_00_u03b1_469_, lean_object* v_ref_470_, lean_object* v_msg_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(v_00_u03b1_469_, v_ref_470_, v_msg_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v_ref_470_);
return v_res_479_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(lean_object* v_00_u03b1_480_, lean_object* v_msg_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
return v___x_489_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_481_ = stack[1].m_obj;
lean_object* v___y_482_ = stack[2].m_obj;
lean_object* v___y_483_ = stack[3].m_obj;
lean_object* v___y_484_ = stack[4].m_obj;
lean_object* v___y_485_ = stack[5].m_obj;
lean_object* v___y_486_ = stack[6].m_obj;
lean_object* v___y_487_ = stack[7].m_obj;
lean_object* v_res_490_;
v_res_490_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(lean_box(0), v_msg_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
stack->m_obj
 = v_res_490_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___boxed(lean_object* v_00_u03b1_491_, lean_object* v_msg_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(v_00_u03b1_491_, v_msg_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
return v_res_500_;
}
}
lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(lean_object* v_msgData_501_, lean_object* v_macroStack_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_msgData_501_, v_macroStack_502_, v___y_507_);
return v___x_510_;
}
}
LEAN_EXPORT void l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_501_ = stack[0].m_obj;
lean_object* v_macroStack_502_ = stack[1].m_obj;
lean_object* v___y_503_ = stack[2].m_obj;
lean_object* v___y_504_ = stack[3].m_obj;
lean_object* v___y_505_ = stack[4].m_obj;
lean_object* v___y_506_ = stack[5].m_obj;
lean_object* v___y_507_ = stack[6].m_obj;
lean_object* v___y_508_ = stack[7].m_obj;
lean_object* v_res_511_;
v_res_511_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(v_msgData_501_, v_macroStack_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_512_, lean_object* v_macroStack_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(v_msgData_512_, v_macroStack_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_521_;
}
}
lean_object* runtime_initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_ConfigEval_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_ConfigEval_Extra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_ConfigEval_Instances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_ConfigEval_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_ConfigEval_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_ConfigEval_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_ConfigEval_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_ConfigEval_Extra(builtin);
}
#ifdef __cplusplus
}
#endif
