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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(lean_object* v_t_1_, lean_object* v___y_2_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg___boxed(lean_object* v_t_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v_t_42_, v___y_43_);
lean_dec(v___y_43_);
return v_res_45_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_46_ = lean_unsigned_to_nat(32u);
v___x_47_ = lean_mk_empty_array_with_capacity(v___x_46_);
v___x_48_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1(void){
_start:
{
size_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_49_ = ((size_t)5ULL);
v___x_50_ = lean_unsigned_to_nat(0u);
v___x_51_ = lean_unsigned_to_nat(32u);
v___x_52_ = lean_mk_empty_array_with_capacity(v___x_51_);
v___x_53_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__0);
v___x_54_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_52_);
lean_ctor_set(v___x_54_, 2, v___x_50_);
lean_ctor_set(v___x_54_, 3, v___x_50_);
lean_ctor_set_usize(v___x_54_, 4, v___x_49_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(lean_object* v_t_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v___x_63_; lean_object* v_infoState_64_; uint8_t v_enabled_65_; 
v___x_63_ = lean_st_ref_get(v___y_61_);
v_infoState_64_ = lean_ctor_get(v___x_63_, 8);
lean_inc_ref(v_infoState_64_);
lean_dec(v___x_63_);
v_enabled_65_ = lean_ctor_get_uint8(v_infoState_64_, sizeof(void*)*3);
lean_dec_ref(v_infoState_64_);
if (v_enabled_65_ == 0)
{
lean_object* v___x_66_; lean_object* v___x_67_; 
lean_dec_ref(v_t_55_);
v___x_66_ = lean_box(0);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_68_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___closed__1);
v___x_69_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_69_, 0, v_t_55_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v___x_69_, v___y_61_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1___boxed(lean_object* v_t_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v_t_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(lean_object* v_info_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(v___x_88_, 0, v_info_80_);
v___x_89_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v___x_88_, v___y_81_, v___y_82_, v___y_83_, v___y_84_, v___y_85_, v___y_86_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0___boxed(lean_object* v_info_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(v_info_90_, v___y_91_, v___y_92_, v___y_93_, v___y_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
lean_dec(v___y_94_);
lean_dec_ref(v___y_93_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(lean_object* v_msgData_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; lean_object* v_env_106_; lean_object* v___x_107_; lean_object* v_toCold_108_; lean_object* v_mctx_109_; lean_object* v_lctx_110_; lean_object* v_options_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_105_ = lean_st_ref_get(v___y_103_);
v_env_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_env_106_);
lean_dec(v___x_105_);
v___x_107_ = lean_st_ref_get(v___y_101_);
v_toCold_108_ = lean_ctor_get(v___y_102_, 0);
v_mctx_109_ = lean_ctor_get(v___x_107_, 0);
lean_inc_ref(v_mctx_109_);
lean_dec(v___x_107_);
v_lctx_110_ = lean_ctor_get(v___y_100_, 2);
v_options_111_ = lean_ctor_get(v_toCold_108_, 2);
lean_inc_ref(v_options_111_);
lean_inc_ref(v_lctx_110_);
v___x_112_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_112_, 0, v_env_106_);
lean_ctor_set(v___x_112_, 1, v_mctx_109_);
lean_ctor_set(v___x_112_, 2, v_lctx_110_);
lean_ctor_set(v___x_112_, 3, v_options_111_);
v___x_113_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_msgData_99_);
v___x_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(v_msgData_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_121_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_box(1);
v___x_123_ = l_Lean_MessageData_ofFormat(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; 
v___x_127_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__2));
v___x_128_ = l_Lean_MessageData_ofFormat(v___x_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7(lean_object* v_x_129_, lean_object* v_x_130_){
_start:
{
if (lean_obj_tag(v_x_130_) == 0)
{
return v_x_129_;
}
else
{
lean_object* v_head_131_; lean_object* v_tail_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_154_; 
v_head_131_ = lean_ctor_get(v_x_130_, 0);
v_tail_132_ = lean_ctor_get(v_x_130_, 1);
v_isSharedCheck_154_ = !lean_is_exclusive(v_x_130_);
if (v_isSharedCheck_154_ == 0)
{
v___x_134_ = v_x_130_;
v_isShared_135_ = v_isSharedCheck_154_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_tail_132_);
lean_inc(v_head_131_);
lean_dec(v_x_130_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_154_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v_before_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_152_; 
v_before_136_ = lean_ctor_get(v_head_131_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v_head_131_);
if (v_isSharedCheck_152_ == 0)
{
lean_object* v_unused_153_; 
v_unused_153_ = lean_ctor_get(v_head_131_, 1);
lean_dec(v_unused_153_);
v___x_138_ = v_head_131_;
v_isShared_139_ = v_isSharedCheck_152_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_before_136_);
lean_dec(v_head_131_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_152_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0);
if (v_isShared_139_ == 0)
{
lean_ctor_set_tag(v___x_138_, 7);
lean_ctor_set(v___x_138_, 1, v___x_140_);
lean_ctor_set(v___x_138_, 0, v_x_129_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_x_129_);
lean_ctor_set(v_reuseFailAlloc_151_, 1, v___x_140_);
v___x_142_ = v_reuseFailAlloc_151_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_143_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__3);
if (v_isShared_135_ == 0)
{
lean_ctor_set_tag(v___x_134_, 7);
lean_ctor_set(v___x_134_, 1, v___x_143_);
lean_ctor_set(v___x_134_, 0, v___x_142_);
v___x_145_ = v___x_134_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_142_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_150_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = l_Lean_MessageData_ofSyntax(v_before_136_);
v___x_147_ = l_Lean_indentD(v___x_146_);
v___x_148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_145_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v_x_129_ = v___x_148_;
v_x_130_ = v_tail_132_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(lean_object* v_opts_155_, lean_object* v_opt_156_){
_start:
{
lean_object* v_name_157_; lean_object* v_defValue_158_; lean_object* v_map_159_; lean_object* v___x_160_; 
v_name_157_ = lean_ctor_get(v_opt_156_, 0);
v_defValue_158_ = lean_ctor_get(v_opt_156_, 1);
v_map_159_ = lean_ctor_get(v_opts_155_, 0);
v___x_160_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_159_, v_name_157_);
if (lean_obj_tag(v___x_160_) == 0)
{
uint8_t v___x_161_; 
v___x_161_ = lean_unbox(v_defValue_158_);
return v___x_161_;
}
else
{
lean_object* v_val_162_; 
v_val_162_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_val_162_);
lean_dec_ref_known(v___x_160_, 1);
if (lean_obj_tag(v_val_162_) == 1)
{
uint8_t v_v_163_; 
v_v_163_ = lean_ctor_get_uint8(v_val_162_, 0);
lean_dec_ref_known(v_val_162_, 0);
return v_v_163_;
}
else
{
uint8_t v___x_164_; 
lean_dec(v_val_162_);
v___x_164_ = lean_unbox(v_defValue_158_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6___boxed(lean_object* v_opts_165_, lean_object* v_opt_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(v_opts_165_, v_opt_166_);
lean_dec_ref(v_opt_166_);
lean_dec_ref(v_opts_165_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__1));
v___x_173_ = l_Lean_MessageData_ofFormat(v___x_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(lean_object* v_msgData_174_, lean_object* v_macroStack_175_, lean_object* v___y_176_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_178_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_176_);
v___x_179_ = l_Lean_Elab_pp_macroStack;
v___x_180_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__6(v___x_178_, v___x_179_);
lean_dec_ref(v___x_178_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; 
lean_dec(v_macroStack_175_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v_msgData_174_);
return v___x_181_;
}
else
{
if (lean_obj_tag(v_macroStack_175_) == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_182_, 0, v_msgData_174_);
return v___x_182_;
}
else
{
lean_object* v_head_183_; lean_object* v_after_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_199_; 
v_head_183_ = lean_ctor_get(v_macroStack_175_, 0);
lean_inc(v_head_183_);
v_after_184_ = lean_ctor_get(v_head_183_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_head_183_);
if (v_isSharedCheck_199_ == 0)
{
lean_object* v_unused_200_; 
v_unused_200_ = lean_ctor_get(v_head_183_, 0);
lean_dec(v_unused_200_);
v___x_186_ = v_head_183_;
v_isShared_187_ = v_isSharedCheck_199_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_after_184_);
lean_dec(v_head_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_199_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_188_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7___closed__0);
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 7);
lean_ctor_set(v___x_186_, 1, v___x_188_);
lean_ctor_set(v___x_186_, 0, v_msgData_174_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_msgData_174_);
lean_ctor_set(v_reuseFailAlloc_198_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_198_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_msgData_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_191_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___closed__2);
v___x_192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = l_Lean_MessageData_ofSyntax(v_after_184_);
v___x_194_ = l_Lean_indentD(v___x_193_);
v_msgData_195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_195_, 0, v___x_192_);
lean_ctor_set(v_msgData_195_, 1, v___x_194_);
v___x_196_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5_spec__7(v_msgData_195_, v_macroStack_175_);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_msgData_201_, lean_object* v_macroStack_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_msgData_201_, v_macroStack_202_, v___y_203_);
lean_dec_ref(v___y_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(lean_object* v_msg_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_ref_214_; lean_object* v_macroStack_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_228_; 
v_ref_214_ = lean_ctor_get(v___y_211_, 2);
v_macroStack_215_ = lean_ctor_get(v___y_207_, 1);
v___x_216_ = l_Lean_Elab_getBetterRef(v_ref_214_, v_macroStack_215_);
v___x_217_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__4(v_msg_206_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref(v___x_217_);
lean_inc(v_macroStack_215_);
v___x_219_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_a_218_, v_macroStack_215_, v___y_211_);
v_a_220_ = lean_ctor_get(v___x_219_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_219_);
if (v_isSharedCheck_228_ == 0)
{
v___x_222_ = v___x_219_;
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_219_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_228_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_216_);
lean_ctor_set(v___x_224_, 1, v_a_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set_tag(v___x_222_, 1);
lean_ctor_set(v___x_222_, 0, v___x_224_);
v___x_226_ = v___x_222_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg___boxed(lean_object* v_msg_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(lean_object* v_ref_238_, lean_object* v_msg_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v_toCold_247_; lean_object* v_currRecDepth_248_; lean_object* v_ref_249_; uint16_t v_optionFlags_250_; uint8_t v_suppressElabErrors_251_; uint8_t v_isRecordingDeps_252_; lean_object* v_ref_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_toCold_247_ = lean_ctor_get(v___y_244_, 0);
v_currRecDepth_248_ = lean_ctor_get(v___y_244_, 1);
v_ref_249_ = lean_ctor_get(v___y_244_, 2);
v_optionFlags_250_ = lean_ctor_get_uint16(v___y_244_, sizeof(void*)*3);
v_suppressElabErrors_251_ = lean_ctor_get_uint8(v___y_244_, sizeof(void*)*3 + 2);
v_isRecordingDeps_252_ = lean_ctor_get_uint8(v___y_244_, sizeof(void*)*3 + 3);
v_ref_253_ = l_Lean_replaceRef(v_ref_238_, v_ref_249_);
lean_inc(v_currRecDepth_248_);
lean_inc_ref(v_toCold_247_);
v___x_254_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_254_, 0, v_toCold_247_);
lean_ctor_set(v___x_254_, 1, v_currRecDepth_248_);
lean_ctor_set(v___x_254_, 2, v_ref_253_);
lean_ctor_set_uint16(v___x_254_, sizeof(void*)*3, v_optionFlags_250_);
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*3 + 2, v_suppressElabErrors_251_);
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*3 + 3, v_isRecordingDeps_252_);
v___x_255_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___x_254_, v___y_245_);
lean_dec_ref_known(v___x_254_, 3);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg___boxed(lean_object* v_ref_256_, lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_ref_256_, v_msg_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v_ref_256_);
return v_res_265_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__2));
v___x_271_ = l_Lean_stringToMessageData(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__4));
v___x_274_ = l_Lean_stringToMessageData(v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(lean_object* v_optionPrefix_275_, lean_object* v_opts_276_, lean_object* v_item_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_option_300_; lean_object* v_value_301_; lean_object* v_optionComps_302_; lean_object* v___x_303_; lean_object* v_optName_304_; lean_object* v_inst_306_; lean_object* v_inst_307_; lean_object* v_inst_308_; lean_object* v___y_309_; lean_object* v___y_310_; lean_object* v___y_311_; lean_object* v___y_312_; lean_object* v___y_313_; lean_object* v___y_314_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_414_; 
v___x_285_ = l_Lean_Elab_ConfigEval_EvalTerm_instBool;
v___x_286_ = l_Lean_Elab_ConfigEval_EvalExpr_instBool;
v___x_287_ = l_Lean_KVMap_instValueBool;
v___x_288_ = l_Lean_Elab_ConfigEval_EvalTerm_instNat;
v___x_289_ = l_Lean_Elab_ConfigEval_EvalExpr_instNat;
v___x_290_ = l_Lean_KVMap_instValueNat;
v___x_291_ = l_Lean_Elab_ConfigEval_EvalTerm_instInt;
v___x_292_ = l_Lean_Elab_ConfigEval_EvalExpr_instInt;
v___x_293_ = l_Lean_KVMap_instValueInt;
v___x_294_ = l_Lean_Elab_ConfigEval_EvalTerm_instString;
v___x_295_ = l_Lean_Elab_ConfigEval_EvalExpr_instString;
v___x_296_ = l_Lean_KVMap_instValueString;
v___x_297_ = l_Lean_Elab_ConfigEval_EvalTerm_instName;
v___x_298_ = l_Lean_Elab_ConfigEval_EvalExpr_instName;
v___x_299_ = l_Lean_KVMap_instValueName;
v_option_300_ = lean_ctor_get(v_item_277_, 1);
v_value_301_ = lean_ctor_get(v_item_277_, 2);
lean_inc(v_value_301_);
v_optionComps_302_ = lean_ctor_get(v_item_277_, 5);
lean_inc_ref(v_item_277_);
v___x_303_ = l_Lean_Elab_ConfigEval_ConfigItem_getCurrOptionName(v_item_277_);
v_optName_304_ = l_Lean_Name_append(v_optionPrefix_275_, v___x_303_);
v___x_333_ = l_Lean_Elab_ConfigEval_ConfigItem_prevRoot(v_item_277_);
lean_inc(v_optionComps_302_);
v___x_334_ = lean_array_mk(v_optionComps_302_);
v___x_335_ = ((lean_object*)(l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__1));
v___x_336_ = lean_box(2);
v___x_337_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
lean_ctor_set(v___x_337_, 2, v___x_334_);
v___x_338_ = lean_unsigned_to_nat(2u);
v___x_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
v___x_340_ = lean_array_push(v___x_339_, v___x_333_);
v___x_341_ = lean_array_push(v___x_340_, v___x_337_);
v___x_342_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_342_, 0, v___x_336_);
lean_ctor_set(v___x_342_, 1, v___x_335_);
lean_ctor_set(v___x_342_, 2, v___x_341_);
v___x_343_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
v___x_344_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__0(v___x_343_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_414_ == 0)
{
lean_object* v_unused_415_; 
v_unused_415_ = lean_ctor_get(v___x_344_, 0);
lean_dec(v_unused_415_);
v___x_346_ = v___x_344_;
v_isShared_347_ = v_isSharedCheck_414_;
goto v_resetjp_345_;
}
else
{
lean_dec(v___x_344_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_414_;
goto v_resetjp_345_;
}
v___jp_305_:
{
lean_object* v___x_315_; 
lean_inc_ref(v_inst_307_);
lean_inc_ref(v_inst_306_);
v___x_315_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___redArg(v_inst_306_, v_inst_307_, v_value_301_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
if (lean_obj_tag(v___x_315_) == 0)
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_324_; 
v_a_316_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_324_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_324_ == 0)
{
v___x_318_ = v___x_315_;
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_315_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_324_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
lean_inc_ref(v_inst_308_);
v___x_320_ = l_Lean_Options_set___redArg(v_inst_308_, v_opts_276_, v_optName_304_, v_a_316_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_320_);
v___x_322_ = v_reuseFailAlloc_323_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
return v___x_322_;
}
}
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
lean_dec(v_optName_304_);
lean_dec_ref(v_opts_276_);
v_a_325_ = lean_ctor_get(v___x_315_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_315_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_315_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_315_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
v_resetjp_345_:
{
lean_object* v_ref_348_; lean_object* v___x_349_; 
v_ref_348_ = lean_ctor_get(v_a_282_, 2);
lean_inc(v_optName_304_);
v___x_349_ = l_Lean_getOptionDecl(v_optName_304_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v_declName_351_; lean_object* v_defValue_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_a_350_);
lean_dec_ref_known(v___x_349_, 1);
v_declName_351_ = lean_ctor_get(v_a_350_, 1);
lean_inc(v_declName_351_);
v_defValue_352_ = lean_ctor_get(v_a_350_, 2);
lean_inc_ref(v_defValue_352_);
lean_dec(v_a_350_);
lean_inc(v_optName_304_);
lean_inc(v_option_300_);
v___x_353_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_353_, 0, v_option_300_);
lean_ctor_set(v___x_353_, 1, v_optName_304_);
lean_ctor_set(v___x_353_, 2, v_declName_351_);
if (v_isShared_347_ == 0)
{
lean_ctor_set_tag(v___x_346_, 5);
lean_ctor_set(v___x_346_, 0, v___x_353_);
v___x_355_ = v___x_346_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v___x_353_);
v___x_355_ = v_reuseFailAlloc_399_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1(v___x_355_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec_ref(v___x_356_);
switch(lean_obj_tag(v_defValue_352_))
{
case 0:
{
lean_object* v___x_357_; 
lean_dec_ref_known(v_defValue_352_, 1);
v___x_357_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_dec_ref_known(v___x_357_, 1);
v_inst_306_ = v___x_294_;
v_inst_307_ = v___x_295_;
v_inst_308_ = v___x_296_;
v___y_309_ = v_a_278_;
v___y_310_ = v_a_279_;
v___y_311_ = v_a_280_;
v___y_312_ = v_a_281_;
v___y_313_ = v_a_282_;
v___y_314_ = v_a_283_;
goto v___jp_305_;
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec(v_optName_304_);
lean_dec(v_value_301_);
lean_dec_ref(v_opts_276_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
case 1:
{
lean_dec_ref_known(v_defValue_352_, 0);
lean_dec_ref(v_item_277_);
v_inst_306_ = v___x_285_;
v_inst_307_ = v___x_286_;
v_inst_308_ = v___x_287_;
v___y_309_ = v_a_278_;
v___y_310_ = v_a_279_;
v___y_311_ = v_a_280_;
v___y_312_ = v_a_281_;
v___y_313_ = v_a_282_;
v___y_314_ = v_a_283_;
goto v___jp_305_;
}
case 2:
{
lean_object* v___x_366_; 
lean_dec_ref_known(v_defValue_352_, 1);
v___x_366_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_dec_ref_known(v___x_366_, 1);
v_inst_306_ = v___x_297_;
v_inst_307_ = v___x_298_;
v_inst_308_ = v___x_299_;
v___y_309_ = v_a_278_;
v___y_310_ = v_a_279_;
v___y_311_ = v_a_280_;
v___y_312_ = v_a_281_;
v___y_313_ = v_a_282_;
v___y_314_ = v_a_283_;
goto v___jp_305_;
}
else
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_374_; 
lean_dec(v_optName_304_);
lean_dec(v_value_301_);
lean_dec_ref(v_opts_276_);
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_374_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_374_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_370_ == 0)
{
v___x_372_ = v___x_369_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_a_367_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
case 3:
{
lean_object* v___x_375_; 
lean_dec_ref_known(v_defValue_352_, 1);
v___x_375_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
if (lean_obj_tag(v___x_375_) == 0)
{
lean_dec_ref_known(v___x_375_, 1);
v_inst_306_ = v___x_288_;
v_inst_307_ = v___x_289_;
v_inst_308_ = v___x_290_;
v___y_309_ = v_a_278_;
v___y_310_ = v_a_279_;
v___y_311_ = v_a_280_;
v___y_312_ = v_a_281_;
v___y_313_ = v_a_282_;
v___y_314_ = v_a_283_;
goto v___jp_305_;
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec(v_optName_304_);
lean_dec(v_value_301_);
lean_dec_ref(v_opts_276_);
v_a_376_ = lean_ctor_get(v___x_375_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_375_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_375_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_375_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
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
case 4:
{
lean_object* v___x_384_; 
lean_dec_ref_known(v_defValue_352_, 1);
v___x_384_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_dec_ref_known(v___x_384_, 1);
v_inst_306_ = v___x_291_;
v_inst_307_ = v___x_292_;
v_inst_308_ = v___x_293_;
v___y_309_ = v_a_278_;
v___y_310_ = v_a_279_;
v___y_311_ = v_a_280_;
v___y_312_ = v_a_281_;
v___y_313_ = v_a_282_;
v___y_314_ = v_a_283_;
goto v___jp_305_;
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_dec(v_optName_304_);
lean_dec(v_value_301_);
lean_dec_ref(v_opts_276_);
v_a_385_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_384_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_384_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
default: 
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
lean_inc(v_option_300_);
lean_dec_ref_known(v_defValue_352_, 1);
lean_dec(v_value_301_);
lean_dec_ref(v_item_277_);
lean_dec_ref(v_opts_276_);
v___x_393_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3, &l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__3);
v___x_394_ = l_Lean_MessageData_ofName(v_optName_304_);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_obj_once(&l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5, &l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5_once, _init_l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___closed__5);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_option_300_, v___x_397_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_);
lean_dec(v_option_300_);
return v___x_398_;
}
}
}
}
else
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_413_; 
lean_dec(v_optName_304_);
lean_dec(v_value_301_);
lean_dec_ref(v_item_277_);
lean_dec_ref(v_opts_276_);
v_a_400_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_413_ == 0)
{
v___x_402_ = v___x_349_;
v_isShared_403_ = v_isSharedCheck_413_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_349_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_413_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_404_ = lean_io_error_to_string(v_a_400_);
if (v_isShared_347_ == 0)
{
lean_ctor_set_tag(v___x_346_, 3);
lean_ctor_set(v___x_346_, 0, v___x_404_);
v___x_406_ = v___x_346_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_412_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_407_ = l_Lean_MessageData_ofFormat(v___x_406_);
lean_inc(v_ref_348_);
v___x_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_408_, 0, v_ref_348_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v___x_408_);
v___x_410_ = v___x_402_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v___x_408_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions___boxed(lean_object* v_optionPrefix_416_, lean_object* v_opts_417_, lean_object* v_item_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions(v_optionPrefix_416_, v_opts_417_, v_item_418_, v_a_419_, v_a_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
lean_dec(v_a_420_);
lean_dec_ref(v_a_419_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(lean_object* v_t_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___redArg(v_t_427_, v___y_433_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1___boxed(lean_object* v_t_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__1_spec__1(v_t_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(lean_object* v_00_u03b1_445_, lean_object* v_ref_446_, lean_object* v_msg_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___redArg(v_ref_446_, v_msg_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2___boxed(lean_object* v_00_u03b1_456_, lean_object* v_ref_457_, lean_object* v_msg_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2(v_00_u03b1_456_, v_ref_457_, v_msg_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v_ref_457_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(lean_object* v_00_u03b1_467_, lean_object* v_msg_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___redArg(v_msg_468_, v___y_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3___boxed(lean_object* v_00_u03b1_477_, lean_object* v_msg_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3(v_00_u03b1_477_, v_msg_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(lean_object* v_msgData_487_, lean_object* v_macroStack_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___redArg(v_msgData_487_, v_macroStack_488_, v___y_493_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_497_, lean_object* v_macroStack_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_ConfigEval_EvalConfigItem_evalSetOptions_spec__2_spec__3_spec__5(v_msgData_497_, v_macroStack_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec_ref(v___y_501_);
lean_dec(v___y_500_);
lean_dec_ref(v___y_499_);
return v_res_506_;
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
