// Lean compiler output
// Module: Lean.Server.Snapshots
// Imports: public import Lean.Elab.Import public import Lean.Elab.Command public import Lean.Widget.InteractiveDiagnostic
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
lean_object* l_Lean_Elab_Command_liftTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_firstFrontendMacroScope;
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_liftCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object*);
lean_object* lean_task_get_own(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedInfoTree_default;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Snapshots_Snapshot_infoTree_spec__0(lean_object*);
static const lean_string_object l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.Snapshots"};
static const lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0 = (const lean_object*)&l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0_value;
static const lean_string_object l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Server.Snapshots.Snapshot.infoTree"};
static const lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1 = (const lean_object*)&l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1_value;
static const lean_string_object l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "assertion violation: infoState.trees.size == 1\n  "};
static const lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2 = (const lean_object*)&l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2_value;
static lean_once_cell_t l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_Snapshots_Snapshot_isAtEnd(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_isAtEnd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object* v_s_1_){
_start:
{
lean_object* v_mpState_2_; lean_object* v_pos_3_; 
v_mpState_2_ = lean_ctor_get(v_s_1_, 1);
v_pos_3_ = lean_ctor_get(v_mpState_2_, 0);
lean_inc(v_pos_3_);
return v_pos_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_endPos___boxed(lean_object* v_s_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Server_Snapshots_Snapshot_endPos(v_s_4_);
lean_dec_ref(v_s_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env(lean_object* v_s_6_){
_start:
{
lean_object* v_cmdState_7_; lean_object* v_env_8_; 
v_cmdState_7_ = lean_ctor_get(v_s_6_, 2);
v_env_8_ = lean_ctor_get(v_cmdState_7_, 0);
lean_inc_ref(v_env_8_);
return v_env_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_env___boxed(lean_object* v_s_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_Server_Snapshots_Snapshot_env(v_s_9_);
lean_dec_ref(v_s_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog(lean_object* v_s_11_){
_start:
{
lean_object* v_cmdState_12_; lean_object* v_messages_13_; 
v_cmdState_12_ = lean_ctor_get(v_s_11_, 2);
v_messages_13_ = lean_ctor_get(v_cmdState_12_, 1);
lean_inc_ref(v_messages_13_);
return v_messages_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_msgLog___boxed(lean_object* v_s_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Server_Snapshots_Snapshot_msgLog(v_s_14_);
lean_dec_ref(v_s_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_Snapshots_Snapshot_infoTree_spec__0(lean_object* v_msg_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_18_ = lean_panic_fn_borrowed(v___x_17_, v_msg_16_);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_22_ = ((lean_object*)(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__2));
v___x_23_ = lean_unsigned_to_nat(2u);
v___x_24_ = lean_unsigned_to_nat(48u);
v___x_25_ = ((lean_object*)(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__1));
v___x_26_ = ((lean_object*)(l_Lean_Server_Snapshots_Snapshot_infoTree___closed__0));
v___x_27_ = l_mkPanicMessageWithDecl(v___x_26_, v___x_25_, v___x_24_, v___x_23_, v___x_22_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object* v_s_28_){
_start:
{
lean_object* v_cmdState_29_; lean_object* v_infoState_30_; lean_object* v___x_31_; lean_object* v_infoState_32_; lean_object* v_trees_33_; lean_object* v_size_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v_cmdState_29_ = lean_ctor_get(v_s_28_, 2);
lean_inc_ref(v_cmdState_29_);
lean_dec_ref(v_s_28_);
v_infoState_30_ = lean_ctor_get(v_cmdState_29_, 8);
lean_inc_ref(v_infoState_30_);
lean_dec_ref(v_cmdState_29_);
v___x_31_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_30_);
v_infoState_32_ = lean_task_get_own(v___x_31_);
v_trees_33_ = lean_ctor_get(v_infoState_32_, 2);
lean_inc_ref(v_trees_33_);
lean_dec(v_infoState_32_);
v_size_34_ = lean_ctor_get(v_trees_33_, 2);
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_dec_eq(v_size_34_, v___x_35_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; lean_object* v___x_38_; 
lean_dec_ref(v_trees_33_);
v___x_37_ = lean_obj_once(&l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3, &l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3_once, _init_l_Lean_Server_Snapshots_Snapshot_infoTree___closed__3);
v___x_38_ = l_panic___at___00Lean_Server_Snapshots_Snapshot_infoTree_spec__0(v___x_37_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_39_ = l_Lean_Elab_instInhabitedInfoTree_default;
v___x_40_ = lean_unsigned_to_nat(0u);
v___x_41_ = lean_nat_dec_lt(v___x_40_, v_size_34_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
lean_dec_ref(v_trees_33_);
v___x_42_ = l_outOfBounds___redArg(v___x_39_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_PersistentArray_get_x21___redArg(v___x_39_, v_trees_33_, v___x_40_);
lean_dec_ref(v_trees_33_);
return v___x_43_;
}
}
}
}
uint8_t l_Lean_Server_Snapshots_Snapshot_isAtEnd(lean_object* v_s_44_){
_start:
{
lean_object* v_stx_45_; uint8_t v___x_46_; 
v_stx_45_ = lean_ctor_get(v_s_44_, 0);
lean_inc(v_stx_45_);
lean_dec_ref(v_s_44_);
v___x_46_ = l_Lean_Parser_isTerminalCommand(v_stx_45_);
return v___x_46_;
}
}
LEAN_EXPORT void l_Lean_Server_Snapshots_Snapshot_isAtEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_44_ = stack[0].m_obj;
uint8_t v_res_47_;
v_res_47_ = l_Lean_Server_Snapshots_Snapshot_isAtEnd(v_s_44_);
stack->m_num = v_res_47_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_isAtEnd___boxed(lean_object* v_s_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Lean_Server_Snapshots_Snapshot_isAtEnd(v_s_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(lean_object* v_snap_51_, lean_object* v_doc_52_, lean_object* v_c_53_){
_start:
{
lean_object* v_uri_55_; lean_object* v_text_56_; lean_object* v_stx_57_; lean_object* v_cmdState_58_; lean_object* v___x_59_; uint8_t v___x_60_; lean_object* v___y_62_; lean_object* v___x_79_; 
v_uri_55_ = lean_ctor_get(v_doc_52_, 0);
v_text_56_ = lean_ctor_get(v_doc_52_, 3);
v_stx_57_ = lean_ctor_get(v_snap_51_, 0);
lean_inc(v_stx_57_);
v_cmdState_58_ = lean_ctor_get(v_snap_51_, 2);
lean_inc_ref(v_cmdState_58_);
lean_dec_ref(v_snap_51_);
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = 0;
v___x_79_ = l_Lean_Syntax_getPos_x3f(v_stx_57_, v___x_60_);
lean_dec(v_stx_57_);
if (lean_obj_tag(v___x_79_) == 0)
{
v___y_62_ = v___x_59_;
goto v___jp_61_;
}
else
{
lean_object* v_val_80_; 
v_val_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v___x_79_, 1);
v___y_62_ = v_val_80_;
goto v___jp_61_;
}
v___jp_61_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v_ctx_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_63_ = lean_box(0);
v___x_64_ = lean_box(0);
v___x_65_ = l_Lean_firstFrontendMacroScope;
v___x_66_ = lean_box(0);
lean_inc_ref(v_text_56_);
lean_inc_ref(v_uri_55_);
v_ctx_67_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v_ctx_67_, 0, v_uri_55_);
lean_ctor_set(v_ctx_67_, 1, v_text_56_);
lean_ctor_set(v_ctx_67_, 2, v___x_59_);
lean_ctor_set(v_ctx_67_, 3, v___y_62_);
lean_ctor_set(v_ctx_67_, 4, v___x_63_);
lean_ctor_set(v_ctx_67_, 5, v___x_64_);
lean_ctor_set(v_ctx_67_, 6, v___x_65_);
lean_ctor_set(v_ctx_67_, 7, v___x_66_);
lean_ctor_set(v_ctx_67_, 8, v___x_64_);
lean_ctor_set(v_ctx_67_, 9, v___x_64_);
lean_ctor_set_uint8(v_ctx_67_, sizeof(void*)*10, v___x_60_);
v___x_68_ = lean_st_mk_ref(v_cmdState_58_);
lean_inc(v___x_68_);
v___x_69_ = lean_apply_3(v_c_53_, v_ctx_67_, v___x_68_, lean_box(0));
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_78_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_78_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_78_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_74_ = lean_st_ref_get(v___x_68_);
lean_dec(v___x_68_);
lean_dec(v___x_74_);
if (v_isShared_73_ == 0)
{
v___x_76_ = v___x_72_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_70_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
else
{
lean_dec(v___x_68_);
return v___x_69_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_51_ = stack[0].m_obj;
lean_object* v_doc_52_ = stack[1].m_obj;
lean_object* v_c_53_ = stack[2].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_51_, v_doc_52_, v_c_53_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg___boxed(lean_object* v_snap_82_, lean_object* v_doc_83_, lean_object* v_c_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_82_, v_doc_83_, v_c_84_);
lean_dec_ref(v_doc_83_);
return v_res_86_;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM(lean_object* v_00_u03b1_87_, lean_object* v_snap_88_, lean_object* v_doc_89_, lean_object* v_c_90_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_88_, v_doc_89_, v_c_90_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Lean_Server_Snapshots_Snapshot_runCommandElabM_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_88_ = stack[1].m_obj;
lean_object* v_doc_89_ = stack[2].m_obj;
lean_object* v_c_90_ = stack[3].m_obj;
lean_object* v_res_93_;
v_res_93_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM(lean_box(0), v_snap_88_, v_doc_89_, v_c_90_);
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___boxed(lean_object* v_00_u03b1_94_, lean_object* v_snap_95_, lean_object* v_doc_96_, lean_object* v_c_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM(v_00_u03b1_94_, v_snap_95_, v_doc_96_, v_c_97_);
lean_dec_ref(v_doc_96_);
return v_res_99_;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(lean_object* v_snap_100_, lean_object* v_doc_101_, lean_object* v_c_102_){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_104_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM___boxed), 5, 2);
lean_closure_set(v___x_104_, 0, lean_box(0));
lean_closure_set(v___x_104_, 1, v_c_102_);
v___x_105_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_100_, v_doc_101_, v___x_104_);
return v___x_105_;
}
}
LEAN_EXPORT void l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_100_ = stack[0].m_obj;
lean_object* v_doc_101_ = stack[1].m_obj;
lean_object* v_c_102_ = stack[2].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_100_, v_doc_101_, v_c_102_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg___boxed(lean_object* v_snap_107_, lean_object* v_doc_108_, lean_object* v_c_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_107_, v_doc_108_, v_c_109_);
lean_dec_ref(v_doc_108_);
return v_res_111_;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM(lean_object* v_00_u03b1_112_, lean_object* v_snap_113_, lean_object* v_doc_114_, lean_object* v_c_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_113_, v_doc_114_, v_c_115_);
return v___x_117_;
}
}
LEAN_EXPORT void l_Lean_Server_Snapshots_Snapshot_runCoreM_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_113_ = stack[1].m_obj;
lean_object* v_doc_114_ = stack[2].m_obj;
lean_object* v_c_115_ = stack[3].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_Lean_Server_Snapshots_Snapshot_runCoreM(lean_box(0), v_snap_113_, v_doc_114_, v_c_115_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___boxed(lean_object* v_00_u03b1_119_, lean_object* v_snap_120_, lean_object* v_doc_121_, lean_object* v_c_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Server_Snapshots_Snapshot_runCoreM(v_00_u03b1_119_, v_snap_120_, v_doc_121_, v_c_122_);
lean_dec_ref(v_doc_121_);
return v_res_124_;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(lean_object* v_snap_125_, lean_object* v_doc_126_, lean_object* v_c_127_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_129_, 0, lean_box(0));
lean_closure_set(v___x_129_, 1, v_c_127_);
v___x_130_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_125_, v_doc_126_, v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT void l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_125_ = stack[0].m_obj;
lean_object* v_doc_126_ = stack[1].m_obj;
lean_object* v_c_127_ = stack[2].m_obj;
lean_object* v_res_131_;
v_res_131_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_125_, v_doc_126_, v_c_127_);
stack->m_obj
 = v_res_131_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg___boxed(lean_object* v_snap_132_, lean_object* v_doc_133_, lean_object* v_c_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_132_, v_doc_133_, v_c_134_);
lean_dec_ref(v_doc_133_);
return v_res_136_;
}
}
lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM(lean_object* v_00_u03b1_137_, lean_object* v_snap_138_, lean_object* v_doc_139_, lean_object* v_c_140_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_138_, v_doc_139_, v_c_140_);
return v___x_142_;
}
}
LEAN_EXPORT void l_Lean_Server_Snapshots_Snapshot_runTermElabM_0interp(lean_interpreter_value* stack)
{
lean_object* v_snap_138_ = stack[1].m_obj;
lean_object* v_doc_139_ = stack[2].m_obj;
lean_object* v_c_140_ = stack[3].m_obj;
lean_object* v_res_143_;
v_res_143_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM(lean_box(0), v_snap_138_, v_doc_139_, v_c_140_);
stack->m_obj
 = v_res_143_;
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___boxed(lean_object* v_00_u03b1_144_, lean_object* v_snap_145_, lean_object* v_doc_146_, lean_object* v_c_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM(v_00_u03b1_144_, v_snap_145_, v_doc_146_, v_c_147_);
lean_dec_ref(v_doc_146_);
return v_res_149_;
}
}
lean_object* runtime_initialize_Lean_Elab_Import(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* runtime_initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_Snapshots(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Widget_InteractiveDiagnostic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_Snapshots(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Import(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
lean_object* initialize_Lean_Widget_InteractiveDiagnostic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_Snapshots(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Import(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_InteractiveDiagnostic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Snapshots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_Snapshots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_Snapshots(builtin);
}
#ifdef __cplusplus
}
#endif
