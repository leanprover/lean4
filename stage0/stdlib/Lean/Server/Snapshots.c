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
LEAN_EXPORT uint8_t l_Lean_Server_Snapshots_Snapshot_isAtEnd(lean_object* v_s_44_){
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
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_isAtEnd___boxed(lean_object* v_s_47_){
_start:
{
uint8_t v_res_48_; lean_object* v_r_49_; 
v_res_48_ = l_Lean_Server_Snapshots_Snapshot_isAtEnd(v_s_47_);
v_r_49_ = lean_box(v_res_48_);
return v_r_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(lean_object* v_snap_50_, lean_object* v_doc_51_, lean_object* v_c_52_){
_start:
{
lean_object* v_uri_54_; lean_object* v_text_55_; lean_object* v_stx_56_; lean_object* v_cmdState_57_; lean_object* v___x_58_; uint8_t v___x_59_; lean_object* v___y_61_; lean_object* v___x_79_; 
v_uri_54_ = lean_ctor_get(v_doc_51_, 0);
v_text_55_ = lean_ctor_get(v_doc_51_, 3);
v_stx_56_ = lean_ctor_get(v_snap_50_, 0);
lean_inc(v_stx_56_);
v_cmdState_57_ = lean_ctor_get(v_snap_50_, 2);
lean_inc_ref(v_cmdState_57_);
lean_dec_ref(v_snap_50_);
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = 0;
v___x_79_ = l_Lean_Syntax_getPos_x3f(v_stx_56_, v___x_59_);
lean_dec(v_stx_56_);
if (lean_obj_tag(v___x_79_) == 0)
{
v___y_61_ = v___x_58_;
goto v___jp_60_;
}
else
{
lean_object* v_val_80_; 
v_val_80_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_val_80_);
lean_dec_ref_known(v___x_79_, 1);
v___y_61_ = v_val_80_;
goto v___jp_60_;
}
v___jp_60_:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; uint8_t v___x_66_; lean_object* v_ctx_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_62_ = lean_box(0);
v___x_63_ = lean_box(0);
v___x_64_ = l_Lean_firstFrontendMacroScope;
v___x_65_ = lean_box(0);
v___x_66_ = 0;
lean_inc_ref(v_text_55_);
lean_inc_ref(v_uri_54_);
v_ctx_67_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v_ctx_67_, 0, v_uri_54_);
lean_ctor_set(v_ctx_67_, 1, v_text_55_);
lean_ctor_set(v_ctx_67_, 2, v___x_58_);
lean_ctor_set(v_ctx_67_, 3, v___y_61_);
lean_ctor_set(v_ctx_67_, 4, v___x_62_);
lean_ctor_set(v_ctx_67_, 5, v___x_63_);
lean_ctor_set(v_ctx_67_, 6, v___x_64_);
lean_ctor_set(v_ctx_67_, 7, v___x_65_);
lean_ctor_set(v_ctx_67_, 8, v___x_63_);
lean_ctor_set(v_ctx_67_, 9, v___x_63_);
lean_ctor_set_uint8(v_ctx_67_, sizeof(void*)*10, v___x_59_);
lean_ctor_set_uint8(v_ctx_67_, sizeof(void*)*10 + 1, v___x_66_);
v___x_68_ = lean_st_mk_ref(v_cmdState_57_);
lean_inc(v___x_68_);
v___x_69_ = lean_apply_3(v_c_52_, v_ctx_67_, v___x_68_, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg___boxed(lean_object* v_snap_81_, lean_object* v_doc_82_, lean_object* v_c_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_81_, v_doc_82_, v_c_83_);
lean_dec_ref(v_doc_82_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM(lean_object* v_00_u03b1_86_, lean_object* v_snap_87_, lean_object* v_doc_88_, lean_object* v_c_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_87_, v_doc_88_, v_c_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCommandElabM___boxed(lean_object* v_00_u03b1_92_, lean_object* v_snap_93_, lean_object* v_doc_94_, lean_object* v_c_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM(v_00_u03b1_92_, v_snap_93_, v_doc_94_, v_c_95_);
lean_dec_ref(v_doc_94_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(lean_object* v_snap_98_, lean_object* v_doc_99_, lean_object* v_c_100_){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftCoreM___boxed), 5, 2);
lean_closure_set(v___x_102_, 0, lean_box(0));
lean_closure_set(v___x_102_, 1, v_c_100_);
v___x_103_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_98_, v_doc_99_, v___x_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg___boxed(lean_object* v_snap_104_, lean_object* v_doc_105_, lean_object* v_c_106_, lean_object* v_a_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_104_, v_doc_105_, v_c_106_);
lean_dec_ref(v_doc_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM(lean_object* v_00_u03b1_109_, lean_object* v_snap_110_, lean_object* v_doc_111_, lean_object* v_c_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Server_Snapshots_Snapshot_runCoreM___redArg(v_snap_110_, v_doc_111_, v_c_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runCoreM___boxed(lean_object* v_00_u03b1_115_, lean_object* v_snap_116_, lean_object* v_doc_117_, lean_object* v_c_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Server_Snapshots_Snapshot_runCoreM(v_00_u03b1_115_, v_snap_116_, v_doc_117_, v_c_118_);
lean_dec_ref(v_doc_117_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(lean_object* v_snap_121_, lean_object* v_doc_122_, lean_object* v_c_123_){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_alloc_closure((void*)(l_Lean_Elab_Command_liftTermElabM___boxed), 5, 2);
lean_closure_set(v___x_125_, 0, lean_box(0));
lean_closure_set(v___x_125_, 1, v_c_123_);
v___x_126_ = l_Lean_Server_Snapshots_Snapshot_runCommandElabM___redArg(v_snap_121_, v_doc_122_, v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg___boxed(lean_object* v_snap_127_, lean_object* v_doc_128_, lean_object* v_c_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_127_, v_doc_128_, v_c_129_);
lean_dec_ref(v_doc_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM(lean_object* v_00_u03b1_132_, lean_object* v_snap_133_, lean_object* v_doc_134_, lean_object* v_c_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM___redArg(v_snap_133_, v_doc_134_, v_c_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_Snapshots_Snapshot_runTermElabM___boxed(lean_object* v_00_u03b1_138_, lean_object* v_snap_139_, lean_object* v_doc_140_, lean_object* v_c_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Server_Snapshots_Snapshot_runTermElabM(v_00_u03b1_138_, v_snap_139_, v_doc_140_, v_c_141_);
lean_dec_ref(v_doc_140_);
return v_res_143_;
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
