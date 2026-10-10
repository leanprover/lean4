// Lean compiler output
// Module: Lean.Elab.BuiltinDo.Basic
// Imports: public import Lean.Elab.Do.Basic meta import Lean.Parser.Do
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
lean_object* l_Lean_Meta_getFVarFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addLocalVarInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_withLCtxKeepingMutVarDefs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoElem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__0(lean_object* v___x_1_, lean_object* v_x_2_, lean_object* v_k_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_Meta_getFVarFromUserName(v___x_1_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
if (lean_obj_tag(v___x_12_) == 0)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_13_ = lean_ctor_get(v___x_12_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v___x_12_, 1);
v___x_14_ = l_Lean_Elab_Term_addLocalVarInfo(v_x_2_, v_a_13_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v___x_15_; 
lean_dec_ref_known(v___x_14_, 1);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
lean_inc_ref(v___y_4_);
v___x_15_ = lean_apply_8(v_k_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, lean_box(0));
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_23_; 
lean_dec_ref(v_k_3_);
v_a_16_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_23_ == 0)
{
v___x_18_ = v___x_14_;
v_isShared_19_ = v_isSharedCheck_23_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_a_16_);
lean_dec(v___x_14_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_23_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v___x_21_; 
if (v_isShared_19_ == 0)
{
v___x_21_ = v___x_18_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_a_16_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
}
else
{
lean_dec_ref(v_k_3_);
lean_dec(v_x_2_);
return v___x_12_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoIdDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1_ = stack[0].m_obj;
lean_object* v_x_2_ = stack[1].m_obj;
lean_object* v_k_3_ = stack[2].m_obj;
lean_object* v___y_4_ = stack[3].m_obj;
lean_object* v___y_5_ = stack[4].m_obj;
lean_object* v___y_6_ = stack[5].m_obj;
lean_object* v___y_7_ = stack[6].m_obj;
lean_object* v___y_8_ = stack[7].m_obj;
lean_object* v___y_9_ = stack[8].m_obj;
lean_object* v___y_10_ = stack[9].m_obj;
lean_object* v_res_24_;
v_res_24_ = l_Lean_Elab_Do_elabDoIdDecl___lam__0(v___x_1_, v_x_2_, v_k_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
stack->m_obj
 = v_res_24_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__0___boxed(lean_object* v___x_25_, lean_object* v_x_26_, lean_object* v_k_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Elab_Do_elabDoIdDecl___lam__0(v___x_25_, v_x_26_, v_k_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
lean_dec_ref(v___y_28_);
return v_res_36_;
}
}
lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__1(lean_object* v_ref_37_, lean_object* v_lctx_38_, lean_object* v_a_39_, lean_object* v___x_40_, lean_object* v___f_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_){
_start:
{
lean_object* v_toCold_50_; lean_object* v_currRecDepth_51_; lean_object* v_ref_52_; uint16_t v_optionFlags_53_; uint8_t v_suppressElabErrors_54_; uint8_t v_isRecordingDeps_55_; lean_object* v_ref_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v_toCold_50_ = lean_ctor_get(v___y_47_, 0);
v_currRecDepth_51_ = lean_ctor_get(v___y_47_, 1);
v_ref_52_ = lean_ctor_get(v___y_47_, 2);
v_optionFlags_53_ = lean_ctor_get_uint16(v___y_47_, sizeof(void*)*3);
v_suppressElabErrors_54_ = lean_ctor_get_uint8(v___y_47_, sizeof(void*)*3 + 2);
v_isRecordingDeps_55_ = lean_ctor_get_uint8(v___y_47_, sizeof(void*)*3 + 3);
v_ref_56_ = l_Lean_replaceRef(v_ref_37_, v_ref_52_);
lean_inc(v_currRecDepth_51_);
lean_inc_ref(v_toCold_50_);
v___x_57_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_57_, 0, v_toCold_50_);
lean_ctor_set(v___x_57_, 1, v_currRecDepth_51_);
lean_ctor_set(v___x_57_, 2, v_ref_56_);
lean_ctor_set_uint16(v___x_57_, sizeof(void*)*3, v_optionFlags_53_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*3 + 2, v_suppressElabErrors_54_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*3 + 3, v_isRecordingDeps_55_);
lean_inc_ref(v_a_39_);
v___x_58_ = l_Lean_Elab_Do_withLCtxKeepingMutVarDefs___redArg(v_lctx_38_, v_a_39_, v___x_40_, v___f_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___x_57_, v___y_48_);
lean_dec_ref_known(v___x_57_, 3);
return v___x_58_;
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoIdDecl___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_37_ = stack[0].m_obj;
lean_object* v_lctx_38_ = stack[1].m_obj;
lean_object* v_a_39_ = stack[2].m_obj;
lean_object* v___x_40_ = stack[3].m_obj;
lean_object* v___f_41_ = stack[4].m_obj;
lean_object* v___y_42_ = stack[5].m_obj;
lean_object* v___y_43_ = stack[6].m_obj;
lean_object* v___y_44_ = stack[7].m_obj;
lean_object* v___y_45_ = stack[8].m_obj;
lean_object* v___y_46_ = stack[9].m_obj;
lean_object* v___y_47_ = stack[10].m_obj;
lean_object* v___y_48_ = stack[11].m_obj;
lean_object* v_res_59_;
v_res_59_ = l_Lean_Elab_Do_elabDoIdDecl___lam__1(v_ref_37_, v_lctx_38_, v_a_39_, v___x_40_, v___f_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___y_46_, v___y_47_, v___y_48_);
stack->m_obj
 = v_res_59_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__1___boxed(lean_object* v_ref_60_, lean_object* v_lctx_61_, lean_object* v_a_62_, lean_object* v___x_63_, lean_object* v___f_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Elab_Do_elabDoIdDecl___lam__1(v_ref_60_, v_lctx_61_, v_a_62_, v___x_63_, v___f_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec(v___y_69_);
lean_dec_ref(v___y_68_);
lean_dec(v___y_67_);
lean_dec_ref(v___y_66_);
lean_dec_ref(v___y_65_);
lean_dec_ref(v_a_62_);
lean_dec(v_ref_60_);
return v_res_73_;
}
}
lean_object* l_Lean_Elab_Do_elabDoIdDecl(lean_object* v_x_74_, lean_object* v_xType_x3f_75_, lean_object* v_rhs_76_, lean_object* v_k_77_, uint8_t v_kind_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___y_88_; 
if (lean_obj_tag(v_xType_x3f_75_) == 0)
{
uint8_t v___x_99_; lean_object* v___x_100_; 
v___x_99_ = 0;
v___x_100_ = l_Lean_mkHole(v_x_74_, v___x_99_);
v___y_88_ = v___x_100_;
goto v___jp_87_;
}
else
{
lean_object* v_val_101_; 
v_val_101_ = lean_ctor_get(v_xType_x3f_75_, 0);
lean_inc(v_val_101_);
lean_dec_ref_known(v_xType_x3f_75_, 1);
v___y_88_ = v_val_101_;
goto v___jp_87_;
}
v___jp_87_:
{
lean_object* v___x_89_; 
v___x_89_ = l_Lean_Elab_Term_elabType(v___y_88_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
if (lean_obj_tag(v___x_89_) == 0)
{
lean_object* v_a_90_; lean_object* v_lctx_91_; lean_object* v_ref_92_; lean_object* v___x_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; 
v_a_90_ = lean_ctor_get(v___x_89_, 0);
lean_inc(v_a_90_);
lean_dec_ref_known(v___x_89_, 1);
v_lctx_91_ = lean_ctor_get(v_a_82_, 2);
v_ref_92_ = lean_ctor_get(v_a_84_, 2);
v___x_93_ = l_Lean_TSyntax_getId(v_x_74_);
lean_inc_n(v___x_93_, 2);
v___f_94_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIdDecl___lam__0___boxed), 11, 3);
lean_closure_set(v___f_94_, 0, v___x_93_);
lean_closure_set(v___f_94_, 1, v_x_74_);
lean_closure_set(v___f_94_, 2, v_k_77_);
lean_inc_ref(v_a_79_);
lean_inc_ref(v_lctx_91_);
lean_inc(v_ref_92_);
v___f_95_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIdDecl___lam__1___boxed), 13, 5);
lean_closure_set(v___f_95_, 0, v_ref_92_);
lean_closure_set(v___f_95_, 1, v_lctx_91_);
lean_closure_set(v___f_95_, 2, v_a_79_);
lean_closure_set(v___f_95_, 3, v___x_93_);
lean_closure_set(v___f_95_, 4, v___f_94_);
v___x_96_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_96_, 0, v___x_93_);
lean_ctor_set(v___x_96_, 1, v_a_90_);
lean_ctor_set(v___x_96_, 2, v___f_95_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*3, v_kind_78_);
v___x_97_ = 1;
v___x_98_ = l_Lean_Elab_Do_elabDoElem(v_rhs_76_, v___x_96_, v___x_97_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
return v___x_98_;
}
else
{
lean_dec_ref(v_k_77_);
lean_dec(v_rhs_76_);
lean_dec(v_x_74_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Do_elabDoIdDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_74_ = stack[0].m_obj;
lean_object* v_xType_x3f_75_ = stack[1].m_obj;
lean_object* v_rhs_76_ = stack[2].m_obj;
lean_object* v_k_77_ = stack[3].m_obj;
uint8_t v_kind_78_ = stack[4].m_num;
lean_object* v_a_79_ = stack[5].m_obj;
lean_object* v_a_80_ = stack[6].m_obj;
lean_object* v_a_81_ = stack[7].m_obj;
lean_object* v_a_82_ = stack[8].m_obj;
lean_object* v_a_83_ = stack[9].m_obj;
lean_object* v_a_84_ = stack[10].m_obj;
lean_object* v_a_85_ = stack[11].m_obj;
lean_object* v_res_102_;
v_res_102_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_74_, v_xType_x3f_75_, v_rhs_76_, v_k_77_, v_kind_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___boxed(lean_object* v_x_103_, lean_object* v_xType_x3f_104_, lean_object* v_rhs_105_, lean_object* v_k_106_, lean_object* v_kind_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
uint8_t v_kind_boxed_116_; lean_object* v_res_117_; 
v_kind_boxed_116_ = lean_unbox(v_kind_107_);
v_res_117_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_103_, v_xType_x3f_104_, v_rhs_105_, v_k_106_, v_kind_boxed_116_, v_a_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_);
lean_dec(v_a_114_);
lean_dec_ref(v_a_113_);
lean_dec(v_a_112_);
lean_dec_ref(v_a_111_);
lean_dec(v_a_110_);
lean_dec_ref(v_a_109_);
lean_dec_ref(v_a_108_);
return v_res_117_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Do_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Do_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_BuiltinDo_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_BuiltinDo_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
