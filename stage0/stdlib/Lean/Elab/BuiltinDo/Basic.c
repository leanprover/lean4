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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__0(lean_object* v___x_1_, lean_object* v_x_2_, lean_object* v_k_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_, lean_object* v___y_10_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__0___boxed(lean_object* v___x_24_, lean_object* v_x_25_, lean_object* v_k_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Elab_Do_elabDoIdDecl___lam__0(v___x_24_, v_x_25_, v_k_26_, v___y_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_, v___y_33_);
lean_dec(v___y_33_);
lean_dec_ref(v___y_32_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
lean_dec_ref(v___y_27_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__1(lean_object* v_ref_36_, lean_object* v_lctx_37_, lean_object* v_a_38_, lean_object* v___x_39_, lean_object* v___f_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_){
_start:
{
lean_object* v_toCold_49_; lean_object* v_options_50_; lean_object* v_currRecDepth_51_; lean_object* v_maxRecDepth_52_; lean_object* v_ref_53_; lean_object* v_currNamespace_54_; lean_object* v_openDecls_55_; lean_object* v_initHeartbeats_56_; lean_object* v_maxHeartbeats_57_; lean_object* v_currMacroScope_58_; uint8_t v_diag_59_; uint8_t v_suppressElabErrors_60_; lean_object* v_ref_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v_toCold_49_ = lean_ctor_get(v___y_46_, 0);
v_options_50_ = lean_ctor_get(v___y_46_, 1);
v_currRecDepth_51_ = lean_ctor_get(v___y_46_, 2);
v_maxRecDepth_52_ = lean_ctor_get(v___y_46_, 3);
v_ref_53_ = lean_ctor_get(v___y_46_, 4);
v_currNamespace_54_ = lean_ctor_get(v___y_46_, 5);
v_openDecls_55_ = lean_ctor_get(v___y_46_, 6);
v_initHeartbeats_56_ = lean_ctor_get(v___y_46_, 7);
v_maxHeartbeats_57_ = lean_ctor_get(v___y_46_, 8);
v_currMacroScope_58_ = lean_ctor_get(v___y_46_, 9);
v_diag_59_ = lean_ctor_get_uint8(v___y_46_, sizeof(void*)*10);
v_suppressElabErrors_60_ = lean_ctor_get_uint8(v___y_46_, sizeof(void*)*10 + 1);
v_ref_61_ = l_Lean_replaceRef(v_ref_36_, v_ref_53_);
lean_inc(v_currMacroScope_58_);
lean_inc(v_maxHeartbeats_57_);
lean_inc(v_initHeartbeats_56_);
lean_inc(v_openDecls_55_);
lean_inc(v_currNamespace_54_);
lean_inc(v_maxRecDepth_52_);
lean_inc(v_currRecDepth_51_);
lean_inc_ref(v_options_50_);
lean_inc_ref(v_toCold_49_);
v___x_62_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_62_, 0, v_toCold_49_);
lean_ctor_set(v___x_62_, 1, v_options_50_);
lean_ctor_set(v___x_62_, 2, v_currRecDepth_51_);
lean_ctor_set(v___x_62_, 3, v_maxRecDepth_52_);
lean_ctor_set(v___x_62_, 4, v_ref_61_);
lean_ctor_set(v___x_62_, 5, v_currNamespace_54_);
lean_ctor_set(v___x_62_, 6, v_openDecls_55_);
lean_ctor_set(v___x_62_, 7, v_initHeartbeats_56_);
lean_ctor_set(v___x_62_, 8, v_maxHeartbeats_57_);
lean_ctor_set(v___x_62_, 9, v_currMacroScope_58_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*10, v_diag_59_);
lean_ctor_set_uint8(v___x_62_, sizeof(void*)*10 + 1, v_suppressElabErrors_60_);
lean_inc_ref(v_a_38_);
v___x_63_ = l_Lean_Elab_Do_withLCtxKeepingMutVarDefs___redArg(v_lctx_37_, v_a_38_, v___x_39_, v___f_40_, v___y_41_, v___y_42_, v___y_43_, v___y_44_, v___y_45_, v___x_62_, v___y_47_);
lean_dec_ref_known(v___x_62_, 10);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__1___boxed(lean_object* v_ref_64_, lean_object* v_lctx_65_, lean_object* v_a_66_, lean_object* v___x_67_, lean_object* v___f_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Elab_Do_elabDoIdDecl___lam__1(v_ref_64_, v_lctx_65_, v_a_66_, v___x_67_, v___f_68_, v___y_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
lean_dec(v___y_71_);
lean_dec_ref(v___y_70_);
lean_dec_ref(v___y_69_);
lean_dec_ref(v_a_66_);
lean_dec(v_ref_64_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl(lean_object* v_x_78_, lean_object* v_xType_x3f_79_, lean_object* v_rhs_80_, lean_object* v_k_81_, uint8_t v_kind_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___y_92_; 
if (lean_obj_tag(v_xType_x3f_79_) == 0)
{
uint8_t v___x_103_; lean_object* v___x_104_; 
v___x_103_ = 0;
v___x_104_ = l_Lean_mkHole(v_x_78_, v___x_103_);
v___y_92_ = v___x_104_;
goto v___jp_91_;
}
else
{
lean_object* v_val_105_; 
v_val_105_ = lean_ctor_get(v_xType_x3f_79_, 0);
lean_inc(v_val_105_);
lean_dec_ref_known(v_xType_x3f_79_, 1);
v___y_92_ = v_val_105_;
goto v___jp_91_;
}
v___jp_91_:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Elab_Term_elabType(v___y_92_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v_lctx_95_; lean_object* v_ref_96_; lean_object* v___x_97_; lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref_known(v___x_93_, 1);
v_lctx_95_ = lean_ctor_get(v_a_86_, 2);
v_ref_96_ = lean_ctor_get(v_a_88_, 4);
v___x_97_ = l_Lean_TSyntax_getId(v_x_78_);
lean_inc_n(v___x_97_, 2);
v___f_98_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIdDecl___lam__0___boxed), 11, 3);
lean_closure_set(v___f_98_, 0, v___x_97_);
lean_closure_set(v___f_98_, 1, v_x_78_);
lean_closure_set(v___f_98_, 2, v_k_81_);
lean_inc_ref(v_a_83_);
lean_inc_ref(v_lctx_95_);
lean_inc(v_ref_96_);
v___f_99_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIdDecl___lam__1___boxed), 13, 5);
lean_closure_set(v___f_99_, 0, v_ref_96_);
lean_closure_set(v___f_99_, 1, v_lctx_95_);
lean_closure_set(v___f_99_, 2, v_a_83_);
lean_closure_set(v___f_99_, 3, v___x_97_);
lean_closure_set(v___f_99_, 4, v___f_98_);
v___x_100_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_100_, 0, v___x_97_);
lean_ctor_set(v___x_100_, 1, v_a_94_);
lean_ctor_set(v___x_100_, 2, v___f_99_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*3, v_kind_82_);
v___x_101_ = 1;
v___x_102_ = l_Lean_Elab_Do_elabDoElem(v_rhs_80_, v___x_100_, v___x_101_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_);
return v___x_102_;
}
else
{
lean_dec_ref(v_k_81_);
lean_dec(v_rhs_80_);
lean_dec(v_x_78_);
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___boxed(lean_object* v_x_106_, lean_object* v_xType_x3f_107_, lean_object* v_rhs_108_, lean_object* v_k_109_, lean_object* v_kind_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
uint8_t v_kind_boxed_119_; lean_object* v_res_120_; 
v_kind_boxed_119_ = lean_unbox(v_kind_110_);
v_res_120_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_106_, v_xType_x3f_107_, v_rhs_108_, v_k_109_, v_kind_boxed_119_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_);
lean_dec(v_a_117_);
lean_dec_ref(v_a_116_);
lean_dec(v_a_115_);
lean_dec_ref(v_a_114_);
lean_dec(v_a_113_);
lean_dec_ref(v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_120_;
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
