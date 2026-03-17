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
lean_object* l_Lean_Elab_Do_withLCtxKeepingMutVarDefs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_elabDoElem(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_12_);
lean_inc(v___y_10_);
lean_inc_ref(v___y_9_);
lean_inc(v___y_8_);
lean_inc_ref(v___y_7_);
lean_inc(v___y_6_);
lean_inc_ref(v___y_5_);
v___x_14_ = l_Lean_Elab_Term_addLocalVarInfo(v_x_2_, v_a_13_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v___x_15_; 
lean_dec_ref(v___x_14_);
v___x_15_ = lean_apply_8(v_k_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, v___y_10_, lean_box(0));
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_23_; 
lean_dec(v___y_10_);
lean_dec_ref(v___y_9_);
lean_dec(v___y_8_);
lean_dec_ref(v___y_7_);
lean_dec(v___y_6_);
lean_dec_ref(v___y_5_);
lean_dec_ref(v___y_4_);
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
lean_dec(v___y_10_);
lean_dec_ref(v___y_9_);
lean_dec(v___y_8_);
lean_dec_ref(v___y_7_);
lean_dec(v___y_6_);
lean_dec_ref(v___y_5_);
lean_dec_ref(v___y_4_);
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
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl(lean_object* v_x_36_, lean_object* v_xType_x3f_37_, lean_object* v_rhs_38_, lean_object* v_k_39_, uint8_t v_kind_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___y_50_; 
if (lean_obj_tag(v_xType_x3f_37_) == 0)
{
uint8_t v___x_60_; lean_object* v___x_61_; 
v___x_60_ = 0;
v___x_61_ = l_Lean_mkHole(v_x_36_, v___x_60_);
v___y_50_ = v___x_61_;
goto v___jp_49_;
}
else
{
lean_object* v_val_62_; 
v_val_62_ = lean_ctor_get(v_xType_x3f_37_, 0);
lean_inc(v_val_62_);
lean_dec_ref(v_xType_x3f_37_);
v___y_50_ = v_val_62_;
goto v___jp_49_;
}
v___jp_49_:
{
lean_object* v___x_51_; 
lean_inc(v_a_47_);
lean_inc_ref(v_a_46_);
lean_inc(v_a_45_);
lean_inc_ref(v_a_44_);
lean_inc(v_a_43_);
lean_inc_ref(v_a_42_);
v___x_51_ = l_Lean_Elab_Term_elabType(v___y_50_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v_lctx_53_; lean_object* v___x_54_; lean_object* v___f_55_; lean_object* v___x_56_; lean_object* v___x_57_; uint8_t v___x_58_; lean_object* v___x_59_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
lean_inc(v_a_52_);
lean_dec_ref(v___x_51_);
v_lctx_53_ = lean_ctor_get(v_a_44_, 2);
v___x_54_ = l_Lean_TSyntax_getId(v_x_36_);
lean_inc(v___x_54_);
v___f_55_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_elabDoIdDecl___lam__0___boxed), 11, 3);
lean_closure_set(v___f_55_, 0, v___x_54_);
lean_closure_set(v___f_55_, 1, v_x_36_);
lean_closure_set(v___f_55_, 2, v_k_39_);
lean_inc(v___x_54_);
lean_inc_ref(v_a_41_);
lean_inc_ref(v_lctx_53_);
v___x_56_ = lean_alloc_closure((void*)(l_Lean_Elab_Do_withLCtxKeepingMutVarDefs___boxed), 13, 5);
lean_closure_set(v___x_56_, 0, lean_box(0));
lean_closure_set(v___x_56_, 1, v_lctx_53_);
lean_closure_set(v___x_56_, 2, v_a_41_);
lean_closure_set(v___x_56_, 3, v___x_54_);
lean_closure_set(v___x_56_, 4, v___f_55_);
v___x_57_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_57_, 0, v___x_54_);
lean_ctor_set(v___x_57_, 1, v_a_52_);
lean_ctor_set(v___x_57_, 2, v___x_56_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*3, v_kind_40_);
v___x_58_ = 1;
v___x_59_ = l_Lean_Elab_Do_elabDoElem(v_rhs_38_, v___x_57_, v___x_58_, v_a_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_);
return v___x_59_;
}
else
{
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
lean_dec_ref(v_a_41_);
lean_dec_ref(v_k_39_);
lean_dec(v_rhs_38_);
lean_dec(v_x_36_);
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_elabDoIdDecl___boxed(lean_object* v_x_63_, lean_object* v_xType_x3f_64_, lean_object* v_rhs_65_, lean_object* v_k_66_, lean_object* v_kind_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
uint8_t v_kind_boxed_76_; lean_object* v_res_77_; 
v_kind_boxed_76_ = lean_unbox(v_kind_67_);
v_res_77_ = l_Lean_Elab_Do_elabDoIdDecl(v_x_63_, v_xType_x3f_64_, v_rhs_65_, v_k_66_, v_kind_boxed_76_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_);
return v_res_77_;
}
}
lean_object* runtime_initialize_Lean_Elab_Do_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_BuiltinDo_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
