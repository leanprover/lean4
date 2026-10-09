// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.DSimproc
// Imports: public import Lean.Meta.Sym.DSimp.Result
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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_andThen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_andThen___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_orElse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0___boxed, .m_arity = 13, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_andThen(lean_object* v_f_1_, lean_object* v_g_2_, lean_object* v_e_u2081_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_e_u2081_3_);
v___x_14_ = lean_apply_11(v_f_1_, v_e_u2081_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
lean_inc(v_a_15_);
if (lean_obj_tag(v_a_15_) == 0)
{
uint8_t v_done_16_; 
v_done_16_ = lean_ctor_get_uint8(v_a_15_, 0);
lean_dec_ref_known(v_a_15_, 0);
if (v_done_16_ == 0)
{
lean_object* v___x_17_; 
lean_dec_ref_known(v___x_14_, 1);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
v___x_17_ = lean_apply_11(v_g_2_, v_e_u2081_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
return v___x_17_;
}
else
{
lean_dec_ref(v_e_u2081_3_);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
else
{
uint8_t v_done_18_; 
lean_dec_ref(v_e_u2081_3_);
v_done_18_ = lean_ctor_get_uint8(v_a_15_, sizeof(void*)*1);
if (v_done_18_ == 0)
{
lean_object* v_e_x27_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_37_; 
lean_dec_ref_known(v___x_14_, 1);
v_e_x27_19_ = lean_ctor_get(v_a_15_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v_a_15_);
if (v_isSharedCheck_37_ == 0)
{
v___x_21_ = v_a_15_;
v_isShared_22_ = v_isSharedCheck_37_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_e_x27_19_);
lean_dec(v_a_15_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_37_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_23_; 
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
lean_inc(v_a_10_);
lean_inc_ref(v_a_9_);
lean_inc(v_a_8_);
lean_inc_ref(v_a_7_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_e_x27_19_);
v___x_23_ = lean_apply_11(v_g_2_, v_e_x27_19_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, lean_box(0));
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v_a_24_; 
v_a_24_ = lean_ctor_get(v___x_23_, 0);
lean_inc(v_a_24_);
if (lean_obj_tag(v_a_24_) == 0)
{
lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_35_; 
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_35_ == 0)
{
lean_object* v_unused_36_; 
v_unused_36_ = lean_ctor_get(v___x_23_, 0);
lean_dec(v_unused_36_);
v___x_26_ = v___x_23_;
v_isShared_27_ = v_isSharedCheck_35_;
goto v_resetjp_25_;
}
else
{
lean_dec(v___x_23_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_35_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
uint8_t v_done_28_; lean_object* v___x_30_; 
v_done_28_ = lean_ctor_get_uint8(v_a_24_, 0);
lean_dec_ref_known(v_a_24_, 0);
if (v_isShared_22_ == 0)
{
v___x_30_ = v___x_21_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_e_x27_19_);
v___x_30_ = v_reuseFailAlloc_34_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
lean_object* v___x_32_; 
lean_ctor_set_uint8(v___x_30_, sizeof(void*)*1, v_done_28_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 0, v___x_30_);
v___x_32_ = v___x_26_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_24_, 1);
lean_del_object(v___x_21_);
lean_dec_ref(v_e_x27_19_);
return v___x_23_;
}
}
else
{
lean_del_object(v___x_21_);
lean_dec_ref(v_e_x27_19_);
return v___x_23_;
}
}
}
else
{
lean_dec_ref_known(v_a_15_, 1);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
}
else
{
lean_dec_ref(v_e_u2081_3_);
lean_dec_ref(v_g_2_);
return v___x_14_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_DSimproc_andThen_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1_ = stack[0].m_obj;
lean_object* v_g_2_ = stack[1].m_obj;
lean_object* v_e_u2081_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_a_8_ = stack[7].m_obj;
lean_object* v_a_9_ = stack[8].m_obj;
lean_object* v_a_10_ = stack[9].m_obj;
lean_object* v_a_11_ = stack[10].m_obj;
lean_object* v_a_12_ = stack[11].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_Meta_Sym_DSimp_DSimproc_andThen(v_f_1_, v_g_2_, v_e_u2081_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_andThen___boxed(lean_object* v_f_39_, lean_object* v_g_40_, lean_object* v_e_u2081_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Meta_Sym_DSimp_DSimproc_andThen(v_f_39_, v_g_40_, v_e_u2081_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_, v_a_50_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
lean_dec(v_a_48_);
lean_dec_ref(v_a_47_);
lean_dec(v_a_46_);
lean_dec_ref(v_a_45_);
lean_dec(v_a_44_);
lean_dec_ref(v_a_43_);
lean_dec(v_a_42_);
return v_res_52_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0(lean_object* v_f_53_, lean_object* v_g_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_box(0);
lean_inc(v___y_64_);
lean_inc_ref(v___y_63_);
lean_inc(v___y_62_);
lean_inc_ref(v___y_61_);
lean_inc(v___y_60_);
lean_inc_ref(v___y_59_);
lean_inc(v___y_58_);
lean_inc_ref(v___y_57_);
lean_inc(v___y_56_);
lean_inc_ref(v___y_55_);
v___x_67_ = lean_apply_11(v_f_53_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, lean_box(0));
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
if (lean_obj_tag(v_a_68_) == 0)
{
uint8_t v_done_69_; 
v_done_69_ = lean_ctor_get_uint8(v_a_68_, 0);
lean_dec_ref_known(v_a_68_, 0);
if (v_done_69_ == 0)
{
lean_object* v___x_70_; 
lean_dec_ref_known(v___x_67_, 1);
lean_inc(v___y_64_);
lean_inc_ref(v___y_63_);
lean_inc(v___y_62_);
lean_inc_ref(v___y_61_);
lean_inc(v___y_60_);
lean_inc_ref(v___y_59_);
lean_inc(v___y_58_);
lean_inc_ref(v___y_57_);
lean_inc(v___y_56_);
v___x_70_ = lean_apply_12(v_g_54_, v___x_66_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, lean_box(0));
return v___x_70_;
}
else
{
lean_dec_ref(v___y_55_);
lean_dec_ref(v_g_54_);
return v___x_67_;
}
}
else
{
uint8_t v_done_71_; 
lean_dec_ref(v___y_55_);
v_done_71_ = lean_ctor_get_uint8(v_a_68_, sizeof(void*)*1);
if (v_done_71_ == 0)
{
lean_object* v_e_x27_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_90_; 
lean_dec_ref_known(v___x_67_, 1);
v_e_x27_72_ = lean_ctor_get(v_a_68_, 0);
v_isSharedCheck_90_ = !lean_is_exclusive(v_a_68_);
if (v_isSharedCheck_90_ == 0)
{
v___x_74_ = v_a_68_;
v_isShared_75_ = v_isSharedCheck_90_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_e_x27_72_);
lean_dec(v_a_68_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_90_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; 
lean_inc(v___y_64_);
lean_inc_ref(v___y_63_);
lean_inc(v___y_62_);
lean_inc_ref(v___y_61_);
lean_inc(v___y_60_);
lean_inc_ref(v___y_59_);
lean_inc(v___y_58_);
lean_inc_ref(v___y_57_);
lean_inc(v___y_56_);
lean_inc_ref(v_e_x27_72_);
v___x_76_ = lean_apply_12(v_g_54_, v___x_66_, v_e_x27_72_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, lean_box(0));
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
if (lean_obj_tag(v_a_77_) == 0)
{
lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_88_; 
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_88_ == 0)
{
lean_object* v_unused_89_; 
v_unused_89_ = lean_ctor_get(v___x_76_, 0);
lean_dec(v_unused_89_);
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_88_;
goto v_resetjp_78_;
}
else
{
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_88_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
uint8_t v_done_81_; lean_object* v___x_83_; 
v_done_81_ = lean_ctor_get_uint8(v_a_77_, 0);
lean_dec_ref_known(v_a_77_, 0);
if (v_isShared_75_ == 0)
{
v___x_83_ = v___x_74_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_e_x27_72_);
v___x_83_ = v_reuseFailAlloc_87_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
lean_object* v___x_85_; 
lean_ctor_set_uint8(v___x_83_, sizeof(void*)*1, v_done_81_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_83_);
v___x_85_ = v___x_79_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v___x_83_);
v___x_85_ = v_reuseFailAlloc_86_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
return v___x_85_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_77_, 1);
lean_del_object(v___x_74_);
lean_dec_ref(v_e_x27_72_);
return v___x_76_;
}
}
else
{
lean_del_object(v___x_74_);
lean_dec_ref(v_e_x27_72_);
return v___x_76_;
}
}
}
else
{
lean_dec_ref_known(v_a_68_, 1);
lean_dec_ref(v_g_54_);
return v___x_67_;
}
}
}
else
{
lean_dec_ref(v___y_55_);
lean_dec_ref(v_g_54_);
return v___x_67_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_53_ = stack[0].m_obj;
lean_object* v_g_54_ = stack[1].m_obj;
lean_object* v___y_55_ = stack[2].m_obj;
lean_object* v___y_56_ = stack[3].m_obj;
lean_object* v___y_57_ = stack[4].m_obj;
lean_object* v___y_58_ = stack[5].m_obj;
lean_object* v___y_59_ = stack[6].m_obj;
lean_object* v___y_60_ = stack[7].m_obj;
lean_object* v___y_61_ = stack[8].m_obj;
lean_object* v___y_62_ = stack[9].m_obj;
lean_object* v___y_63_ = stack[10].m_obj;
lean_object* v___y_64_ = stack[11].m_obj;
lean_object* v_res_91_;
v_res_91_ = l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0(v_f_53_, v_g_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_);
stack->m_obj
 = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0___boxed(lean_object* v_f_92_, lean_object* v_g_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0(v_f_92_, v_g_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, v___y_101_, v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec(v___y_99_);
lean_dec_ref(v___y_98_);
lean_dec(v___y_97_);
lean_dec_ref(v___y_96_);
lean_dec(v___y_95_);
return v_res_105_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_orElse(lean_object* v_f_108_, lean_object* v_g_109_, lean_object* v_e_u2081_110_, lean_object* v_a_111_, lean_object* v_a_112_, lean_object* v_a_113_, lean_object* v_a_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v___x_121_; 
lean_inc(v_a_119_);
lean_inc_ref(v_a_118_);
lean_inc(v_a_117_);
lean_inc_ref(v_a_116_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
lean_inc(v_a_111_);
lean_inc_ref(v_e_u2081_110_);
v___x_121_ = lean_apply_11(v_f_108_, v_e_u2081_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, lean_box(0));
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
if (lean_obj_tag(v_a_122_) == 0)
{
uint8_t v_done_123_; 
v_done_123_ = lean_ctor_get_uint8(v_a_122_, 0);
lean_dec_ref_known(v_a_122_, 0);
if (v_done_123_ == 0)
{
lean_object* v___x_124_; 
lean_dec_ref_known(v___x_121_, 1);
lean_inc(v_a_119_);
lean_inc_ref(v_a_118_);
lean_inc(v_a_117_);
lean_inc_ref(v_a_116_);
lean_inc(v_a_115_);
lean_inc_ref(v_a_114_);
lean_inc(v_a_113_);
lean_inc_ref(v_a_112_);
lean_inc(v_a_111_);
v___x_124_ = lean_apply_11(v_g_109_, v_e_u2081_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_, lean_box(0));
return v___x_124_;
}
else
{
lean_dec_ref(v_e_u2081_110_);
lean_dec_ref(v_g_109_);
return v___x_121_;
}
}
else
{
lean_dec_ref_known(v_a_122_, 1);
lean_dec_ref(v_e_u2081_110_);
lean_dec_ref(v_g_109_);
return v___x_121_;
}
}
else
{
lean_dec_ref(v_e_u2081_110_);
lean_dec_ref(v_g_109_);
return v___x_121_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_DSimproc_orElse_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_108_ = stack[0].m_obj;
lean_object* v_g_109_ = stack[1].m_obj;
lean_object* v_e_u2081_110_ = stack[2].m_obj;
lean_object* v_a_111_ = stack[3].m_obj;
lean_object* v_a_112_ = stack[4].m_obj;
lean_object* v_a_113_ = stack[5].m_obj;
lean_object* v_a_114_ = stack[6].m_obj;
lean_object* v_a_115_ = stack[7].m_obj;
lean_object* v_a_116_ = stack[8].m_obj;
lean_object* v_a_117_ = stack[9].m_obj;
lean_object* v_a_118_ = stack[10].m_obj;
lean_object* v_a_119_ = stack[11].m_obj;
lean_object* v_res_125_;
v_res_125_ = l_Lean_Meta_Sym_DSimp_DSimproc_orElse(v_f_108_, v_g_109_, v_e_u2081_110_, v_a_111_, v_a_112_, v_a_113_, v_a_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_, v_a_119_);
stack->m_obj
 = v_res_125_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_orElse___boxed(lean_object* v_f_126_, lean_object* v_g_127_, lean_object* v_e_u2081_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Meta_Sym_DSimp_DSimproc_orElse(v_f_126_, v_g_127_, v_e_u2081_128_, v_a_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_, v_a_137_);
lean_dec(v_a_137_);
lean_dec_ref(v_a_136_);
lean_dec(v_a_135_);
lean_dec_ref(v_a_134_);
lean_dec(v_a_133_);
lean_dec_ref(v_a_132_);
lean_dec(v_a_131_);
lean_dec_ref(v_a_130_);
lean_dec(v_a_129_);
return v_res_139_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0(lean_object* v_f_140_, lean_object* v_g_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_box(0);
lean_inc(v___y_151_);
lean_inc_ref(v___y_150_);
lean_inc(v___y_149_);
lean_inc_ref(v___y_148_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
lean_inc(v___y_143_);
lean_inc_ref(v___y_142_);
v___x_154_ = lean_apply_11(v_f_140_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, lean_box(0));
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
if (lean_obj_tag(v_a_155_) == 0)
{
uint8_t v_done_156_; 
v_done_156_ = lean_ctor_get_uint8(v_a_155_, 0);
lean_dec_ref_known(v_a_155_, 0);
if (v_done_156_ == 0)
{
lean_object* v___x_157_; 
lean_dec_ref_known(v___x_154_, 1);
lean_inc(v___y_151_);
lean_inc_ref(v___y_150_);
lean_inc(v___y_149_);
lean_inc_ref(v___y_148_);
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
lean_inc(v___y_143_);
v___x_157_ = lean_apply_12(v_g_141_, v___x_153_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, lean_box(0));
return v___x_157_;
}
else
{
lean_dec_ref(v___y_142_);
lean_dec_ref(v_g_141_);
return v___x_154_;
}
}
else
{
lean_dec_ref_known(v_a_155_, 1);
lean_dec_ref(v___y_142_);
lean_dec_ref(v_g_141_);
return v___x_154_;
}
}
else
{
lean_dec_ref(v___y_142_);
lean_dec_ref(v_g_141_);
return v___x_154_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_140_ = stack[0].m_obj;
lean_object* v_g_141_ = stack[1].m_obj;
lean_object* v___y_142_ = stack[2].m_obj;
lean_object* v___y_143_ = stack[3].m_obj;
lean_object* v___y_144_ = stack[4].m_obj;
lean_object* v___y_145_ = stack[5].m_obj;
lean_object* v___y_146_ = stack[6].m_obj;
lean_object* v___y_147_ = stack[7].m_obj;
lean_object* v___y_148_ = stack[8].m_obj;
lean_object* v___y_149_ = stack[9].m_obj;
lean_object* v___y_150_ = stack[10].m_obj;
lean_object* v___y_151_ = stack[11].m_obj;
lean_object* v_res_158_;
v_res_158_ = l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0(v_f_140_, v_g_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0___boxed(lean_object* v_f_159_, lean_object* v_g_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0(v_f_159_, v_g_160_, v___y_161_, v___y_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
lean_dec(v___y_164_);
lean_dec_ref(v___y_163_);
lean_dec(v___y_162_);
return v_res_172_;
}
}
lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch(lean_object* v_f_175_, lean_object* v_e_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_187_; 
lean_inc(v_a_185_);
lean_inc_ref(v_a_184_);
lean_inc(v_a_183_);
lean_inc_ref(v_a_182_);
lean_inc(v_a_181_);
lean_inc_ref(v_a_180_);
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
lean_inc(v_a_177_);
v___x_187_ = lean_apply_11(v_f_175_, v_e_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, lean_box(0));
if (lean_obj_tag(v___x_187_) == 0)
{
return v___x_187_;
}
else
{
lean_object* v_a_188_; uint8_t v___y_190_; uint8_t v___x_200_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
v___x_200_ = l_Lean_Exception_isInterrupt(v_a_188_);
if (v___x_200_ == 0)
{
uint8_t v___x_201_; 
v___x_201_ = l_Lean_Exception_isRuntime(v_a_188_);
v___y_190_ = v___x_201_;
goto v___jp_189_;
}
else
{
lean_dec(v_a_188_);
v___y_190_ = v___x_200_;
goto v___jp_189_;
}
v___jp_189_:
{
if (v___y_190_ == 0)
{
lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_198_; 
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_198_ == 0)
{
lean_object* v_unused_199_; 
v_unused_199_ = lean_ctor_get(v___x_187_, 0);
lean_dec(v_unused_199_);
v___x_192_ = v___x_187_;
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
else
{
lean_dec(v___x_187_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_198_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_194_, 0, v___y_190_);
if (v_isShared_193_ == 0)
{
lean_ctor_set_tag(v___x_192_, 0);
lean_ctor_set(v___x_192_, 0, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
else
{
return v___x_187_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_175_ = stack[0].m_obj;
lean_object* v_e_176_ = stack[1].m_obj;
lean_object* v_a_177_ = stack[2].m_obj;
lean_object* v_a_178_ = stack[3].m_obj;
lean_object* v_a_179_ = stack[4].m_obj;
lean_object* v_a_180_ = stack[5].m_obj;
lean_object* v_a_181_ = stack[6].m_obj;
lean_object* v_a_182_ = stack[7].m_obj;
lean_object* v_a_183_ = stack[8].m_obj;
lean_object* v_a_184_ = stack[9].m_obj;
lean_object* v_a_185_ = stack[10].m_obj;
lean_object* v_res_202_;
v_res_202_ = l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch(v_f_175_, v_e_176_, v_a_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch___boxed(lean_object* v_f_203_, lean_object* v_e_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch(v_f_203_, v_e_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_);
lean_dec(v_a_213_);
lean_dec_ref(v_a_212_);
lean_dec(v_a_211_);
lean_dec_ref(v_a_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_a_208_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
return v_res_215_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_Result(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_DSimproc(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_Result(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
}
#ifdef __cplusplus
}
#endif
