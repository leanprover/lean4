// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util
// Imports: public import Lean.Meta.Tactic.Simp.Simproc
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
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__6;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_false_of_decide"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(171, 157, 112, 124, 91, 52, 64, 56)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__9;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__12;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__15;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_true_of_decide"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(10, 132, 193, 70, 136, 209, 66, 149)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_box(0);
v___x_7_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__2));
v___x_8_ = l_Lean_mkConst(v___x_7_, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_box(0);
v___x_13_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__5));
v___x_14_ = l_Lean_mkConst(v___x_13_, v___x_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__9(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_box(0);
v___x_19_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__8));
v___x_20_ = l_Lean_mkConst(v___x_19_, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__12(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_box(0);
v___x_26_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__11));
v___x_27_ = l_Lean_mkConst(v___x_26_, v___x_25_);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__14));
v___x_33_ = l_Lean_mkConst(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__18(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_box(0);
v___x_38_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__17));
v___x_39_ = l_Lean_mkConst(v___x_38_, v___x_37_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object* v_p_40_, uint8_t v_result_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___x_47_; 
lean_inc(v_a_45_);
lean_inc_ref(v_a_44_);
lean_inc(v_a_43_);
lean_inc_ref(v_a_42_);
lean_inc_ref(v_p_40_);
v___x_47_ = l_Lean_Meta_mkDecide(v_p_40_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; uint8_t v___x_49_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
lean_dec_ref(v___x_47_);
v___x_49_ = 1;
if (v_result_41_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__3, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__3_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__3);
v___x_51_ = l_Lean_Meta_mkEqRefl(v___x_50_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_71_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_71_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_71_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_71_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_56_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__6, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6);
v___x_57_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__9, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__9_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__9);
v___x_58_ = l_Lean_Expr_appArg_x21(v_a_48_);
lean_dec(v_a_48_);
v___x_59_ = lean_unsigned_to_nat(3u);
v___x_60_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_61_ = lean_array_push(v___x_60_, v_p_40_);
v___x_62_ = lean_array_push(v___x_61_, v___x_58_);
v___x_63_ = lean_array_push(v___x_62_, v_a_52_);
v___x_64_ = l_Lean_mkAppN(v___x_57_, v___x_63_);
lean_dec_ref(v___x_63_);
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
v___x_66_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_66_, 0, v___x_56_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
lean_ctor_set_uint8(v___x_66_, sizeof(void*)*2, v___x_49_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_67_);
v___x_69_ = v___x_54_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
else
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
lean_dec(v_a_48_);
lean_dec_ref(v_p_40_);
v_a_72_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v___x_51_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_51_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__12, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__12_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__12);
v___x_81_ = l_Lean_Meta_mkEqRefl(v___x_80_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_101_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_101_ == 0)
{
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_101_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_101_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_86_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__15, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15);
v___x_87_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__18, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__18_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__18);
v___x_88_ = l_Lean_Expr_appArg_x21(v_a_48_);
lean_dec(v_a_48_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_mk_empty_array_with_capacity(v___x_89_);
v___x_91_ = lean_array_push(v___x_90_, v_p_40_);
v___x_92_ = lean_array_push(v___x_91_, v___x_88_);
v___x_93_ = lean_array_push(v___x_92_, v_a_82_);
v___x_94_ = l_Lean_mkAppN(v___x_87_, v___x_93_);
lean_dec_ref(v___x_93_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_96_, 0, v___x_86_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*2, v___x_49_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_97_);
v___x_99_ = v___x_84_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec(v_a_48_);
lean_dec_ref(v_p_40_);
v_a_102_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_81_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_81_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
lean_dec(v_a_43_);
lean_dec_ref(v_a_42_);
lean_dec_ref(v_p_40_);
v_a_110_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_47_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_47_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___boxed(lean_object* v_p_118_, lean_object* v_result_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
uint8_t v_result_boxed_125_; lean_object* v_res_126_; 
v_result_boxed_125_ = lean_unbox(v_result_119_);
v_res_126_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_p_118_, v_result_boxed_125_, v_a_120_, v_a_121_, v_a_122_, v_a_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep(lean_object* v_p_127_, uint8_t v_result_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_p_127_, v_result_128_, v_a_132_, v_a_133_, v_a_134_, v_a_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___boxed(lean_object* v_p_138_, lean_object* v_result_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
uint8_t v_result_boxed_148_; lean_object* v_res_149_; 
v_result_boxed_148_ = lean_unbox(v_result_139_);
v_res_149_ = l_Lean_Meta_Simp_evalPropStep(v_p_138_, v_result_boxed_148_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v_a_142_);
lean_dec_ref(v_a_141_);
lean_dec(v_a_140_);
return v_res_149_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
}
#ifdef __cplusplus
}
#endif
