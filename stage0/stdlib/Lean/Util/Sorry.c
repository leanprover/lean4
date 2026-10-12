// Lean compiler output
// Module: Lean.Util.Sorry
// Imports: public import Lean.Util.FindExpr public import Lean.Declaration
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_isSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "sorryAx"};
static const lean_object* l_Lean_Expr_isSorry___closed__0 = (const lean_object*)&l_Lean_Expr_isSorry___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isSorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(196, 190, 164, 146, 38, 179, 69, 72)}};
static const lean_object* l_Lean_Expr_isSorry___closed__1 = (const lean_object*)&l_Lean_Expr_isSorry___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSorry___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isSyntheticSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Expr_isSyntheticSorry___closed__0 = (const lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__0_value;
static const lean_string_object l_Lean_Expr_isSyntheticSorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Expr_isSyntheticSorry___closed__1 = (const lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__1_value;
static const lean_ctor_object l_Lean_Expr_isSyntheticSorry___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_isSyntheticSorry___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__1_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Expr_isSyntheticSorry___closed__2 = (const lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__2_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_isNonSyntheticSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Expr_isNonSyntheticSorry___closed__0 = (const lean_object*)&l_Lean_Expr_isNonSyntheticSorry___closed__0_value;
static const lean_ctor_object l_Lean_Expr_isNonSyntheticSorry___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_isSyntheticSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Expr_isNonSyntheticSorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_isNonSyntheticSorry___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_isNonSyntheticSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Expr_isNonSyntheticSorry___closed__1 = (const lean_object*)&l_Lean_Expr_isNonSyntheticSorry___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Expr_isNonSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isNonSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_hasSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hasSorry___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_hasSorry___closed__0 = (const lean_object*)&l_Lean_Expr_hasSorry___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_hasSyntheticSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isSyntheticSorry___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_hasSyntheticSorry___closed__0 = (const lean_object*)&l_Lean_Expr_hasSyntheticSorry___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_hasNonSyntheticSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isNonSyntheticSorry___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_hasNonSyntheticSorry___closed__0 = (const lean_object*)&l_Lean_Expr_hasNonSyntheticSorry___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Expr_hasNonSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasNonSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSyntheticSorry___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Declaration_hasNonSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_hasNonSyntheticSorry___boxed(lean_object*);
uint8_t l_Lean_Expr_isSorry(lean_object* v_e_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_6_ = l_Lean_Expr_isAppOf(v_e_4_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Expr_isSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_4_ = stack[0].m_obj;
uint8_t v_res_7_;
v_res_7_ = l_Lean_Expr_isSorry(v_e_4_);
stack->m_num = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSorry___boxed(lean_object* v_e_8_){
_start:
{
uint8_t v_res_9_; lean_object* v_r_10_; 
v_res_9_ = l_Lean_Expr_isSorry(v_e_8_);
lean_dec_ref(v_e_8_);
v_r_10_ = lean_box(v_res_9_);
return v_r_10_;
}
}
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object* v_e_16_){
_start:
{
uint8_t v___y_18_; lean_object* v___x_26_; uint8_t v___x_27_; 
v___x_26_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_27_ = l_Lean_Expr_isAppOf(v_e_16_, v___x_26_);
if (v___x_27_ == 0)
{
v___y_18_ = v___x_27_;
goto v___jp_17_;
}
else
{
lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(2u);
v___x_29_ = l_Lean_Expr_getAppNumArgs(v_e_16_);
v___x_30_ = lean_nat_dec_le(v___x_28_, v___x_29_);
lean_dec(v___x_29_);
v___y_18_ = v___x_30_;
goto v___jp_17_;
}
v___jp_17_:
{
if (v___y_18_ == 0)
{
return v___y_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_19_ = lean_unsigned_to_nat(1u);
v___x_20_ = l_Lean_Expr_getAppNumArgs(v_e_16_);
v___x_21_ = lean_nat_sub(v___x_20_, v___x_19_);
lean_dec(v___x_20_);
v___x_22_ = lean_nat_sub(v___x_21_, v___x_19_);
lean_dec(v___x_21_);
v___x_23_ = l_Lean_Expr_getRevArg_x21(v_e_16_, v___x_22_);
v___x_24_ = ((lean_object*)(l_Lean_Expr_isSyntheticSorry___closed__2));
v___x_25_ = l_Lean_Expr_isConstOf(v___x_23_, v___x_24_);
lean_dec_ref(v___x_23_);
return v___x_25_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_isSyntheticSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_16_ = stack[0].m_obj;
uint8_t v_res_31_;
v_res_31_ = l_Lean_Expr_isSyntheticSorry(v_e_16_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object* v_e_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = l_Lean_Expr_isSyntheticSorry(v_e_32_);
lean_dec_ref(v_e_32_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
uint8_t l_Lean_Expr_isNonSyntheticSorry(lean_object* v_e_39_){
_start:
{
uint8_t v___y_41_; lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_50_ = l_Lean_Expr_isAppOf(v_e_39_, v___x_49_);
if (v___x_50_ == 0)
{
v___y_41_ = v___x_50_;
goto v___jp_40_;
}
else
{
lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
v___x_51_ = lean_unsigned_to_nat(2u);
v___x_52_ = l_Lean_Expr_getAppNumArgs(v_e_39_);
v___x_53_ = lean_nat_dec_le(v___x_51_, v___x_52_);
lean_dec(v___x_52_);
v___y_41_ = v___x_53_;
goto v___jp_40_;
}
v___jp_40_:
{
if (v___y_41_ == 0)
{
return v___y_41_;
}
else
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = l_Lean_Expr_getAppNumArgs(v_e_39_);
v___x_44_ = lean_nat_sub(v___x_43_, v___x_42_);
lean_dec(v___x_43_);
v___x_45_ = lean_nat_sub(v___x_44_, v___x_42_);
lean_dec(v___x_44_);
v___x_46_ = l_Lean_Expr_getRevArg_x21(v_e_39_, v___x_45_);
v___x_47_ = ((lean_object*)(l_Lean_Expr_isNonSyntheticSorry___closed__1));
v___x_48_ = l_Lean_Expr_isConstOf(v___x_46_, v___x_47_);
lean_dec_ref(v___x_46_);
return v___x_48_;
}
}
}
}
LEAN_EXPORT void l_Lean_Expr_isNonSyntheticSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_39_ = stack[0].m_obj;
uint8_t v_res_54_;
v_res_54_ = l_Lean_Expr_isNonSyntheticSorry(v_e_39_);
stack->m_num = v_res_54_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_isNonSyntheticSorry___boxed(lean_object* v_e_55_){
_start:
{
uint8_t v_res_56_; lean_object* v_r_57_; 
v_res_56_ = l_Lean_Expr_isNonSyntheticSorry(v_e_55_);
lean_dec_ref(v_e_55_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
uint8_t l_Lean_Expr_hasSorry___lam__0(lean_object* v_x_58_){
_start:
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_60_ = l_Lean_Expr_isConstOf(v_x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT void l_Lean_Expr_hasSorry___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_58_ = stack[0].m_obj;
uint8_t v_res_61_;
v_res_61_ = l_Lean_Expr_hasSorry___lam__0(v_x_58_);
stack->m_num = v_res_61_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___lam__0___boxed(lean_object* v_x_62_){
_start:
{
uint8_t v_res_63_; lean_object* v_r_64_; 
v_res_63_ = l_Lean_Expr_hasSorry___lam__0(v_x_62_);
lean_dec_ref(v_x_62_);
v_r_64_ = lean_box(v_res_63_);
return v_r_64_;
}
}
uint8_t l_Lean_Expr_hasSorry(lean_object* v_e_66_){
_start:
{
lean_object* v___f_67_; lean_object* v___x_68_; 
v___f_67_ = ((lean_object*)(l_Lean_Expr_hasSorry___closed__0));
v___x_68_ = lean_find_expr(v___f_67_, v_e_66_);
if (lean_obj_tag(v___x_68_) == 0)
{
uint8_t v___x_69_; 
v___x_69_ = 0;
return v___x_69_;
}
else
{
uint8_t v___x_70_; 
lean_dec_ref_known(v___x_68_, 1);
v___x_70_ = 1;
return v___x_70_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_hasSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_66_ = stack[0].m_obj;
uint8_t v_res_71_;
v_res_71_ = l_Lean_Expr_hasSorry(v_e_66_);
stack->m_num = v_res_71_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___boxed(lean_object* v_e_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Lean_Expr_hasSorry(v_e_72_);
lean_dec_ref(v_e_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object* v_e_76_){
_start:
{
lean_object* v___f_77_; lean_object* v___x_78_; 
v___f_77_ = ((lean_object*)(l_Lean_Expr_hasSyntheticSorry___closed__0));
v___x_78_ = lean_find_expr(v___f_77_, v_e_76_);
if (lean_obj_tag(v___x_78_) == 0)
{
uint8_t v___x_79_; 
v___x_79_ = 0;
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
lean_dec_ref_known(v___x_78_, 1);
v___x_80_ = 1;
return v___x_80_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_hasSyntheticSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_76_ = stack[0].m_obj;
uint8_t v_res_81_;
v_res_81_ = l_Lean_Expr_hasSyntheticSorry(v_e_76_);
stack->m_num = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object* v_e_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Lean_Expr_hasSyntheticSorry(v_e_82_);
lean_dec_ref(v_e_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
uint8_t l_Lean_Expr_hasNonSyntheticSorry(lean_object* v_e_86_){
_start:
{
lean_object* v___f_87_; lean_object* v___x_88_; 
v___f_87_ = ((lean_object*)(l_Lean_Expr_hasNonSyntheticSorry___closed__0));
v___x_88_ = lean_find_expr(v___f_87_, v_e_86_);
if (lean_obj_tag(v___x_88_) == 0)
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
else
{
uint8_t v___x_90_; 
lean_dec_ref_known(v___x_88_, 1);
v___x_90_ = 1;
return v___x_90_;
}
}
}
LEAN_EXPORT void l_Lean_Expr_hasNonSyntheticSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_86_ = stack[0].m_obj;
uint8_t v_res_91_;
v_res_91_ = l_Lean_Expr_hasNonSyntheticSorry(v_e_86_);
stack->m_num = v_res_91_;
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasNonSyntheticSorry___boxed(lean_object* v_e_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Lean_Expr_hasNonSyntheticSorry(v_e_92_);
lean_dec_ref(v_e_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(uint8_t v_r_95_, lean_object* v_e_96_){
_start:
{
if (v_r_95_ == 0)
{
uint8_t v___x_97_; 
v___x_97_ = l_Lean_Expr_hasSorry(v_e_96_);
return v___x_97_;
}
else
{
return v_r_95_;
}
}
}
LEAN_EXPORT void l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_r_95_ = stack[0].m_num;
lean_object* v_e_96_ = stack[1].m_obj;
uint8_t v_res_98_;
v_res_98_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_r_95_, v_e_96_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0___boxed(lean_object* v_r_99_, lean_object* v_e_100_){
_start:
{
uint8_t v_r_boxed_101_; uint8_t v_res_102_; lean_object* v_r_103_; 
v_r_boxed_101_ = lean_unbox(v_r_99_);
v_res_102_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_r_boxed_101_, v_e_100_);
lean_dec_ref(v_e_100_);
v_r_103_ = lean_box(v_res_102_);
return v_r_103_;
}
}
uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(uint8_t v_x_104_, lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
return v_x_104_;
}
else
{
lean_object* v_head_106_; lean_object* v_toConstantVal_107_; lean_object* v_tail_108_; lean_object* v_value_109_; lean_object* v_type_110_; uint8_t v___x_111_; uint8_t v___x_112_; 
v_head_106_ = lean_ctor_get(v_x_105_, 0);
v_toConstantVal_107_ = lean_ctor_get(v_head_106_, 0);
v_tail_108_ = lean_ctor_get(v_x_105_, 1);
v_value_109_ = lean_ctor_get(v_head_106_, 1);
v_type_110_ = lean_ctor_get(v_toConstantVal_107_, 2);
v___x_111_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_x_104_, v_type_110_);
v___x_112_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v___x_111_, v_value_109_);
v_x_104_ = v___x_112_;
v_x_105_ = v_tail_108_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_104_ = stack[0].m_num;
lean_object* v_x_105_ = stack[1].m_obj;
uint8_t v_res_114_;
v_res_114_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_x_104_, v_x_105_);
stack->m_num = v_res_114_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1___boxed(lean_object* v_x_115_, lean_object* v_x_116_){
_start:
{
uint8_t v_x_1025__boxed_117_; uint8_t v_res_118_; lean_object* v_r_119_; 
v_x_1025__boxed_117_ = lean_unbox(v_x_115_);
v_res_118_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_x_1025__boxed_117_, v_x_116_);
lean_dec(v_x_116_);
v_r_119_ = lean_box(v_res_118_);
return v_r_119_;
}
}
uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(uint8_t v_x_120_, lean_object* v_x_121_){
_start:
{
if (lean_obj_tag(v_x_121_) == 0)
{
return v_x_120_;
}
else
{
if (v_x_120_ == 0)
{
lean_object* v_head_122_; lean_object* v_tail_123_; lean_object* v_type_124_; uint8_t v___x_125_; 
v_head_122_ = lean_ctor_get(v_x_121_, 0);
v_tail_123_ = lean_ctor_get(v_x_121_, 1);
v_type_124_ = lean_ctor_get(v_head_122_, 1);
v___x_125_ = l_Lean_Expr_hasSorry(v_type_124_);
v_x_120_ = v___x_125_;
v_x_121_ = v_tail_123_;
goto _start;
}
else
{
lean_object* v_tail_127_; 
v_tail_127_ = lean_ctor_get(v_x_121_, 1);
v_x_121_ = v_tail_127_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_120_ = stack[0].m_num;
lean_object* v_x_121_ = stack[1].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_120_, v_x_121_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1___boxed(lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
uint8_t v_x_1050__boxed_132_; uint8_t v_res_133_; lean_object* v_r_134_; 
v_x_1050__boxed_132_ = lean_unbox(v_x_130_);
v_res_133_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_1050__boxed_132_, v_x_131_);
lean_dec(v_x_131_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(uint8_t v_x_135_, lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 0)
{
return v_x_135_;
}
else
{
if (v_x_135_ == 0)
{
lean_object* v_head_137_; lean_object* v_tail_138_; lean_object* v_type_139_; uint8_t v___x_140_; uint8_t v___x_141_; 
v_head_137_ = lean_ctor_get(v_x_136_, 0);
v_tail_138_ = lean_ctor_get(v_x_136_, 1);
v_type_139_ = lean_ctor_get(v_head_137_, 1);
v___x_140_ = l_Lean_Expr_hasSorry(v_type_139_);
v___x_141_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v___x_140_, v_tail_138_);
return v___x_141_;
}
else
{
lean_object* v_tail_142_; uint8_t v___x_143_; 
v_tail_142_ = lean_ctor_get(v_x_136_, 1);
v___x_143_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_135_, v_tail_142_);
return v___x_143_;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_135_ = stack[0].m_num;
lean_object* v_x_136_ = stack[1].m_obj;
uint8_t v_res_144_;
v_res_144_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v_x_135_, v_x_136_);
stack->m_num = v_res_144_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0___boxed(lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
uint8_t v_x_1078__boxed_147_; uint8_t v_res_148_; lean_object* v_r_149_; 
v_x_1078__boxed_147_ = lean_unbox(v_x_145_);
v_res_148_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v_x_1078__boxed_147_, v_x_146_);
lean_dec(v_x_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(uint8_t v_x_150_, lean_object* v_x_151_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
return v_x_150_;
}
else
{
lean_object* v_head_152_; lean_object* v_tail_153_; lean_object* v_type_154_; lean_object* v_ctors_155_; uint8_t v___y_157_; 
v_head_152_ = lean_ctor_get(v_x_151_, 0);
v_tail_153_ = lean_ctor_get(v_x_151_, 1);
v_type_154_ = lean_ctor_get(v_head_152_, 1);
v_ctors_155_ = lean_ctor_get(v_head_152_, 2);
if (v_x_150_ == 0)
{
uint8_t v___x_160_; 
v___x_160_ = l_Lean_Expr_hasSorry(v_type_154_);
v___y_157_ = v___x_160_;
goto v___jp_156_;
}
else
{
v___y_157_ = v_x_150_;
goto v___jp_156_;
}
v___jp_156_:
{
uint8_t v___x_158_; 
v___x_158_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v___y_157_, v_ctors_155_);
v_x_150_ = v___x_158_;
v_x_151_ = v_tail_153_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_150_ = stack[0].m_num;
lean_object* v_x_151_ = stack[1].m_obj;
uint8_t v_res_161_;
v_res_161_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(v_x_150_, v_x_151_);
stack->m_num = v_res_161_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4___boxed(lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
uint8_t v_x_1106__boxed_164_; uint8_t v_res_165_; lean_object* v_r_166_; 
v_x_1106__boxed_164_ = lean_unbox(v_x_162_);
v_res_165_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(v_x_1106__boxed_164_, v_x_163_);
lean_dec(v_x_163_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(uint8_t v_x_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_168_) == 0)
{
return v_x_167_;
}
else
{
lean_object* v_head_169_; lean_object* v_tail_170_; lean_object* v_type_171_; lean_object* v_ctors_172_; uint8_t v___y_174_; 
v_head_169_ = lean_ctor_get(v_x_168_, 0);
v_tail_170_ = lean_ctor_get(v_x_168_, 1);
v_type_171_ = lean_ctor_get(v_head_169_, 1);
v_ctors_172_ = lean_ctor_get(v_head_169_, 2);
if (v_x_167_ == 0)
{
uint8_t v___x_177_; 
v___x_177_ = l_Lean_Expr_hasSorry(v_type_171_);
v___y_174_ = v___x_177_;
goto v___jp_173_;
}
else
{
v___y_174_ = v_x_167_;
goto v___jp_173_;
}
v___jp_173_:
{
uint8_t v___x_175_; uint8_t v___x_176_; 
v___x_175_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v___y_174_, v_ctors_172_);
v___x_176_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(v___x_175_, v_tail_170_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_167_ = stack[0].m_num;
lean_object* v_x_168_ = stack[1].m_obj;
uint8_t v_res_178_;
v_res_178_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_x_167_, v_x_168_);
stack->m_num = v_res_178_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2___boxed(lean_object* v_x_179_, lean_object* v_x_180_){
_start:
{
uint8_t v_x_1137__boxed_181_; uint8_t v_res_182_; lean_object* v_r_183_; 
v_x_1137__boxed_181_ = lean_unbox(v_x_179_);
v_res_182_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_x_1137__boxed_181_, v_x_180_);
lean_dec(v_x_180_);
v_r_183_ = lean_box(v_res_182_);
return v_r_183_;
}
}
uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(lean_object* v_d_184_, uint8_t v_a_185_){
_start:
{
switch(lean_obj_tag(v_d_184_))
{
case 0:
{
lean_object* v_val_186_; lean_object* v_toConstantVal_187_; lean_object* v_type_188_; uint8_t v___x_189_; 
v_val_186_ = lean_ctor_get(v_d_184_, 0);
v_toConstantVal_187_ = lean_ctor_get(v_val_186_, 0);
v_type_188_ = lean_ctor_get(v_toConstantVal_187_, 2);
v___x_189_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_a_185_, v_type_188_);
return v___x_189_;
}
case 4:
{
return v_a_185_;
}
case 5:
{
lean_object* v_defns_190_; uint8_t v___x_191_; 
v_defns_190_ = lean_ctor_get(v_d_184_, 0);
v___x_191_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_a_185_, v_defns_190_);
return v___x_191_;
}
case 6:
{
lean_object* v_types_192_; uint8_t v___x_193_; 
v_types_192_ = lean_ctor_get(v_d_184_, 2);
v___x_193_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_a_185_, v_types_192_);
return v___x_193_;
}
default: 
{
lean_object* v_val_194_; lean_object* v_toConstantVal_195_; lean_object* v_value_196_; lean_object* v_type_197_; uint8_t v___x_198_; uint8_t v___x_199_; 
v_val_194_ = lean_ctor_get(v_d_184_, 0);
v_toConstantVal_195_ = lean_ctor_get(v_val_194_, 0);
v_value_196_ = lean_ctor_get(v_val_194_, 1);
v_type_197_ = lean_ctor_get(v_toConstantVal_195_, 2);
v___x_198_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_a_185_, v_type_197_);
v___x_199_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v___x_198_, v_value_196_);
return v___x_199_;
}
}
}
}
LEAN_EXPORT void l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_184_ = stack[0].m_obj;
uint8_t v_a_185_ = stack[1].m_num;
uint8_t v_res_200_;
v_res_200_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(v_d_184_, v_a_185_);
stack->m_num = v_res_200_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___boxed(lean_object* v_d_201_, lean_object* v_a_202_){
_start:
{
uint8_t v_a_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v_a_boxed_203_ = lean_unbox(v_a_202_);
v_res_204_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(v_d_201_, v_a_boxed_203_);
lean_dec(v_d_201_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
uint8_t l_Lean_Declaration_hasSorry(lean_object* v_d_206_){
_start:
{
uint8_t v___x_207_; uint8_t v___x_208_; 
v___x_207_ = 0;
v___x_208_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(v_d_206_, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT void l_Lean_Declaration_hasSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_206_ = stack[0].m_obj;
uint8_t v_res_209_;
v_res_209_ = l_Lean_Declaration_hasSorry(v_d_206_);
stack->m_num = v_res_209_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSorry___boxed(lean_object* v_d_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Lean_Declaration_hasSorry(v_d_210_);
lean_dec(v_d_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(uint8_t v_r_213_, lean_object* v_e_214_){
_start:
{
if (v_r_213_ == 0)
{
uint8_t v___x_215_; 
v___x_215_ = l_Lean_Expr_hasSyntheticSorry(v_e_214_);
return v___x_215_;
}
else
{
return v_r_213_;
}
}
}
LEAN_EXPORT void l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_r_213_ = stack[0].m_num;
lean_object* v_e_214_ = stack[1].m_obj;
uint8_t v_res_216_;
v_res_216_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_r_213_, v_e_214_);
stack->m_num = v_res_216_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0___boxed(lean_object* v_r_217_, lean_object* v_e_218_){
_start:
{
uint8_t v_r_boxed_219_; uint8_t v_res_220_; lean_object* v_r_221_; 
v_r_boxed_219_ = lean_unbox(v_r_217_);
v_res_220_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_r_boxed_219_, v_e_218_);
lean_dec_ref(v_e_218_);
v_r_221_ = lean_box(v_res_220_);
return v_r_221_;
}
}
uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(uint8_t v_x_222_, lean_object* v_x_223_){
_start:
{
if (lean_obj_tag(v_x_223_) == 0)
{
return v_x_222_;
}
else
{
lean_object* v_head_224_; lean_object* v_toConstantVal_225_; lean_object* v_tail_226_; lean_object* v_value_227_; lean_object* v_type_228_; uint8_t v___x_229_; uint8_t v___x_230_; 
v_head_224_ = lean_ctor_get(v_x_223_, 0);
v_toConstantVal_225_ = lean_ctor_get(v_head_224_, 0);
v_tail_226_ = lean_ctor_get(v_x_223_, 1);
v_value_227_ = lean_ctor_get(v_head_224_, 1);
v_type_228_ = lean_ctor_get(v_toConstantVal_225_, 2);
v___x_229_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_x_222_, v_type_228_);
v___x_230_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v___x_229_, v_value_227_);
v_x_222_ = v___x_230_;
v_x_223_ = v_tail_226_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_222_ = stack[0].m_num;
lean_object* v_x_223_ = stack[1].m_obj;
uint8_t v_res_232_;
v_res_232_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_x_222_, v_x_223_);
stack->m_num = v_res_232_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1___boxed(lean_object* v_x_233_, lean_object* v_x_234_){
_start:
{
uint8_t v_x_1025__boxed_235_; uint8_t v_res_236_; lean_object* v_r_237_; 
v_x_1025__boxed_235_ = lean_unbox(v_x_233_);
v_res_236_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_x_1025__boxed_235_, v_x_234_);
lean_dec(v_x_234_);
v_r_237_ = lean_box(v_res_236_);
return v_r_237_;
}
}
uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(uint8_t v_x_238_, lean_object* v_x_239_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
return v_x_238_;
}
else
{
if (v_x_238_ == 0)
{
lean_object* v_head_240_; lean_object* v_tail_241_; lean_object* v_type_242_; uint8_t v___x_243_; 
v_head_240_ = lean_ctor_get(v_x_239_, 0);
v_tail_241_ = lean_ctor_get(v_x_239_, 1);
v_type_242_ = lean_ctor_get(v_head_240_, 1);
v___x_243_ = l_Lean_Expr_hasSyntheticSorry(v_type_242_);
v_x_238_ = v___x_243_;
v_x_239_ = v_tail_241_;
goto _start;
}
else
{
lean_object* v_tail_245_; 
v_tail_245_ = lean_ctor_get(v_x_239_, 1);
v_x_239_ = v_tail_245_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_238_ = stack[0].m_num;
lean_object* v_x_239_ = stack[1].m_obj;
uint8_t v_res_247_;
v_res_247_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_238_, v_x_239_);
stack->m_num = v_res_247_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
uint8_t v_x_1050__boxed_250_; uint8_t v_res_251_; lean_object* v_r_252_; 
v_x_1050__boxed_250_ = lean_unbox(v_x_248_);
v_res_251_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_1050__boxed_250_, v_x_249_);
lean_dec(v_x_249_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(uint8_t v_x_253_, lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
return v_x_253_;
}
else
{
if (v_x_253_ == 0)
{
lean_object* v_head_255_; lean_object* v_tail_256_; lean_object* v_type_257_; uint8_t v___x_258_; uint8_t v___x_259_; 
v_head_255_ = lean_ctor_get(v_x_254_, 0);
v_tail_256_ = lean_ctor_get(v_x_254_, 1);
v_type_257_ = lean_ctor_get(v_head_255_, 1);
v___x_258_ = l_Lean_Expr_hasSyntheticSorry(v_type_257_);
v___x_259_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v___x_258_, v_tail_256_);
return v___x_259_;
}
else
{
lean_object* v_tail_260_; uint8_t v___x_261_; 
v_tail_260_ = lean_ctor_get(v_x_254_, 1);
v___x_261_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_253_, v_tail_260_);
return v___x_261_;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_253_ = stack[0].m_num;
lean_object* v_x_254_ = stack[1].m_obj;
uint8_t v_res_262_;
v_res_262_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v_x_253_, v_x_254_);
stack->m_num = v_res_262_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0___boxed(lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
uint8_t v_x_1078__boxed_265_; uint8_t v_res_266_; lean_object* v_r_267_; 
v_x_1078__boxed_265_ = lean_unbox(v_x_263_);
v_res_266_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v_x_1078__boxed_265_, v_x_264_);
lean_dec(v_x_264_);
v_r_267_ = lean_box(v_res_266_);
return v_r_267_;
}
}
uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(uint8_t v_x_268_, lean_object* v_x_269_){
_start:
{
if (lean_obj_tag(v_x_269_) == 0)
{
return v_x_268_;
}
else
{
lean_object* v_head_270_; lean_object* v_tail_271_; lean_object* v_type_272_; lean_object* v_ctors_273_; uint8_t v___y_275_; 
v_head_270_ = lean_ctor_get(v_x_269_, 0);
v_tail_271_ = lean_ctor_get(v_x_269_, 1);
v_type_272_ = lean_ctor_get(v_head_270_, 1);
v_ctors_273_ = lean_ctor_get(v_head_270_, 2);
if (v_x_268_ == 0)
{
uint8_t v___x_278_; 
v___x_278_ = l_Lean_Expr_hasSyntheticSorry(v_type_272_);
v___y_275_ = v___x_278_;
goto v___jp_274_;
}
else
{
v___y_275_ = v_x_268_;
goto v___jp_274_;
}
v___jp_274_:
{
uint8_t v___x_276_; 
v___x_276_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v___y_275_, v_ctors_273_);
v_x_268_ = v___x_276_;
v_x_269_ = v_tail_271_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_268_ = stack[0].m_num;
lean_object* v_x_269_ = stack[1].m_obj;
uint8_t v_res_279_;
v_res_279_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(v_x_268_, v_x_269_);
stack->m_num = v_res_279_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object* v_x_280_, lean_object* v_x_281_){
_start:
{
uint8_t v_x_1106__boxed_282_; uint8_t v_res_283_; lean_object* v_r_284_; 
v_x_1106__boxed_282_ = lean_unbox(v_x_280_);
v_res_283_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(v_x_1106__boxed_282_, v_x_281_);
lean_dec(v_x_281_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(uint8_t v_x_285_, lean_object* v_x_286_){
_start:
{
if (lean_obj_tag(v_x_286_) == 0)
{
return v_x_285_;
}
else
{
lean_object* v_head_287_; lean_object* v_tail_288_; lean_object* v_type_289_; lean_object* v_ctors_290_; uint8_t v___y_292_; 
v_head_287_ = lean_ctor_get(v_x_286_, 0);
v_tail_288_ = lean_ctor_get(v_x_286_, 1);
v_type_289_ = lean_ctor_get(v_head_287_, 1);
v_ctors_290_ = lean_ctor_get(v_head_287_, 2);
if (v_x_285_ == 0)
{
uint8_t v___x_295_; 
v___x_295_ = l_Lean_Expr_hasSyntheticSorry(v_type_289_);
v___y_292_ = v___x_295_;
goto v___jp_291_;
}
else
{
v___y_292_ = v_x_285_;
goto v___jp_291_;
}
v___jp_291_:
{
uint8_t v___x_293_; uint8_t v___x_294_; 
v___x_293_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v___y_292_, v_ctors_290_);
v___x_294_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(v___x_293_, v_tail_288_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_285_ = stack[0].m_num;
lean_object* v_x_286_ = stack[1].m_obj;
uint8_t v_res_296_;
v_res_296_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_x_285_, v_x_286_);
stack->m_num = v_res_296_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2___boxed(lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
uint8_t v_x_1137__boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v_x_1137__boxed_299_ = lean_unbox(v_x_297_);
v_res_300_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_x_1137__boxed_299_, v_x_298_);
lean_dec(v_x_298_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(lean_object* v_d_302_, uint8_t v_a_303_){
_start:
{
switch(lean_obj_tag(v_d_302_))
{
case 0:
{
lean_object* v_val_304_; lean_object* v_toConstantVal_305_; lean_object* v_type_306_; uint8_t v___x_307_; 
v_val_304_ = lean_ctor_get(v_d_302_, 0);
v_toConstantVal_305_ = lean_ctor_get(v_val_304_, 0);
v_type_306_ = lean_ctor_get(v_toConstantVal_305_, 2);
v___x_307_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_a_303_, v_type_306_);
return v___x_307_;
}
case 4:
{
return v_a_303_;
}
case 5:
{
lean_object* v_defns_308_; uint8_t v___x_309_; 
v_defns_308_ = lean_ctor_get(v_d_302_, 0);
v___x_309_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_a_303_, v_defns_308_);
return v___x_309_;
}
case 6:
{
lean_object* v_types_310_; uint8_t v___x_311_; 
v_types_310_ = lean_ctor_get(v_d_302_, 2);
v___x_311_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_a_303_, v_types_310_);
return v___x_311_;
}
default: 
{
lean_object* v_val_312_; lean_object* v_toConstantVal_313_; lean_object* v_value_314_; lean_object* v_type_315_; uint8_t v___x_316_; uint8_t v___x_317_; 
v_val_312_ = lean_ctor_get(v_d_302_, 0);
v_toConstantVal_313_ = lean_ctor_get(v_val_312_, 0);
v_value_314_ = lean_ctor_get(v_val_312_, 1);
v_type_315_ = lean_ctor_get(v_toConstantVal_313_, 2);
v___x_316_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_a_303_, v_type_315_);
v___x_317_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v___x_316_, v_value_314_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT void l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_302_ = stack[0].m_obj;
uint8_t v_a_303_ = stack[1].m_num;
uint8_t v_res_318_;
v_res_318_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(v_d_302_, v_a_303_);
stack->m_num = v_res_318_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___boxed(lean_object* v_d_319_, lean_object* v_a_320_){
_start:
{
uint8_t v_a_boxed_321_; uint8_t v_res_322_; lean_object* v_r_323_; 
v_a_boxed_321_ = lean_unbox(v_a_320_);
v_res_322_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(v_d_319_, v_a_boxed_321_);
lean_dec(v_d_319_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
uint8_t l_Lean_Declaration_hasSyntheticSorry(lean_object* v_d_324_){
_start:
{
uint8_t v___x_325_; uint8_t v___x_326_; 
v___x_325_ = 0;
v___x_326_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(v_d_324_, v___x_325_);
return v___x_326_;
}
}
LEAN_EXPORT void l_Lean_Declaration_hasSyntheticSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_324_ = stack[0].m_obj;
uint8_t v_res_327_;
v_res_327_ = l_Lean_Declaration_hasSyntheticSorry(v_d_324_);
stack->m_num = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSyntheticSorry___boxed(lean_object* v_d_328_){
_start:
{
uint8_t v_res_329_; lean_object* v_r_330_; 
v_res_329_ = l_Lean_Declaration_hasSyntheticSorry(v_d_328_);
lean_dec(v_d_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(uint8_t v_r_331_, lean_object* v_e_332_){
_start:
{
if (v_r_331_ == 0)
{
uint8_t v___x_333_; 
v___x_333_ = l_Lean_Expr_hasNonSyntheticSorry(v_e_332_);
return v___x_333_;
}
else
{
return v_r_331_;
}
}
}
LEAN_EXPORT void l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_r_331_ = stack[0].m_num;
lean_object* v_e_332_ = stack[1].m_obj;
uint8_t v_res_334_;
v_res_334_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_r_331_, v_e_332_);
stack->m_num = v_res_334_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0___boxed(lean_object* v_r_335_, lean_object* v_e_336_){
_start:
{
uint8_t v_r_boxed_337_; uint8_t v_res_338_; lean_object* v_r_339_; 
v_r_boxed_337_ = lean_unbox(v_r_335_);
v_res_338_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_r_boxed_337_, v_e_336_);
lean_dec_ref(v_e_336_);
v_r_339_ = lean_box(v_res_338_);
return v_r_339_;
}
}
uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(uint8_t v_x_340_, lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_341_) == 0)
{
return v_x_340_;
}
else
{
lean_object* v_head_342_; lean_object* v_toConstantVal_343_; lean_object* v_tail_344_; lean_object* v_value_345_; lean_object* v_type_346_; uint8_t v___x_347_; uint8_t v___x_348_; 
v_head_342_ = lean_ctor_get(v_x_341_, 0);
v_toConstantVal_343_ = lean_ctor_get(v_head_342_, 0);
v_tail_344_ = lean_ctor_get(v_x_341_, 1);
v_value_345_ = lean_ctor_get(v_head_342_, 1);
v_type_346_ = lean_ctor_get(v_toConstantVal_343_, 2);
v___x_347_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_x_340_, v_type_346_);
v___x_348_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v___x_347_, v_value_345_);
v_x_340_ = v___x_348_;
v_x_341_ = v_tail_344_;
goto _start;
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_340_ = stack[0].m_num;
lean_object* v_x_341_ = stack[1].m_obj;
uint8_t v_res_350_;
v_res_350_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_x_340_, v_x_341_);
stack->m_num = v_res_350_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1___boxed(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
uint8_t v_x_1025__boxed_353_; uint8_t v_res_354_; lean_object* v_r_355_; 
v_x_1025__boxed_353_ = lean_unbox(v_x_351_);
v_res_354_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_x_1025__boxed_353_, v_x_352_);
lean_dec(v_x_352_);
v_r_355_ = lean_box(v_res_354_);
return v_r_355_;
}
}
uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(uint8_t v_x_356_, lean_object* v_x_357_){
_start:
{
if (lean_obj_tag(v_x_357_) == 0)
{
return v_x_356_;
}
else
{
if (v_x_356_ == 0)
{
lean_object* v_head_358_; lean_object* v_tail_359_; lean_object* v_type_360_; uint8_t v___x_361_; 
v_head_358_ = lean_ctor_get(v_x_357_, 0);
v_tail_359_ = lean_ctor_get(v_x_357_, 1);
v_type_360_ = lean_ctor_get(v_head_358_, 1);
v___x_361_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_360_);
v_x_356_ = v___x_361_;
v_x_357_ = v_tail_359_;
goto _start;
}
else
{
lean_object* v_tail_363_; 
v_tail_363_ = lean_ctor_get(v_x_357_, 1);
v_x_357_ = v_tail_363_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_356_ = stack[0].m_num;
lean_object* v_x_357_ = stack[1].m_obj;
uint8_t v_res_365_;
v_res_365_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_356_, v_x_357_);
stack->m_num = v_res_365_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object* v_x_366_, lean_object* v_x_367_){
_start:
{
uint8_t v_x_1050__boxed_368_; uint8_t v_res_369_; lean_object* v_r_370_; 
v_x_1050__boxed_368_ = lean_unbox(v_x_366_);
v_res_369_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_1050__boxed_368_, v_x_367_);
lean_dec(v_x_367_);
v_r_370_ = lean_box(v_res_369_);
return v_r_370_;
}
}
uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(uint8_t v_x_371_, lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
return v_x_371_;
}
else
{
if (v_x_371_ == 0)
{
lean_object* v_head_373_; lean_object* v_tail_374_; lean_object* v_type_375_; uint8_t v___x_376_; uint8_t v___x_377_; 
v_head_373_ = lean_ctor_get(v_x_372_, 0);
v_tail_374_ = lean_ctor_get(v_x_372_, 1);
v_type_375_ = lean_ctor_get(v_head_373_, 1);
v___x_376_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_375_);
v___x_377_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v___x_376_, v_tail_374_);
return v___x_377_;
}
else
{
lean_object* v_tail_378_; uint8_t v___x_379_; 
v_tail_378_ = lean_ctor_get(v_x_372_, 1);
v___x_379_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_371_, v_tail_378_);
return v___x_379_;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_371_ = stack[0].m_num;
lean_object* v_x_372_ = stack[1].m_obj;
uint8_t v_res_380_;
v_res_380_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v_x_371_, v_x_372_);
stack->m_num = v_res_380_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0___boxed(lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
uint8_t v_x_1078__boxed_383_; uint8_t v_res_384_; lean_object* v_r_385_; 
v_x_1078__boxed_383_ = lean_unbox(v_x_381_);
v_res_384_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v_x_1078__boxed_383_, v_x_382_);
lean_dec(v_x_382_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(uint8_t v_x_386_, lean_object* v_x_387_){
_start:
{
if (lean_obj_tag(v_x_387_) == 0)
{
return v_x_386_;
}
else
{
lean_object* v_head_388_; lean_object* v_tail_389_; lean_object* v_type_390_; lean_object* v_ctors_391_; uint8_t v___y_393_; 
v_head_388_ = lean_ctor_get(v_x_387_, 0);
v_tail_389_ = lean_ctor_get(v_x_387_, 1);
v_type_390_ = lean_ctor_get(v_head_388_, 1);
v_ctors_391_ = lean_ctor_get(v_head_388_, 2);
if (v_x_386_ == 0)
{
uint8_t v___x_396_; 
v___x_396_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_390_);
v___y_393_ = v___x_396_;
goto v___jp_392_;
}
else
{
v___y_393_ = v_x_386_;
goto v___jp_392_;
}
v___jp_392_:
{
uint8_t v___x_394_; 
v___x_394_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v___y_393_, v_ctors_391_);
v_x_386_ = v___x_394_;
v_x_387_ = v_tail_389_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_386_ = stack[0].m_num;
lean_object* v_x_387_ = stack[1].m_obj;
uint8_t v_res_397_;
v_res_397_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(v_x_386_, v_x_387_);
stack->m_num = v_res_397_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object* v_x_398_, lean_object* v_x_399_){
_start:
{
uint8_t v_x_1106__boxed_400_; uint8_t v_res_401_; lean_object* v_r_402_; 
v_x_1106__boxed_400_ = lean_unbox(v_x_398_);
v_res_401_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(v_x_1106__boxed_400_, v_x_399_);
lean_dec(v_x_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(uint8_t v_x_403_, lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
return v_x_403_;
}
else
{
lean_object* v_head_405_; lean_object* v_tail_406_; lean_object* v_type_407_; lean_object* v_ctors_408_; uint8_t v___y_410_; 
v_head_405_ = lean_ctor_get(v_x_404_, 0);
v_tail_406_ = lean_ctor_get(v_x_404_, 1);
v_type_407_ = lean_ctor_get(v_head_405_, 1);
v_ctors_408_ = lean_ctor_get(v_head_405_, 2);
if (v_x_403_ == 0)
{
uint8_t v___x_413_; 
v___x_413_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_407_);
v___y_410_ = v___x_413_;
goto v___jp_409_;
}
else
{
v___y_410_ = v_x_403_;
goto v___jp_409_;
}
v___jp_409_:
{
uint8_t v___x_411_; uint8_t v___x_412_; 
v___x_411_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v___y_410_, v_ctors_408_);
v___x_412_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(v___x_411_, v_tail_406_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_403_ = stack[0].m_num;
lean_object* v_x_404_ = stack[1].m_obj;
uint8_t v_res_414_;
v_res_414_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_x_403_, v_x_404_);
stack->m_num = v_res_414_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2___boxed(lean_object* v_x_415_, lean_object* v_x_416_){
_start:
{
uint8_t v_x_1137__boxed_417_; uint8_t v_res_418_; lean_object* v_r_419_; 
v_x_1137__boxed_417_ = lean_unbox(v_x_415_);
v_res_418_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_x_1137__boxed_417_, v_x_416_);
lean_dec(v_x_416_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(lean_object* v_d_420_, uint8_t v_a_421_){
_start:
{
switch(lean_obj_tag(v_d_420_))
{
case 0:
{
lean_object* v_val_422_; lean_object* v_toConstantVal_423_; lean_object* v_type_424_; uint8_t v___x_425_; 
v_val_422_ = lean_ctor_get(v_d_420_, 0);
v_toConstantVal_423_ = lean_ctor_get(v_val_422_, 0);
v_type_424_ = lean_ctor_get(v_toConstantVal_423_, 2);
v___x_425_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_a_421_, v_type_424_);
return v___x_425_;
}
case 4:
{
return v_a_421_;
}
case 5:
{
lean_object* v_defns_426_; uint8_t v___x_427_; 
v_defns_426_ = lean_ctor_get(v_d_420_, 0);
v___x_427_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_a_421_, v_defns_426_);
return v___x_427_;
}
case 6:
{
lean_object* v_types_428_; uint8_t v___x_429_; 
v_types_428_ = lean_ctor_get(v_d_420_, 2);
v___x_429_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_a_421_, v_types_428_);
return v___x_429_;
}
default: 
{
lean_object* v_val_430_; lean_object* v_toConstantVal_431_; lean_object* v_value_432_; lean_object* v_type_433_; uint8_t v___x_434_; uint8_t v___x_435_; 
v_val_430_ = lean_ctor_get(v_d_420_, 0);
v_toConstantVal_431_ = lean_ctor_get(v_val_430_, 0);
v_value_432_ = lean_ctor_get(v_val_430_, 1);
v_type_433_ = lean_ctor_get(v_toConstantVal_431_, 2);
v___x_434_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_a_421_, v_type_433_);
v___x_435_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v___x_434_, v_value_432_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT void l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_420_ = stack[0].m_obj;
uint8_t v_a_421_ = stack[1].m_num;
uint8_t v_res_436_;
v_res_436_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(v_d_420_, v_a_421_);
stack->m_num = v_res_436_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___boxed(lean_object* v_d_437_, lean_object* v_a_438_){
_start:
{
uint8_t v_a_boxed_439_; uint8_t v_res_440_; lean_object* v_r_441_; 
v_a_boxed_439_ = lean_unbox(v_a_438_);
v_res_440_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(v_d_437_, v_a_boxed_439_);
lean_dec(v_d_437_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
uint8_t l_Lean_Declaration_hasNonSyntheticSorry(lean_object* v_d_442_){
_start:
{
uint8_t v___x_443_; uint8_t v___x_444_; 
v___x_443_ = 0;
v___x_444_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(v_d_442_, v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT void l_Lean_Declaration_hasNonSyntheticSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_d_442_ = stack[0].m_obj;
uint8_t v_res_445_;
v_res_445_ = l_Lean_Declaration_hasNonSyntheticSorry(v_d_442_);
stack->m_num = v_res_445_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasNonSyntheticSorry___boxed(lean_object* v_d_446_){
_start:
{
uint8_t v_res_447_; lean_object* v_r_448_; 
v_res_447_ = l_Lean_Declaration_hasNonSyntheticSorry(v_d_446_);
lean_dec(v_d_446_);
v_r_448_ = lean_box(v_res_447_);
return v_r_448_;
}
}
lean_object* runtime_initialize_Lean_Util_FindExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_FindExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin);
lean_object* initialize_Lean_Declaration(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_FindExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_Sorry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_Sorry(builtin);
}
#ifdef __cplusplus
}
#endif
