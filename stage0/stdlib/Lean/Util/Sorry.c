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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Expr_isSorry(lean_object* v_e_4_){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_5_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_6_ = l_Lean_Expr_isAppOf(v_e_4_, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSorry___boxed(lean_object* v_e_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_Expr_isSorry(v_e_7_);
lean_dec_ref(v_e_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isSyntheticSorry(lean_object* v_e_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_17_ = l_Lean_Expr_isAppOf(v_e_15_, v___x_16_);
if (v___x_17_ == 0)
{
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_unsigned_to_nat(2u);
v___x_19_ = l_Lean_Expr_getAppNumArgs(v_e_15_);
v___x_20_ = lean_nat_dec_le(v___x_18_, v___x_19_);
if (v___x_20_ == 0)
{
lean_dec(v___x_19_);
return v___x_20_;
}
else
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_22_ = lean_nat_sub(v___x_19_, v___x_21_);
lean_dec(v___x_19_);
v___x_23_ = lean_nat_sub(v___x_22_, v___x_21_);
lean_dec(v___x_22_);
v___x_24_ = l_Lean_Expr_getRevArg_x21(v_e_15_, v___x_23_);
v___x_25_ = ((lean_object*)(l_Lean_Expr_isSyntheticSorry___closed__2));
v___x_26_ = l_Lean_Expr_isConstOf(v___x_24_, v___x_25_);
lean_dec_ref(v___x_24_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object* v_e_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_Lean_Expr_isSyntheticSorry(v_e_27_);
lean_dec_ref(v_e_27_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isNonSyntheticSorry(lean_object* v_e_34_){
_start:
{
lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_35_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_36_ = l_Lean_Expr_isAppOf(v_e_34_, v___x_35_);
if (v___x_36_ == 0)
{
return v___x_36_;
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; uint8_t v___x_39_; 
v___x_37_ = lean_unsigned_to_nat(2u);
v___x_38_ = l_Lean_Expr_getAppNumArgs(v_e_34_);
v___x_39_ = lean_nat_dec_le(v___x_37_, v___x_38_);
if (v___x_39_ == 0)
{
lean_dec(v___x_38_);
return v___x_39_;
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = lean_nat_sub(v___x_38_, v___x_40_);
lean_dec(v___x_38_);
v___x_42_ = lean_nat_sub(v___x_41_, v___x_40_);
lean_dec(v___x_41_);
v___x_43_ = l_Lean_Expr_getRevArg_x21(v_e_34_, v___x_42_);
v___x_44_ = ((lean_object*)(l_Lean_Expr_isNonSyntheticSorry___closed__1));
v___x_45_ = l_Lean_Expr_isConstOf(v___x_43_, v___x_44_);
lean_dec_ref(v___x_43_);
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isNonSyntheticSorry___boxed(lean_object* v_e_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_Lean_Expr_isNonSyntheticSorry(v_e_46_);
lean_dec_ref(v_e_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry___lam__0(lean_object* v_x_49_){
_start:
{
lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_50_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_51_ = l_Lean_Expr_isConstOf(v_x_49_, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___lam__0___boxed(lean_object* v_x_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Lean_Expr_hasSorry___lam__0(v_x_52_);
lean_dec_ref(v_x_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry(lean_object* v_e_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___x_58_; 
v___f_57_ = ((lean_object*)(l_Lean_Expr_hasSorry___closed__0));
v___x_58_ = lean_find_expr(v___f_57_, v_e_56_);
if (lean_obj_tag(v___x_58_) == 0)
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
else
{
uint8_t v___x_60_; 
lean_dec_ref_known(v___x_58_, 1);
v___x_60_ = 1;
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___boxed(lean_object* v_e_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Lean_Expr_hasSorry(v_e_61_);
lean_dec_ref(v_e_61_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object* v_e_65_){
_start:
{
lean_object* v___f_66_; lean_object* v___x_67_; 
v___f_66_ = ((lean_object*)(l_Lean_Expr_hasSyntheticSorry___closed__0));
v___x_67_ = lean_find_expr(v___f_66_, v_e_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
else
{
uint8_t v___x_69_; 
lean_dec_ref_known(v___x_67_, 1);
v___x_69_ = 1;
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object* v_e_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_Expr_hasSyntheticSorry(v_e_70_);
lean_dec_ref(v_e_70_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasNonSyntheticSorry(lean_object* v_e_74_){
_start:
{
lean_object* v___f_75_; lean_object* v___x_76_; 
v___f_75_ = ((lean_object*)(l_Lean_Expr_hasNonSyntheticSorry___closed__0));
v___x_76_ = lean_find_expr(v___f_75_, v_e_74_);
if (lean_obj_tag(v___x_76_) == 0)
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
lean_dec_ref_known(v___x_76_, 1);
v___x_78_ = 1;
return v___x_78_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasNonSyntheticSorry___boxed(lean_object* v_e_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Lean_Expr_hasNonSyntheticSorry(v_e_79_);
lean_dec_ref(v_e_79_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(uint8_t v_r_82_, lean_object* v_e_83_){
_start:
{
if (v_r_82_ == 0)
{
uint8_t v___x_84_; 
v___x_84_ = l_Lean_Expr_hasSorry(v_e_83_);
return v___x_84_;
}
else
{
return v_r_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0___boxed(lean_object* v_r_85_, lean_object* v_e_86_){
_start:
{
uint8_t v_r_boxed_87_; uint8_t v_res_88_; lean_object* v_r_89_; 
v_r_boxed_87_ = lean_unbox(v_r_85_);
v_res_88_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_r_boxed_87_, v_e_86_);
lean_dec_ref(v_e_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(uint8_t v_x_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_91_) == 0)
{
return v_x_90_;
}
else
{
lean_object* v_head_92_; lean_object* v_toConstantVal_93_; lean_object* v_tail_94_; lean_object* v_value_95_; lean_object* v_type_96_; uint8_t v___x_97_; uint8_t v___x_98_; 
v_head_92_ = lean_ctor_get(v_x_91_, 0);
v_toConstantVal_93_ = lean_ctor_get(v_head_92_, 0);
v_tail_94_ = lean_ctor_get(v_x_91_, 1);
v_value_95_ = lean_ctor_get(v_head_92_, 1);
v_type_96_ = lean_ctor_get(v_toConstantVal_93_, 2);
v___x_97_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_x_90_, v_type_96_);
v___x_98_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v___x_97_, v_value_95_);
v_x_90_ = v___x_98_;
v_x_91_ = v_tail_94_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1___boxed(lean_object* v_x_100_, lean_object* v_x_101_){
_start:
{
uint8_t v_x_1024__boxed_102_; uint8_t v_res_103_; lean_object* v_r_104_; 
v_x_1024__boxed_102_ = lean_unbox(v_x_100_);
v_res_103_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_x_1024__boxed_102_, v_x_101_);
lean_dec(v_x_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(uint8_t v_x_105_, lean_object* v_x_106_){
_start:
{
if (lean_obj_tag(v_x_106_) == 0)
{
return v_x_105_;
}
else
{
if (v_x_105_ == 0)
{
lean_object* v_head_107_; lean_object* v_tail_108_; lean_object* v_type_109_; uint8_t v___x_110_; 
v_head_107_ = lean_ctor_get(v_x_106_, 0);
v_tail_108_ = lean_ctor_get(v_x_106_, 1);
v_type_109_ = lean_ctor_get(v_head_107_, 1);
v___x_110_ = l_Lean_Expr_hasSorry(v_type_109_);
v_x_105_ = v___x_110_;
v_x_106_ = v_tail_108_;
goto _start;
}
else
{
lean_object* v_tail_112_; 
v_tail_112_ = lean_ctor_get(v_x_106_, 1);
v_x_106_ = v_tail_112_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1___boxed(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
uint8_t v_x_1040__boxed_116_; uint8_t v_res_117_; lean_object* v_r_118_; 
v_x_1040__boxed_116_ = lean_unbox(v_x_114_);
v_res_117_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_116_, v_x_115_);
lean_dec(v_x_115_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(uint8_t v_x_119_, lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
return v_x_119_;
}
else
{
if (v_x_119_ == 0)
{
lean_object* v_head_121_; lean_object* v_tail_122_; lean_object* v_type_123_; uint8_t v___x_124_; uint8_t v___x_125_; 
v_head_121_ = lean_ctor_get(v_x_120_, 0);
v_tail_122_ = lean_ctor_get(v_x_120_, 1);
v_type_123_ = lean_ctor_get(v_head_121_, 1);
v___x_124_ = l_Lean_Expr_hasSorry(v_type_123_);
v___x_125_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v___x_124_, v_tail_122_);
return v___x_125_;
}
else
{
lean_object* v_tail_126_; uint8_t v___x_127_; 
v_tail_126_ = lean_ctor_get(v_x_120_, 1);
v___x_127_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_119_, v_tail_126_);
return v___x_127_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0___boxed(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_x_1058__boxed_130_; uint8_t v_res_131_; lean_object* v_r_132_; 
v_x_1058__boxed_130_ = lean_unbox(v_x_128_);
v_res_131_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v_x_1058__boxed_130_, v_x_129_);
lean_dec(v_x_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(uint8_t v_x_133_, lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_134_) == 0)
{
return v_x_133_;
}
else
{
lean_object* v_head_135_; lean_object* v_tail_136_; lean_object* v_type_137_; lean_object* v_ctors_138_; uint8_t v___y_140_; 
v_head_135_ = lean_ctor_get(v_x_134_, 0);
v_tail_136_ = lean_ctor_get(v_x_134_, 1);
v_type_137_ = lean_ctor_get(v_head_135_, 1);
v_ctors_138_ = lean_ctor_get(v_head_135_, 2);
if (v_x_133_ == 0)
{
uint8_t v___x_143_; 
v___x_143_ = l_Lean_Expr_hasSorry(v_type_137_);
v___y_140_ = v___x_143_;
goto v___jp_139_;
}
else
{
v___y_140_ = v_x_133_;
goto v___jp_139_;
}
v___jp_139_:
{
uint8_t v___x_141_; 
v___x_141_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v___y_140_, v_ctors_138_);
v_x_133_ = v___x_141_;
v_x_134_ = v_tail_136_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4___boxed(lean_object* v_x_144_, lean_object* v_x_145_){
_start:
{
uint8_t v_x_1076__boxed_146_; uint8_t v_res_147_; lean_object* v_r_148_; 
v_x_1076__boxed_146_ = lean_unbox(v_x_144_);
v_res_147_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_146_, v_x_145_);
lean_dec(v_x_145_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(uint8_t v_x_149_, lean_object* v_x_150_){
_start:
{
if (lean_obj_tag(v_x_150_) == 0)
{
return v_x_149_;
}
else
{
lean_object* v_head_151_; lean_object* v_tail_152_; lean_object* v_type_153_; lean_object* v_ctors_154_; uint8_t v___y_156_; 
v_head_151_ = lean_ctor_get(v_x_150_, 0);
v_tail_152_ = lean_ctor_get(v_x_150_, 1);
v_type_153_ = lean_ctor_get(v_head_151_, 1);
v_ctors_154_ = lean_ctor_get(v_head_151_, 2);
if (v_x_149_ == 0)
{
uint8_t v___x_159_; 
v___x_159_ = l_Lean_Expr_hasSorry(v_type_153_);
v___y_156_ = v___x_159_;
goto v___jp_155_;
}
else
{
v___y_156_ = v_x_149_;
goto v___jp_155_;
}
v___jp_155_:
{
uint8_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v___y_156_, v_ctors_154_);
v___x_158_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(v___x_157_, v_tail_152_);
return v___x_158_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2___boxed(lean_object* v_x_160_, lean_object* v_x_161_){
_start:
{
uint8_t v_x_1096__boxed_162_; uint8_t v_res_163_; lean_object* v_r_164_; 
v_x_1096__boxed_162_ = lean_unbox(v_x_160_);
v_res_163_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_x_1096__boxed_162_, v_x_161_);
lean_dec(v_x_161_);
v_r_164_ = lean_box(v_res_163_);
return v_r_164_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(lean_object* v_d_165_, uint8_t v_a_166_){
_start:
{
switch(lean_obj_tag(v_d_165_))
{
case 0:
{
lean_object* v_val_167_; lean_object* v_toConstantVal_168_; lean_object* v_type_169_; uint8_t v___x_170_; 
v_val_167_ = lean_ctor_get(v_d_165_, 0);
v_toConstantVal_168_ = lean_ctor_get(v_val_167_, 0);
v_type_169_ = lean_ctor_get(v_toConstantVal_168_, 2);
v___x_170_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_a_166_, v_type_169_);
return v___x_170_;
}
case 4:
{
return v_a_166_;
}
case 5:
{
lean_object* v_defns_171_; uint8_t v___x_172_; 
v_defns_171_ = lean_ctor_get(v_d_165_, 0);
v___x_172_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_a_166_, v_defns_171_);
return v___x_172_;
}
case 6:
{
lean_object* v_types_173_; uint8_t v___x_174_; 
v_types_173_ = lean_ctor_get(v_d_165_, 2);
v___x_174_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_a_166_, v_types_173_);
return v___x_174_;
}
default: 
{
lean_object* v_val_175_; lean_object* v_toConstantVal_176_; lean_object* v_value_177_; lean_object* v_type_178_; uint8_t v___x_179_; uint8_t v___x_180_; 
v_val_175_ = lean_ctor_get(v_d_165_, 0);
v_toConstantVal_176_ = lean_ctor_get(v_val_175_, 0);
v_value_177_ = lean_ctor_get(v_val_175_, 1);
v_type_178_ = lean_ctor_get(v_toConstantVal_176_, 2);
v___x_179_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_a_166_, v_type_178_);
v___x_180_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v___x_179_, v_value_177_);
return v___x_180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___boxed(lean_object* v_d_181_, lean_object* v_a_182_){
_start:
{
uint8_t v_a_boxed_183_; uint8_t v_res_184_; lean_object* v_r_185_; 
v_a_boxed_183_ = lean_unbox(v_a_182_);
v_res_184_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(v_d_181_, v_a_boxed_183_);
lean_dec(v_d_181_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSorry(lean_object* v_d_186_){
_start:
{
uint8_t v___x_187_; uint8_t v___x_188_; 
v___x_187_ = 0;
v___x_188_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(v_d_186_, v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSorry___boxed(lean_object* v_d_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Lean_Declaration_hasSorry(v_d_189_);
lean_dec(v_d_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(uint8_t v_r_192_, lean_object* v_e_193_){
_start:
{
if (v_r_192_ == 0)
{
uint8_t v___x_194_; 
v___x_194_ = l_Lean_Expr_hasSyntheticSorry(v_e_193_);
return v___x_194_;
}
else
{
return v_r_192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0___boxed(lean_object* v_r_195_, lean_object* v_e_196_){
_start:
{
uint8_t v_r_boxed_197_; uint8_t v_res_198_; lean_object* v_r_199_; 
v_r_boxed_197_ = lean_unbox(v_r_195_);
v_res_198_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_r_boxed_197_, v_e_196_);
lean_dec_ref(v_e_196_);
v_r_199_ = lean_box(v_res_198_);
return v_r_199_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(uint8_t v_x_200_, lean_object* v_x_201_){
_start:
{
if (lean_obj_tag(v_x_201_) == 0)
{
return v_x_200_;
}
else
{
lean_object* v_head_202_; lean_object* v_toConstantVal_203_; lean_object* v_tail_204_; lean_object* v_value_205_; lean_object* v_type_206_; uint8_t v___x_207_; uint8_t v___x_208_; 
v_head_202_ = lean_ctor_get(v_x_201_, 0);
v_toConstantVal_203_ = lean_ctor_get(v_head_202_, 0);
v_tail_204_ = lean_ctor_get(v_x_201_, 1);
v_value_205_ = lean_ctor_get(v_head_202_, 1);
v_type_206_ = lean_ctor_get(v_toConstantVal_203_, 2);
v___x_207_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_x_200_, v_type_206_);
v___x_208_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v___x_207_, v_value_205_);
v_x_200_ = v___x_208_;
v_x_201_ = v_tail_204_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1___boxed(lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
uint8_t v_x_1024__boxed_212_; uint8_t v_res_213_; lean_object* v_r_214_; 
v_x_1024__boxed_212_ = lean_unbox(v_x_210_);
v_res_213_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_x_1024__boxed_212_, v_x_211_);
lean_dec(v_x_211_);
v_r_214_ = lean_box(v_res_213_);
return v_r_214_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(uint8_t v_x_215_, lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
return v_x_215_;
}
else
{
if (v_x_215_ == 0)
{
lean_object* v_head_217_; lean_object* v_tail_218_; lean_object* v_type_219_; uint8_t v___x_220_; 
v_head_217_ = lean_ctor_get(v_x_216_, 0);
v_tail_218_ = lean_ctor_get(v_x_216_, 1);
v_type_219_ = lean_ctor_get(v_head_217_, 1);
v___x_220_ = l_Lean_Expr_hasSyntheticSorry(v_type_219_);
v_x_215_ = v___x_220_;
v_x_216_ = v_tail_218_;
goto _start;
}
else
{
lean_object* v_tail_222_; 
v_tail_222_ = lean_ctor_get(v_x_216_, 1);
v_x_216_ = v_tail_222_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object* v_x_224_, lean_object* v_x_225_){
_start:
{
uint8_t v_x_1040__boxed_226_; uint8_t v_res_227_; lean_object* v_r_228_; 
v_x_1040__boxed_226_ = lean_unbox(v_x_224_);
v_res_227_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_226_, v_x_225_);
lean_dec(v_x_225_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(uint8_t v_x_229_, lean_object* v_x_230_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
return v_x_229_;
}
else
{
if (v_x_229_ == 0)
{
lean_object* v_head_231_; lean_object* v_tail_232_; lean_object* v_type_233_; uint8_t v___x_234_; uint8_t v___x_235_; 
v_head_231_ = lean_ctor_get(v_x_230_, 0);
v_tail_232_ = lean_ctor_get(v_x_230_, 1);
v_type_233_ = lean_ctor_get(v_head_231_, 1);
v___x_234_ = l_Lean_Expr_hasSyntheticSorry(v_type_233_);
v___x_235_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v___x_234_, v_tail_232_);
return v___x_235_;
}
else
{
lean_object* v_tail_236_; uint8_t v___x_237_; 
v_tail_236_ = lean_ctor_get(v_x_230_, 1);
v___x_237_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_229_, v_tail_236_);
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0___boxed(lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
uint8_t v_x_1058__boxed_240_; uint8_t v_res_241_; lean_object* v_r_242_; 
v_x_1058__boxed_240_ = lean_unbox(v_x_238_);
v_res_241_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v_x_1058__boxed_240_, v_x_239_);
lean_dec(v_x_239_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(uint8_t v_x_243_, lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
return v_x_243_;
}
else
{
lean_object* v_head_245_; lean_object* v_tail_246_; lean_object* v_type_247_; lean_object* v_ctors_248_; uint8_t v___y_250_; 
v_head_245_ = lean_ctor_get(v_x_244_, 0);
v_tail_246_ = lean_ctor_get(v_x_244_, 1);
v_type_247_ = lean_ctor_get(v_head_245_, 1);
v_ctors_248_ = lean_ctor_get(v_head_245_, 2);
if (v_x_243_ == 0)
{
uint8_t v___x_253_; 
v___x_253_ = l_Lean_Expr_hasSyntheticSorry(v_type_247_);
v___y_250_ = v___x_253_;
goto v___jp_249_;
}
else
{
v___y_250_ = v_x_243_;
goto v___jp_249_;
}
v___jp_249_:
{
uint8_t v___x_251_; 
v___x_251_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v___y_250_, v_ctors_248_);
v_x_243_ = v___x_251_;
v_x_244_ = v_tail_246_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
uint8_t v_x_1076__boxed_256_; uint8_t v_res_257_; lean_object* v_r_258_; 
v_x_1076__boxed_256_ = lean_unbox(v_x_254_);
v_res_257_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_256_, v_x_255_);
lean_dec(v_x_255_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(uint8_t v_x_259_, lean_object* v_x_260_){
_start:
{
if (lean_obj_tag(v_x_260_) == 0)
{
return v_x_259_;
}
else
{
lean_object* v_head_261_; lean_object* v_tail_262_; lean_object* v_type_263_; lean_object* v_ctors_264_; uint8_t v___y_266_; 
v_head_261_ = lean_ctor_get(v_x_260_, 0);
v_tail_262_ = lean_ctor_get(v_x_260_, 1);
v_type_263_ = lean_ctor_get(v_head_261_, 1);
v_ctors_264_ = lean_ctor_get(v_head_261_, 2);
if (v_x_259_ == 0)
{
uint8_t v___x_269_; 
v___x_269_ = l_Lean_Expr_hasSyntheticSorry(v_type_263_);
v___y_266_ = v___x_269_;
goto v___jp_265_;
}
else
{
v___y_266_ = v_x_259_;
goto v___jp_265_;
}
v___jp_265_:
{
uint8_t v___x_267_; uint8_t v___x_268_; 
v___x_267_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v___y_266_, v_ctors_264_);
v___x_268_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(v___x_267_, v_tail_262_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2___boxed(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
uint8_t v_x_1096__boxed_272_; uint8_t v_res_273_; lean_object* v_r_274_; 
v_x_1096__boxed_272_ = lean_unbox(v_x_270_);
v_res_273_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_x_1096__boxed_272_, v_x_271_);
lean_dec(v_x_271_);
v_r_274_ = lean_box(v_res_273_);
return v_r_274_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(lean_object* v_d_275_, uint8_t v_a_276_){
_start:
{
switch(lean_obj_tag(v_d_275_))
{
case 0:
{
lean_object* v_val_277_; lean_object* v_toConstantVal_278_; lean_object* v_type_279_; uint8_t v___x_280_; 
v_val_277_ = lean_ctor_get(v_d_275_, 0);
v_toConstantVal_278_ = lean_ctor_get(v_val_277_, 0);
v_type_279_ = lean_ctor_get(v_toConstantVal_278_, 2);
v___x_280_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_a_276_, v_type_279_);
return v___x_280_;
}
case 4:
{
return v_a_276_;
}
case 5:
{
lean_object* v_defns_281_; uint8_t v___x_282_; 
v_defns_281_ = lean_ctor_get(v_d_275_, 0);
v___x_282_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_a_276_, v_defns_281_);
return v___x_282_;
}
case 6:
{
lean_object* v_types_283_; uint8_t v___x_284_; 
v_types_283_ = lean_ctor_get(v_d_275_, 2);
v___x_284_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_a_276_, v_types_283_);
return v___x_284_;
}
default: 
{
lean_object* v_val_285_; lean_object* v_toConstantVal_286_; lean_object* v_value_287_; lean_object* v_type_288_; uint8_t v___x_289_; uint8_t v___x_290_; 
v_val_285_ = lean_ctor_get(v_d_275_, 0);
v_toConstantVal_286_ = lean_ctor_get(v_val_285_, 0);
v_value_287_ = lean_ctor_get(v_val_285_, 1);
v_type_288_ = lean_ctor_get(v_toConstantVal_286_, 2);
v___x_289_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_a_276_, v_type_288_);
v___x_290_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v___x_289_, v_value_287_);
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___boxed(lean_object* v_d_291_, lean_object* v_a_292_){
_start:
{
uint8_t v_a_boxed_293_; uint8_t v_res_294_; lean_object* v_r_295_; 
v_a_boxed_293_ = lean_unbox(v_a_292_);
v_res_294_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(v_d_291_, v_a_boxed_293_);
lean_dec(v_d_291_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSyntheticSorry(lean_object* v_d_296_){
_start:
{
uint8_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 0;
v___x_298_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(v_d_296_, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSyntheticSorry___boxed(lean_object* v_d_299_){
_start:
{
uint8_t v_res_300_; lean_object* v_r_301_; 
v_res_300_ = l_Lean_Declaration_hasSyntheticSorry(v_d_299_);
lean_dec(v_d_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(uint8_t v_r_302_, lean_object* v_e_303_){
_start:
{
if (v_r_302_ == 0)
{
uint8_t v___x_304_; 
v___x_304_ = l_Lean_Expr_hasNonSyntheticSorry(v_e_303_);
return v___x_304_;
}
else
{
return v_r_302_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0___boxed(lean_object* v_r_305_, lean_object* v_e_306_){
_start:
{
uint8_t v_r_boxed_307_; uint8_t v_res_308_; lean_object* v_r_309_; 
v_r_boxed_307_ = lean_unbox(v_r_305_);
v_res_308_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_r_boxed_307_, v_e_306_);
lean_dec_ref(v_e_306_);
v_r_309_ = lean_box(v_res_308_);
return v_r_309_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(uint8_t v_x_310_, lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
return v_x_310_;
}
else
{
lean_object* v_head_312_; lean_object* v_toConstantVal_313_; lean_object* v_tail_314_; lean_object* v_value_315_; lean_object* v_type_316_; uint8_t v___x_317_; uint8_t v___x_318_; 
v_head_312_ = lean_ctor_get(v_x_311_, 0);
v_toConstantVal_313_ = lean_ctor_get(v_head_312_, 0);
v_tail_314_ = lean_ctor_get(v_x_311_, 1);
v_value_315_ = lean_ctor_get(v_head_312_, 1);
v_type_316_ = lean_ctor_get(v_toConstantVal_313_, 2);
v___x_317_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_x_310_, v_type_316_);
v___x_318_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v___x_317_, v_value_315_);
v_x_310_ = v___x_318_;
v_x_311_ = v_tail_314_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1___boxed(lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
uint8_t v_x_1024__boxed_322_; uint8_t v_res_323_; lean_object* v_r_324_; 
v_x_1024__boxed_322_ = lean_unbox(v_x_320_);
v_res_323_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_x_1024__boxed_322_, v_x_321_);
lean_dec(v_x_321_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(uint8_t v_x_325_, lean_object* v_x_326_){
_start:
{
if (lean_obj_tag(v_x_326_) == 0)
{
return v_x_325_;
}
else
{
if (v_x_325_ == 0)
{
lean_object* v_head_327_; lean_object* v_tail_328_; lean_object* v_type_329_; uint8_t v___x_330_; 
v_head_327_ = lean_ctor_get(v_x_326_, 0);
v_tail_328_ = lean_ctor_get(v_x_326_, 1);
v_type_329_ = lean_ctor_get(v_head_327_, 1);
v___x_330_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_329_);
v_x_325_ = v___x_330_;
v_x_326_ = v_tail_328_;
goto _start;
}
else
{
lean_object* v_tail_332_; 
v_tail_332_ = lean_ctor_get(v_x_326_, 1);
v_x_326_ = v_tail_332_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object* v_x_334_, lean_object* v_x_335_){
_start:
{
uint8_t v_x_1040__boxed_336_; uint8_t v_res_337_; lean_object* v_r_338_; 
v_x_1040__boxed_336_ = lean_unbox(v_x_334_);
v_res_337_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_336_, v_x_335_);
lean_dec(v_x_335_);
v_r_338_ = lean_box(v_res_337_);
return v_r_338_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(uint8_t v_x_339_, lean_object* v_x_340_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
return v_x_339_;
}
else
{
if (v_x_339_ == 0)
{
lean_object* v_head_341_; lean_object* v_tail_342_; lean_object* v_type_343_; uint8_t v___x_344_; uint8_t v___x_345_; 
v_head_341_ = lean_ctor_get(v_x_340_, 0);
v_tail_342_ = lean_ctor_get(v_x_340_, 1);
v_type_343_ = lean_ctor_get(v_head_341_, 1);
v___x_344_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_343_);
v___x_345_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v___x_344_, v_tail_342_);
return v___x_345_;
}
else
{
lean_object* v_tail_346_; uint8_t v___x_347_; 
v_tail_346_ = lean_ctor_get(v_x_340_, 1);
v___x_347_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_339_, v_tail_346_);
return v___x_347_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0___boxed(lean_object* v_x_348_, lean_object* v_x_349_){
_start:
{
uint8_t v_x_1058__boxed_350_; uint8_t v_res_351_; lean_object* v_r_352_; 
v_x_1058__boxed_350_ = lean_unbox(v_x_348_);
v_res_351_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v_x_1058__boxed_350_, v_x_349_);
lean_dec(v_x_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(uint8_t v_x_353_, lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 0)
{
return v_x_353_;
}
else
{
lean_object* v_head_355_; lean_object* v_tail_356_; lean_object* v_type_357_; lean_object* v_ctors_358_; uint8_t v___y_360_; 
v_head_355_ = lean_ctor_get(v_x_354_, 0);
v_tail_356_ = lean_ctor_get(v_x_354_, 1);
v_type_357_ = lean_ctor_get(v_head_355_, 1);
v_ctors_358_ = lean_ctor_get(v_head_355_, 2);
if (v_x_353_ == 0)
{
uint8_t v___x_363_; 
v___x_363_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_357_);
v___y_360_ = v___x_363_;
goto v___jp_359_;
}
else
{
v___y_360_ = v_x_353_;
goto v___jp_359_;
}
v___jp_359_:
{
uint8_t v___x_361_; 
v___x_361_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v___y_360_, v_ctors_358_);
v_x_353_ = v___x_361_;
v_x_354_ = v_tail_356_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object* v_x_364_, lean_object* v_x_365_){
_start:
{
uint8_t v_x_1076__boxed_366_; uint8_t v_res_367_; lean_object* v_r_368_; 
v_x_1076__boxed_366_ = lean_unbox(v_x_364_);
v_res_367_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_366_, v_x_365_);
lean_dec(v_x_365_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(uint8_t v_x_369_, lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
return v_x_369_;
}
else
{
lean_object* v_head_371_; lean_object* v_tail_372_; lean_object* v_type_373_; lean_object* v_ctors_374_; uint8_t v___y_376_; 
v_head_371_ = lean_ctor_get(v_x_370_, 0);
v_tail_372_ = lean_ctor_get(v_x_370_, 1);
v_type_373_ = lean_ctor_get(v_head_371_, 1);
v_ctors_374_ = lean_ctor_get(v_head_371_, 2);
if (v_x_369_ == 0)
{
uint8_t v___x_379_; 
v___x_379_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_373_);
v___y_376_ = v___x_379_;
goto v___jp_375_;
}
else
{
v___y_376_ = v_x_369_;
goto v___jp_375_;
}
v___jp_375_:
{
uint8_t v___x_377_; uint8_t v___x_378_; 
v___x_377_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v___y_376_, v_ctors_374_);
v___x_378_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(v___x_377_, v_tail_372_);
return v___x_378_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2___boxed(lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
uint8_t v_x_1096__boxed_382_; uint8_t v_res_383_; lean_object* v_r_384_; 
v_x_1096__boxed_382_ = lean_unbox(v_x_380_);
v_res_383_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_x_1096__boxed_382_, v_x_381_);
lean_dec(v_x_381_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(lean_object* v_d_385_, uint8_t v_a_386_){
_start:
{
switch(lean_obj_tag(v_d_385_))
{
case 0:
{
lean_object* v_val_387_; lean_object* v_toConstantVal_388_; lean_object* v_type_389_; uint8_t v___x_390_; 
v_val_387_ = lean_ctor_get(v_d_385_, 0);
v_toConstantVal_388_ = lean_ctor_get(v_val_387_, 0);
v_type_389_ = lean_ctor_get(v_toConstantVal_388_, 2);
v___x_390_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_a_386_, v_type_389_);
return v___x_390_;
}
case 4:
{
return v_a_386_;
}
case 5:
{
lean_object* v_defns_391_; uint8_t v___x_392_; 
v_defns_391_ = lean_ctor_get(v_d_385_, 0);
v___x_392_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_a_386_, v_defns_391_);
return v___x_392_;
}
case 6:
{
lean_object* v_types_393_; uint8_t v___x_394_; 
v_types_393_ = lean_ctor_get(v_d_385_, 2);
v___x_394_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_a_386_, v_types_393_);
return v___x_394_;
}
default: 
{
lean_object* v_val_395_; lean_object* v_toConstantVal_396_; lean_object* v_value_397_; lean_object* v_type_398_; uint8_t v___x_399_; uint8_t v___x_400_; 
v_val_395_ = lean_ctor_get(v_d_385_, 0);
v_toConstantVal_396_ = lean_ctor_get(v_val_395_, 0);
v_value_397_ = lean_ctor_get(v_val_395_, 1);
v_type_398_ = lean_ctor_get(v_toConstantVal_396_, 2);
v___x_399_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_a_386_, v_type_398_);
v___x_400_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v___x_399_, v_value_397_);
return v___x_400_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___boxed(lean_object* v_d_401_, lean_object* v_a_402_){
_start:
{
uint8_t v_a_boxed_403_; uint8_t v_res_404_; lean_object* v_r_405_; 
v_a_boxed_403_ = lean_unbox(v_a_402_);
v_res_404_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(v_d_401_, v_a_boxed_403_);
lean_dec(v_d_401_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasNonSyntheticSorry(lean_object* v_d_406_){
_start:
{
uint8_t v___x_407_; uint8_t v___x_408_; 
v___x_407_ = 0;
v___x_408_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(v_d_406_, v___x_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasNonSyntheticSorry___boxed(lean_object* v_d_409_){
_start:
{
uint8_t v_res_410_; lean_object* v_r_411_; 
v_res_410_ = l_Lean_Declaration_hasNonSyntheticSorry(v_d_409_);
lean_dec(v_d_409_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
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
