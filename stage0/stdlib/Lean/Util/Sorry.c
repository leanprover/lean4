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
uint8_t v___y_17_; lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_26_ = l_Lean_Expr_isAppOf(v_e_15_, v___x_25_);
if (v___x_26_ == 0)
{
v___y_17_ = v___x_26_;
goto v___jp_16_;
}
else
{
lean_object* v___x_27_; lean_object* v___x_28_; uint8_t v___x_29_; 
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = l_Lean_Expr_getAppNumArgs(v_e_15_);
v___x_29_ = lean_nat_dec_le(v___x_27_, v___x_28_);
lean_dec(v___x_28_);
v___y_17_ = v___x_29_;
goto v___jp_16_;
}
v___jp_16_:
{
if (v___y_17_ == 0)
{
return v___y_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = l_Lean_Expr_getAppNumArgs(v_e_15_);
v___x_20_ = lean_nat_sub(v___x_19_, v___x_18_);
lean_dec(v___x_19_);
v___x_21_ = lean_nat_sub(v___x_20_, v___x_18_);
lean_dec(v___x_20_);
v___x_22_ = l_Lean_Expr_getRevArg_x21(v_e_15_, v___x_21_);
v___x_23_ = ((lean_object*)(l_Lean_Expr_isSyntheticSorry___closed__2));
v___x_24_ = l_Lean_Expr_isConstOf(v___x_22_, v___x_23_);
lean_dec_ref(v___x_22_);
return v___x_24_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isSyntheticSorry___boxed(lean_object* v_e_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Lean_Expr_isSyntheticSorry(v_e_30_);
lean_dec_ref(v_e_30_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_isNonSyntheticSorry(lean_object* v_e_37_){
_start:
{
uint8_t v___y_39_; lean_object* v___x_47_; uint8_t v___x_48_; 
v___x_47_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_48_ = l_Lean_Expr_isAppOf(v_e_37_, v___x_47_);
if (v___x_48_ == 0)
{
v___y_39_ = v___x_48_;
goto v___jp_38_;
}
else
{
lean_object* v___x_49_; lean_object* v___x_50_; uint8_t v___x_51_; 
v___x_49_ = lean_unsigned_to_nat(2u);
v___x_50_ = l_Lean_Expr_getAppNumArgs(v_e_37_);
v___x_51_ = lean_nat_dec_le(v___x_49_, v___x_50_);
lean_dec(v___x_50_);
v___y_39_ = v___x_51_;
goto v___jp_38_;
}
v___jp_38_:
{
if (v___y_39_ == 0)
{
return v___y_39_;
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; uint8_t v___x_46_; 
v___x_40_ = lean_unsigned_to_nat(1u);
v___x_41_ = l_Lean_Expr_getAppNumArgs(v_e_37_);
v___x_42_ = lean_nat_sub(v___x_41_, v___x_40_);
lean_dec(v___x_41_);
v___x_43_ = lean_nat_sub(v___x_42_, v___x_40_);
lean_dec(v___x_42_);
v___x_44_ = l_Lean_Expr_getRevArg_x21(v_e_37_, v___x_43_);
v___x_45_ = ((lean_object*)(l_Lean_Expr_isNonSyntheticSorry___closed__1));
v___x_46_ = l_Lean_Expr_isConstOf(v___x_44_, v___x_45_);
lean_dec_ref(v___x_44_);
return v___x_46_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isNonSyntheticSorry___boxed(lean_object* v_e_52_){
_start:
{
uint8_t v_res_53_; lean_object* v_r_54_; 
v_res_53_ = l_Lean_Expr_isNonSyntheticSorry(v_e_52_);
lean_dec_ref(v_e_52_);
v_r_54_ = lean_box(v_res_53_);
return v_r_54_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry___lam__0(lean_object* v_x_55_){
_start:
{
lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_56_ = ((lean_object*)(l_Lean_Expr_isSorry___closed__1));
v___x_57_ = l_Lean_Expr_isConstOf(v_x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___lam__0___boxed(lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = l_Lean_Expr_hasSorry___lam__0(v_x_58_);
lean_dec_ref(v_x_58_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSorry(lean_object* v_e_62_){
_start:
{
lean_object* v___f_63_; lean_object* v___x_64_; 
v___f_63_ = ((lean_object*)(l_Lean_Expr_hasSorry___closed__0));
v___x_64_ = lean_find_expr(v___f_63_, v_e_62_);
if (lean_obj_tag(v___x_64_) == 0)
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
else
{
uint8_t v___x_66_; 
lean_dec_ref(v___x_64_);
v___x_66_ = 1;
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSorry___boxed(lean_object* v_e_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Lean_Expr_hasSorry(v_e_67_);
lean_dec_ref(v_e_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object* v_e_71_){
_start:
{
lean_object* v___f_72_; lean_object* v___x_73_; 
v___f_72_ = ((lean_object*)(l_Lean_Expr_hasSyntheticSorry___closed__0));
v___x_73_ = lean_find_expr(v___f_72_, v_e_71_);
if (lean_obj_tag(v___x_73_) == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 0;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
lean_dec_ref(v___x_73_);
v___x_75_ = 1;
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasSyntheticSorry___boxed(lean_object* v_e_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Lean_Expr_hasSyntheticSorry(v_e_76_);
lean_dec_ref(v_e_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasNonSyntheticSorry(lean_object* v_e_80_){
_start:
{
lean_object* v___f_81_; lean_object* v___x_82_; 
v___f_81_ = ((lean_object*)(l_Lean_Expr_hasNonSyntheticSorry___closed__0));
v___x_82_ = lean_find_expr(v___f_81_, v_e_80_);
if (lean_obj_tag(v___x_82_) == 0)
{
uint8_t v___x_83_; 
v___x_83_ = 0;
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
lean_dec_ref(v___x_82_);
v___x_84_ = 1;
return v___x_84_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasNonSyntheticSorry___boxed(lean_object* v_e_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Lean_Expr_hasNonSyntheticSorry(v_e_85_);
lean_dec_ref(v_e_85_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(uint8_t v_r_88_, lean_object* v_e_89_){
_start:
{
if (v_r_88_ == 0)
{
uint8_t v___x_90_; 
v___x_90_ = l_Lean_Expr_hasSorry(v_e_89_);
return v___x_90_;
}
else
{
return v_r_88_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0___boxed(lean_object* v_r_91_, lean_object* v_e_92_){
_start:
{
uint8_t v_r_boxed_93_; uint8_t v_res_94_; lean_object* v_r_95_; 
v_r_boxed_93_ = lean_unbox(v_r_91_);
v_res_94_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_r_boxed_93_, v_e_92_);
lean_dec_ref(v_e_92_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(uint8_t v_x_96_, lean_object* v_x_97_){
_start:
{
if (lean_obj_tag(v_x_97_) == 0)
{
return v_x_96_;
}
else
{
lean_object* v_head_98_; lean_object* v_toConstantVal_99_; lean_object* v_tail_100_; lean_object* v_value_101_; lean_object* v_type_102_; uint8_t v___x_103_; uint8_t v___x_104_; 
v_head_98_ = lean_ctor_get(v_x_97_, 0);
v_toConstantVal_99_ = lean_ctor_get(v_head_98_, 0);
v_tail_100_ = lean_ctor_get(v_x_97_, 1);
v_value_101_ = lean_ctor_get(v_head_98_, 1);
v_type_102_ = lean_ctor_get(v_toConstantVal_99_, 2);
v___x_103_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_x_96_, v_type_102_);
v___x_104_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v___x_103_, v_value_101_);
v_x_96_ = v___x_104_;
v_x_97_ = v_tail_100_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1___boxed(lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
uint8_t v_x_1024__boxed_108_; uint8_t v_res_109_; lean_object* v_r_110_; 
v_x_1024__boxed_108_ = lean_unbox(v_x_106_);
v_res_109_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_x_1024__boxed_108_, v_x_107_);
lean_dec(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(uint8_t v_x_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
return v_x_111_;
}
else
{
if (v_x_111_ == 0)
{
lean_object* v_head_113_; lean_object* v_tail_114_; lean_object* v_type_115_; uint8_t v___x_116_; 
v_head_113_ = lean_ctor_get(v_x_112_, 0);
v_tail_114_ = lean_ctor_get(v_x_112_, 1);
v_type_115_ = lean_ctor_get(v_head_113_, 1);
v___x_116_ = l_Lean_Expr_hasSorry(v_type_115_);
v_x_111_ = v___x_116_;
v_x_112_ = v_tail_114_;
goto _start;
}
else
{
lean_object* v_tail_118_; 
v_tail_118_ = lean_ctor_get(v_x_112_, 1);
v_x_112_ = v_tail_118_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1___boxed(lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
uint8_t v_x_1040__boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_x_1040__boxed_122_ = lean_unbox(v_x_120_);
v_res_123_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_122_, v_x_121_);
lean_dec(v_x_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(uint8_t v_x_125_, lean_object* v_x_126_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
return v_x_125_;
}
else
{
if (v_x_125_ == 0)
{
lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v_type_129_; uint8_t v___x_130_; uint8_t v___x_131_; 
v_head_127_ = lean_ctor_get(v_x_126_, 0);
v_tail_128_ = lean_ctor_get(v_x_126_, 1);
v_type_129_ = lean_ctor_get(v_head_127_, 1);
v___x_130_ = l_Lean_Expr_hasSorry(v_type_129_);
v___x_131_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v___x_130_, v_tail_128_);
return v___x_131_;
}
else
{
lean_object* v_tail_132_; uint8_t v___x_133_; 
v_tail_132_ = lean_ctor_get(v_x_126_, 1);
v___x_133_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0_spec__1(v_x_125_, v_tail_132_);
return v___x_133_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0___boxed(lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
uint8_t v_x_1058__boxed_136_; uint8_t v_res_137_; lean_object* v_r_138_; 
v_x_1058__boxed_136_ = lean_unbox(v_x_134_);
v_res_137_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v_x_1058__boxed_136_, v_x_135_);
lean_dec(v_x_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(uint8_t v_x_139_, lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_140_) == 0)
{
return v_x_139_;
}
else
{
lean_object* v_head_141_; lean_object* v_tail_142_; lean_object* v_type_143_; lean_object* v_ctors_144_; uint8_t v___y_146_; 
v_head_141_ = lean_ctor_get(v_x_140_, 0);
v_tail_142_ = lean_ctor_get(v_x_140_, 1);
v_type_143_ = lean_ctor_get(v_head_141_, 1);
v_ctors_144_ = lean_ctor_get(v_head_141_, 2);
if (v_x_139_ == 0)
{
uint8_t v___x_149_; 
v___x_149_ = l_Lean_Expr_hasSorry(v_type_143_);
v___y_146_ = v___x_149_;
goto v___jp_145_;
}
else
{
v___y_146_ = v_x_139_;
goto v___jp_145_;
}
v___jp_145_:
{
uint8_t v___x_147_; 
v___x_147_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v___y_146_, v_ctors_144_);
v_x_139_ = v___x_147_;
v_x_140_ = v_tail_142_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4___boxed(lean_object* v_x_150_, lean_object* v_x_151_){
_start:
{
uint8_t v_x_1076__boxed_152_; uint8_t v_res_153_; lean_object* v_r_154_; 
v_x_1076__boxed_152_ = lean_unbox(v_x_150_);
v_res_153_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_152_, v_x_151_);
lean_dec(v_x_151_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(uint8_t v_x_155_, lean_object* v_x_156_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
return v_x_155_;
}
else
{
lean_object* v_head_157_; lean_object* v_tail_158_; lean_object* v_type_159_; lean_object* v_ctors_160_; uint8_t v___y_162_; 
v_head_157_ = lean_ctor_get(v_x_156_, 0);
v_tail_158_ = lean_ctor_get(v_x_156_, 1);
v_type_159_ = lean_ctor_get(v_head_157_, 1);
v_ctors_160_ = lean_ctor_get(v_head_157_, 2);
if (v_x_155_ == 0)
{
uint8_t v___x_165_; 
v___x_165_ = l_Lean_Expr_hasSorry(v_type_159_);
v___y_162_ = v___x_165_;
goto v___jp_161_;
}
else
{
v___y_162_ = v_x_155_;
goto v___jp_161_;
}
v___jp_161_:
{
uint8_t v___x_163_; uint8_t v___x_164_; 
v___x_163_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__0(v___y_162_, v_ctors_160_);
v___x_164_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2_spec__4(v___x_163_, v_tail_158_);
return v___x_164_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2___boxed(lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
uint8_t v_x_1096__boxed_168_; uint8_t v_res_169_; lean_object* v_r_170_; 
v_x_1096__boxed_168_ = lean_unbox(v_x_166_);
v_res_169_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_x_1096__boxed_168_, v_x_167_);
lean_dec(v_x_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(lean_object* v_d_171_, uint8_t v_a_172_){
_start:
{
switch(lean_obj_tag(v_d_171_))
{
case 0:
{
lean_object* v_val_173_; lean_object* v_toConstantVal_174_; lean_object* v_type_175_; uint8_t v___x_176_; 
v_val_173_ = lean_ctor_get(v_d_171_, 0);
v_toConstantVal_174_ = lean_ctor_get(v_val_173_, 0);
v_type_175_ = lean_ctor_get(v_toConstantVal_174_, 2);
v___x_176_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_a_172_, v_type_175_);
return v___x_176_;
}
case 4:
{
return v_a_172_;
}
case 5:
{
lean_object* v_defns_177_; uint8_t v___x_178_; 
v_defns_177_ = lean_ctor_get(v_d_171_, 0);
v___x_178_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__1(v_a_172_, v_defns_177_);
return v___x_178_;
}
case 6:
{
lean_object* v_types_179_; uint8_t v___x_180_; 
v_types_179_ = lean_ctor_get(v_d_171_, 2);
v___x_180_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0_spec__2(v_a_172_, v_types_179_);
return v___x_180_;
}
default: 
{
lean_object* v_val_181_; lean_object* v_toConstantVal_182_; lean_object* v_value_183_; lean_object* v_type_184_; uint8_t v___x_185_; uint8_t v___x_186_; 
v_val_181_ = lean_ctor_get(v_d_171_, 0);
v_toConstantVal_182_ = lean_ctor_get(v_val_181_, 0);
v_value_183_ = lean_ctor_get(v_val_181_, 1);
v_type_184_ = lean_ctor_get(v_toConstantVal_182_, 2);
v___x_185_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v_a_172_, v_type_184_);
v___x_186_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___lam__0(v___x_185_, v_value_183_);
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0___boxed(lean_object* v_d_187_, lean_object* v_a_188_){
_start:
{
uint8_t v_a_boxed_189_; uint8_t v_res_190_; lean_object* v_r_191_; 
v_a_boxed_189_ = lean_unbox(v_a_188_);
v_res_190_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(v_d_187_, v_a_boxed_189_);
lean_dec(v_d_187_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSorry(lean_object* v_d_192_){
_start:
{
uint8_t v___x_193_; uint8_t v___x_194_; 
v___x_193_ = 0;
v___x_194_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSorry_spec__0(v_d_192_, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSorry___boxed(lean_object* v_d_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Lean_Declaration_hasSorry(v_d_195_);
lean_dec(v_d_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(uint8_t v_r_198_, lean_object* v_e_199_){
_start:
{
if (v_r_198_ == 0)
{
uint8_t v___x_200_; 
v___x_200_ = l_Lean_Expr_hasSyntheticSorry(v_e_199_);
return v___x_200_;
}
else
{
return v_r_198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0___boxed(lean_object* v_r_201_, lean_object* v_e_202_){
_start:
{
uint8_t v_r_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v_r_boxed_203_ = lean_unbox(v_r_201_);
v_res_204_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_r_boxed_203_, v_e_202_);
lean_dec_ref(v_e_202_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(uint8_t v_x_206_, lean_object* v_x_207_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
return v_x_206_;
}
else
{
lean_object* v_head_208_; lean_object* v_toConstantVal_209_; lean_object* v_tail_210_; lean_object* v_value_211_; lean_object* v_type_212_; uint8_t v___x_213_; uint8_t v___x_214_; 
v_head_208_ = lean_ctor_get(v_x_207_, 0);
v_toConstantVal_209_ = lean_ctor_get(v_head_208_, 0);
v_tail_210_ = lean_ctor_get(v_x_207_, 1);
v_value_211_ = lean_ctor_get(v_head_208_, 1);
v_type_212_ = lean_ctor_get(v_toConstantVal_209_, 2);
v___x_213_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_x_206_, v_type_212_);
v___x_214_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v___x_213_, v_value_211_);
v_x_206_ = v___x_214_;
v_x_207_ = v_tail_210_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1___boxed(lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
uint8_t v_x_1024__boxed_218_; uint8_t v_res_219_; lean_object* v_r_220_; 
v_x_1024__boxed_218_ = lean_unbox(v_x_216_);
v_res_219_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_x_1024__boxed_218_, v_x_217_);
lean_dec(v_x_217_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(uint8_t v_x_221_, lean_object* v_x_222_){
_start:
{
if (lean_obj_tag(v_x_222_) == 0)
{
return v_x_221_;
}
else
{
if (v_x_221_ == 0)
{
lean_object* v_head_223_; lean_object* v_tail_224_; lean_object* v_type_225_; uint8_t v___x_226_; 
v_head_223_ = lean_ctor_get(v_x_222_, 0);
v_tail_224_ = lean_ctor_get(v_x_222_, 1);
v_type_225_ = lean_ctor_get(v_head_223_, 1);
v___x_226_ = l_Lean_Expr_hasSyntheticSorry(v_type_225_);
v_x_221_ = v___x_226_;
v_x_222_ = v_tail_224_;
goto _start;
}
else
{
lean_object* v_tail_228_; 
v_tail_228_ = lean_ctor_get(v_x_222_, 1);
v_x_222_ = v_tail_228_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
uint8_t v_x_1040__boxed_232_; uint8_t v_res_233_; lean_object* v_r_234_; 
v_x_1040__boxed_232_ = lean_unbox(v_x_230_);
v_res_233_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_232_, v_x_231_);
lean_dec(v_x_231_);
v_r_234_ = lean_box(v_res_233_);
return v_r_234_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(uint8_t v_x_235_, lean_object* v_x_236_){
_start:
{
if (lean_obj_tag(v_x_236_) == 0)
{
return v_x_235_;
}
else
{
if (v_x_235_ == 0)
{
lean_object* v_head_237_; lean_object* v_tail_238_; lean_object* v_type_239_; uint8_t v___x_240_; uint8_t v___x_241_; 
v_head_237_ = lean_ctor_get(v_x_236_, 0);
v_tail_238_ = lean_ctor_get(v_x_236_, 1);
v_type_239_ = lean_ctor_get(v_head_237_, 1);
v___x_240_ = l_Lean_Expr_hasSyntheticSorry(v_type_239_);
v___x_241_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v___x_240_, v_tail_238_);
return v___x_241_;
}
else
{
lean_object* v_tail_242_; uint8_t v___x_243_; 
v_tail_242_ = lean_ctor_get(v_x_236_, 1);
v___x_243_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0_spec__1(v_x_235_, v_tail_242_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0___boxed(lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
uint8_t v_x_1058__boxed_246_; uint8_t v_res_247_; lean_object* v_r_248_; 
v_x_1058__boxed_246_ = lean_unbox(v_x_244_);
v_res_247_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v_x_1058__boxed_246_, v_x_245_);
lean_dec(v_x_245_);
v_r_248_ = lean_box(v_res_247_);
return v_r_248_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(uint8_t v_x_249_, lean_object* v_x_250_){
_start:
{
if (lean_obj_tag(v_x_250_) == 0)
{
return v_x_249_;
}
else
{
lean_object* v_head_251_; lean_object* v_tail_252_; lean_object* v_type_253_; lean_object* v_ctors_254_; uint8_t v___y_256_; 
v_head_251_ = lean_ctor_get(v_x_250_, 0);
v_tail_252_ = lean_ctor_get(v_x_250_, 1);
v_type_253_ = lean_ctor_get(v_head_251_, 1);
v_ctors_254_ = lean_ctor_get(v_head_251_, 2);
if (v_x_249_ == 0)
{
uint8_t v___x_259_; 
v___x_259_ = l_Lean_Expr_hasSyntheticSorry(v_type_253_);
v___y_256_ = v___x_259_;
goto v___jp_255_;
}
else
{
v___y_256_ = v_x_249_;
goto v___jp_255_;
}
v___jp_255_:
{
uint8_t v___x_257_; 
v___x_257_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v___y_256_, v_ctors_254_);
v_x_249_ = v___x_257_;
v_x_250_ = v_tail_252_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
uint8_t v_x_1076__boxed_262_; uint8_t v_res_263_; lean_object* v_r_264_; 
v_x_1076__boxed_262_ = lean_unbox(v_x_260_);
v_res_263_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_262_, v_x_261_);
lean_dec(v_x_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(uint8_t v_x_265_, lean_object* v_x_266_){
_start:
{
if (lean_obj_tag(v_x_266_) == 0)
{
return v_x_265_;
}
else
{
lean_object* v_head_267_; lean_object* v_tail_268_; lean_object* v_type_269_; lean_object* v_ctors_270_; uint8_t v___y_272_; 
v_head_267_ = lean_ctor_get(v_x_266_, 0);
v_tail_268_ = lean_ctor_get(v_x_266_, 1);
v_type_269_ = lean_ctor_get(v_head_267_, 1);
v_ctors_270_ = lean_ctor_get(v_head_267_, 2);
if (v_x_265_ == 0)
{
uint8_t v___x_275_; 
v___x_275_ = l_Lean_Expr_hasSyntheticSorry(v_type_269_);
v___y_272_ = v___x_275_;
goto v___jp_271_;
}
else
{
v___y_272_ = v_x_265_;
goto v___jp_271_;
}
v___jp_271_:
{
uint8_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__0(v___y_272_, v_ctors_270_);
v___x_274_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2_spec__4(v___x_273_, v_tail_268_);
return v___x_274_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2___boxed(lean_object* v_x_276_, lean_object* v_x_277_){
_start:
{
uint8_t v_x_1096__boxed_278_; uint8_t v_res_279_; lean_object* v_r_280_; 
v_x_1096__boxed_278_ = lean_unbox(v_x_276_);
v_res_279_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_x_1096__boxed_278_, v_x_277_);
lean_dec(v_x_277_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(lean_object* v_d_281_, uint8_t v_a_282_){
_start:
{
switch(lean_obj_tag(v_d_281_))
{
case 0:
{
lean_object* v_val_283_; lean_object* v_toConstantVal_284_; lean_object* v_type_285_; uint8_t v___x_286_; 
v_val_283_ = lean_ctor_get(v_d_281_, 0);
v_toConstantVal_284_ = lean_ctor_get(v_val_283_, 0);
v_type_285_ = lean_ctor_get(v_toConstantVal_284_, 2);
v___x_286_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_a_282_, v_type_285_);
return v___x_286_;
}
case 4:
{
return v_a_282_;
}
case 5:
{
lean_object* v_defns_287_; uint8_t v___x_288_; 
v_defns_287_ = lean_ctor_get(v_d_281_, 0);
v___x_288_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__1(v_a_282_, v_defns_287_);
return v___x_288_;
}
case 6:
{
lean_object* v_types_289_; uint8_t v___x_290_; 
v_types_289_ = lean_ctor_get(v_d_281_, 2);
v___x_290_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0_spec__2(v_a_282_, v_types_289_);
return v___x_290_;
}
default: 
{
lean_object* v_val_291_; lean_object* v_toConstantVal_292_; lean_object* v_value_293_; lean_object* v_type_294_; uint8_t v___x_295_; uint8_t v___x_296_; 
v_val_291_ = lean_ctor_get(v_d_281_, 0);
v_toConstantVal_292_ = lean_ctor_get(v_val_291_, 0);
v_value_293_ = lean_ctor_get(v_val_291_, 1);
v_type_294_ = lean_ctor_get(v_toConstantVal_292_, 2);
v___x_295_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v_a_282_, v_type_294_);
v___x_296_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___lam__0(v___x_295_, v_value_293_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0___boxed(lean_object* v_d_297_, lean_object* v_a_298_){
_start:
{
uint8_t v_a_boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v_a_boxed_299_ = lean_unbox(v_a_298_);
v_res_300_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(v_d_297_, v_a_boxed_299_);
lean_dec(v_d_297_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasSyntheticSorry(lean_object* v_d_302_){
_start:
{
uint8_t v___x_303_; uint8_t v___x_304_; 
v___x_303_ = 0;
v___x_304_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasSyntheticSorry_spec__0(v_d_302_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasSyntheticSorry___boxed(lean_object* v_d_305_){
_start:
{
uint8_t v_res_306_; lean_object* v_r_307_; 
v_res_306_ = l_Lean_Declaration_hasSyntheticSorry(v_d_305_);
lean_dec(v_d_305_);
v_r_307_ = lean_box(v_res_306_);
return v_r_307_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(uint8_t v_r_308_, lean_object* v_e_309_){
_start:
{
if (v_r_308_ == 0)
{
uint8_t v___x_310_; 
v___x_310_ = l_Lean_Expr_hasNonSyntheticSorry(v_e_309_);
return v___x_310_;
}
else
{
return v_r_308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0___boxed(lean_object* v_r_311_, lean_object* v_e_312_){
_start:
{
uint8_t v_r_boxed_313_; uint8_t v_res_314_; lean_object* v_r_315_; 
v_r_boxed_313_ = lean_unbox(v_r_311_);
v_res_314_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_r_boxed_313_, v_e_312_);
lean_dec_ref(v_e_312_);
v_r_315_ = lean_box(v_res_314_);
return v_r_315_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(uint8_t v_x_316_, lean_object* v_x_317_){
_start:
{
if (lean_obj_tag(v_x_317_) == 0)
{
return v_x_316_;
}
else
{
lean_object* v_head_318_; lean_object* v_toConstantVal_319_; lean_object* v_tail_320_; lean_object* v_value_321_; lean_object* v_type_322_; uint8_t v___x_323_; uint8_t v___x_324_; 
v_head_318_ = lean_ctor_get(v_x_317_, 0);
v_toConstantVal_319_ = lean_ctor_get(v_head_318_, 0);
v_tail_320_ = lean_ctor_get(v_x_317_, 1);
v_value_321_ = lean_ctor_get(v_head_318_, 1);
v_type_322_ = lean_ctor_get(v_toConstantVal_319_, 2);
v___x_323_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_x_316_, v_type_322_);
v___x_324_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v___x_323_, v_value_321_);
v_x_316_ = v___x_324_;
v_x_317_ = v_tail_320_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1___boxed(lean_object* v_x_326_, lean_object* v_x_327_){
_start:
{
uint8_t v_x_1024__boxed_328_; uint8_t v_res_329_; lean_object* v_r_330_; 
v_x_1024__boxed_328_ = lean_unbox(v_x_326_);
v_res_329_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_x_1024__boxed_328_, v_x_327_);
lean_dec(v_x_327_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(uint8_t v_x_331_, lean_object* v_x_332_){
_start:
{
if (lean_obj_tag(v_x_332_) == 0)
{
return v_x_331_;
}
else
{
if (v_x_331_ == 0)
{
lean_object* v_head_333_; lean_object* v_tail_334_; lean_object* v_type_335_; uint8_t v___x_336_; 
v_head_333_ = lean_ctor_get(v_x_332_, 0);
v_tail_334_ = lean_ctor_get(v_x_332_, 1);
v_type_335_ = lean_ctor_get(v_head_333_, 1);
v___x_336_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_335_);
v_x_331_ = v___x_336_;
v_x_332_ = v_tail_334_;
goto _start;
}
else
{
lean_object* v_tail_338_; 
v_tail_338_ = lean_ctor_get(v_x_332_, 1);
v_x_332_ = v_tail_338_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1___boxed(lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
uint8_t v_x_1040__boxed_342_; uint8_t v_res_343_; lean_object* v_r_344_; 
v_x_1040__boxed_342_ = lean_unbox(v_x_340_);
v_res_343_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_1040__boxed_342_, v_x_341_);
lean_dec(v_x_341_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(uint8_t v_x_345_, lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_346_) == 0)
{
return v_x_345_;
}
else
{
if (v_x_345_ == 0)
{
lean_object* v_head_347_; lean_object* v_tail_348_; lean_object* v_type_349_; uint8_t v___x_350_; uint8_t v___x_351_; 
v_head_347_ = lean_ctor_get(v_x_346_, 0);
v_tail_348_ = lean_ctor_get(v_x_346_, 1);
v_type_349_ = lean_ctor_get(v_head_347_, 1);
v___x_350_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_349_);
v___x_351_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v___x_350_, v_tail_348_);
return v___x_351_;
}
else
{
lean_object* v_tail_352_; uint8_t v___x_353_; 
v_tail_352_ = lean_ctor_get(v_x_346_, 1);
v___x_353_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0_spec__1(v_x_345_, v_tail_352_);
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0___boxed(lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
uint8_t v_x_1058__boxed_356_; uint8_t v_res_357_; lean_object* v_r_358_; 
v_x_1058__boxed_356_ = lean_unbox(v_x_354_);
v_res_357_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v_x_1058__boxed_356_, v_x_355_);
lean_dec(v_x_355_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(uint8_t v_x_359_, lean_object* v_x_360_){
_start:
{
if (lean_obj_tag(v_x_360_) == 0)
{
return v_x_359_;
}
else
{
lean_object* v_head_361_; lean_object* v_tail_362_; lean_object* v_type_363_; lean_object* v_ctors_364_; uint8_t v___y_366_; 
v_head_361_ = lean_ctor_get(v_x_360_, 0);
v_tail_362_ = lean_ctor_get(v_x_360_, 1);
v_type_363_ = lean_ctor_get(v_head_361_, 1);
v_ctors_364_ = lean_ctor_get(v_head_361_, 2);
if (v_x_359_ == 0)
{
uint8_t v___x_369_; 
v___x_369_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_363_);
v___y_366_ = v___x_369_;
goto v___jp_365_;
}
else
{
v___y_366_ = v_x_359_;
goto v___jp_365_;
}
v___jp_365_:
{
uint8_t v___x_367_; 
v___x_367_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v___y_366_, v_ctors_364_);
v_x_359_ = v___x_367_;
v_x_360_ = v_tail_362_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4___boxed(lean_object* v_x_370_, lean_object* v_x_371_){
_start:
{
uint8_t v_x_1076__boxed_372_; uint8_t v_res_373_; lean_object* v_r_374_; 
v_x_1076__boxed_372_ = lean_unbox(v_x_370_);
v_res_373_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(v_x_1076__boxed_372_, v_x_371_);
lean_dec(v_x_371_);
v_r_374_ = lean_box(v_res_373_);
return v_r_374_;
}
}
LEAN_EXPORT uint8_t l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(uint8_t v_x_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
return v_x_375_;
}
else
{
lean_object* v_head_377_; lean_object* v_tail_378_; lean_object* v_type_379_; lean_object* v_ctors_380_; uint8_t v___y_382_; 
v_head_377_ = lean_ctor_get(v_x_376_, 0);
v_tail_378_ = lean_ctor_get(v_x_376_, 1);
v_type_379_ = lean_ctor_get(v_head_377_, 1);
v_ctors_380_ = lean_ctor_get(v_head_377_, 2);
if (v_x_375_ == 0)
{
uint8_t v___x_385_; 
v___x_385_ = l_Lean_Expr_hasNonSyntheticSorry(v_type_379_);
v___y_382_ = v___x_385_;
goto v___jp_381_;
}
else
{
v___y_382_ = v_x_375_;
goto v___jp_381_;
}
v___jp_381_:
{
uint8_t v___x_383_; uint8_t v___x_384_; 
v___x_383_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__0(v___y_382_, v_ctors_380_);
v___x_384_ = l_List_foldlM___at___00List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2_spec__4(v___x_383_, v_tail_378_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2___boxed(lean_object* v_x_386_, lean_object* v_x_387_){
_start:
{
uint8_t v_x_1096__boxed_388_; uint8_t v_res_389_; lean_object* v_r_390_; 
v_x_1096__boxed_388_ = lean_unbox(v_x_386_);
v_res_389_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_x_1096__boxed_388_, v_x_387_);
lean_dec(v_x_387_);
v_r_390_ = lean_box(v_res_389_);
return v_r_390_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(lean_object* v_d_391_, uint8_t v_a_392_){
_start:
{
switch(lean_obj_tag(v_d_391_))
{
case 0:
{
lean_object* v_val_393_; lean_object* v_toConstantVal_394_; lean_object* v_type_395_; uint8_t v___x_396_; 
v_val_393_ = lean_ctor_get(v_d_391_, 0);
v_toConstantVal_394_ = lean_ctor_get(v_val_393_, 0);
v_type_395_ = lean_ctor_get(v_toConstantVal_394_, 2);
v___x_396_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_a_392_, v_type_395_);
return v___x_396_;
}
case 4:
{
return v_a_392_;
}
case 5:
{
lean_object* v_defns_397_; uint8_t v___x_398_; 
v_defns_397_ = lean_ctor_get(v_d_391_, 0);
v___x_398_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__1(v_a_392_, v_defns_397_);
return v___x_398_;
}
case 6:
{
lean_object* v_types_399_; uint8_t v___x_400_; 
v_types_399_ = lean_ctor_get(v_d_391_, 2);
v___x_400_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0_spec__2(v_a_392_, v_types_399_);
return v___x_400_;
}
default: 
{
lean_object* v_val_401_; lean_object* v_toConstantVal_402_; lean_object* v_value_403_; lean_object* v_type_404_; uint8_t v___x_405_; uint8_t v___x_406_; 
v_val_401_ = lean_ctor_get(v_d_391_, 0);
v_toConstantVal_402_ = lean_ctor_get(v_val_401_, 0);
v_value_403_ = lean_ctor_get(v_val_401_, 1);
v_type_404_ = lean_ctor_get(v_toConstantVal_402_, 2);
v___x_405_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v_a_392_, v_type_404_);
v___x_406_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___lam__0(v___x_405_, v_value_403_);
return v___x_406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0___boxed(lean_object* v_d_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_a_boxed_409_; uint8_t v_res_410_; lean_object* v_r_411_; 
v_a_boxed_409_ = lean_unbox(v_a_408_);
v_res_410_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(v_d_407_, v_a_boxed_409_);
lean_dec(v_d_407_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT uint8_t l_Lean_Declaration_hasNonSyntheticSorry(lean_object* v_d_412_){
_start:
{
uint8_t v___x_413_; uint8_t v___x_414_; 
v___x_413_ = 0;
v___x_414_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_hasNonSyntheticSorry_spec__0(v_d_412_, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_hasNonSyntheticSorry___boxed(lean_object* v_d_415_){
_start:
{
uint8_t v_res_416_; lean_object* v_r_417_; 
v_res_416_ = l_Lean_Declaration_hasNonSyntheticSorry(v_d_415_);
lean_dec(v_d_415_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
lean_object* runtime_initialize_Lean_Util_FindExpr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
