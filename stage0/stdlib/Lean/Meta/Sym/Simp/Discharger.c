// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Discharger
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.Meta.AppBuilder
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
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_getConfig___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
uint8_t v_contextDependent_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v_contextDependent_8_ = lean_ctor_get_uint8(v_t_6_, 0);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_box(v_contextDependent_8_);
v___x_10_ = lean_apply_1(v_k_7_, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v_proof_11_; uint8_t v_contextDependent_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v_proof_11_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_proof_11_);
v_contextDependent_12_ = lean_ctor_get_uint8(v_t_6_, sizeof(void*)*1);
lean_dec_ref(v_t_6_);
v___x_13_ = lean_box(v_contextDependent_12_);
v___x_14_ = lean_apply_2(v_k_7_, v_proof_11_, v___x_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim___redArg(lean_object* v_t_27_, lean_object* v_failed_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_27_, v_failed_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_failed_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_failed_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_31_, v_failed_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim___redArg(lean_object* v_t_35_, lean_object* v_solved_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_35_, v_solved_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_DischargeResult_solved_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_solved_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Meta_Sym_Simp_DischargeResult_ctorElim___redArg(v_t_39_, v_solved_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(lean_object* v_e_43_, lean_object* v_result_44_){
_start:
{
if (lean_obj_tag(v_result_44_) == 0)
{
uint8_t v_contextDependent_45_; lean_object* v___x_46_; 
lean_dec_ref(v_e_43_);
v_contextDependent_45_ = lean_ctor_get_uint8(v_result_44_, 1);
lean_dec_ref(v_result_44_);
v___x_46_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_46_, 0, v_contextDependent_45_);
return v___x_46_;
}
else
{
lean_object* v_e_x27_47_; lean_object* v_proof_48_; uint8_t v_contextDependent_49_; uint8_t v___x_50_; 
v_e_x27_47_ = lean_ctor_get(v_result_44_, 0);
lean_inc_ref(v_e_x27_47_);
v_proof_48_ = lean_ctor_get(v_result_44_, 1);
lean_inc_ref(v_proof_48_);
v_contextDependent_49_ = lean_ctor_get_uint8(v_result_44_, sizeof(void*)*2 + 1);
lean_dec_ref(v_result_44_);
v___x_50_ = l_Lean_Expr_isTrue(v_e_x27_47_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; 
lean_dec_ref(v_proof_48_);
lean_dec_ref(v_e_43_);
v___x_51_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_51_, 0, v_contextDependent_49_);
return v___x_51_;
}
else
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = l_Lean_Meta_mkOfEqTrueCore(v_e_43_, v_proof_48_);
v___x_53_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set_uint8(v___x_53_, sizeof(void*)*1, v_contextDependent_49_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(lean_object* v_p_54_, lean_object* v_e_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; 
lean_inc_ref(v_e_55_);
v___x_66_ = lean_apply_11(v_p_54_, v_e_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_, v_a_60_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, lean_box(0));
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_75_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_75_ == 0)
{
v___x_69_ = v___x_66_;
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
else
{
lean_inc(v_a_67_);
lean_dec(v___x_66_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_75_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(v_e_55_, v_a_67_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_71_);
v___x_73_ = v___x_69_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
else
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_83_; 
lean_dec_ref(v_e_55_);
v_a_76_ = lean_ctor_get(v___x_66_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v___x_66_);
if (v_isSharedCheck_83_ == 0)
{
v___x_78_ = v___x_66_;
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_66_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_83_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_81_; 
if (v_isShared_79_ == 0)
{
v___x_81_ = v___x_78_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_a_76_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc___boxed(lean_object* v_p_84_, lean_object* v_e_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Meta_Sym_Simp_mkDischargerFromSimproc(v_p_84_, v_e_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(lean_object* v_a_97_, lean_object* v_persistentCache_98_, lean_object* v_transientCache_99_, lean_object* v_funext_100_, lean_object* v_a_x3f_101_){
_start:
{
lean_object* v___x_103_; lean_object* v_numSteps_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_114_; 
v___x_103_ = lean_st_ref_take(v_a_97_);
v_numSteps_104_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; lean_object* v_unused_116_; lean_object* v_unused_117_; 
v_unused_115_ = lean_ctor_get(v___x_103_, 3);
lean_dec(v_unused_115_);
v_unused_116_ = lean_ctor_get(v___x_103_, 2);
lean_dec(v_unused_116_);
v_unused_117_ = lean_ctor_get(v___x_103_, 1);
lean_dec(v_unused_117_);
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_114_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_numSteps_104_);
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_114_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 3, v_funext_100_);
lean_ctor_set(v___x_106_, 2, v_transientCache_99_);
lean_ctor_set(v___x_106_, 1, v_persistentCache_98_);
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_numSteps_104_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_persistentCache_98_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_transientCache_99_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_funext_100_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_110_ = lean_st_ref_set(v_a_97_, v___x_109_);
v___x_111_ = lean_box(0);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0___boxed(lean_object* v_a_118_, lean_object* v_persistentCache_119_, lean_object* v_transientCache_120_, lean_object* v_funext_121_, lean_object* v_a_x3f_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_118_, v_persistentCache_119_, v_transientCache_120_, v_funext_121_, v_a_x3f_122_);
lean_dec(v_a_x3f_122_);
lean_dec(v_a_118_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf(lean_object* v_e_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Sym_Simp_getConfig___redArg(v_a_129_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_197_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_197_ == 0)
{
v___x_141_ = v___x_138_;
v_isShared_142_ = v_isSharedCheck_197_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_a_139_);
lean_dec(v___x_138_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_197_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v_maxDischargeDepth_143_; lean_object* v_config_144_; lean_object* v_initialLCtxSize_145_; lean_object* v_dischargeDepth_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_196_; 
v_maxDischargeDepth_143_ = lean_ctor_get(v_a_139_, 1);
lean_inc(v_maxDischargeDepth_143_);
lean_dec(v_a_139_);
v_config_144_ = lean_ctor_get(v_a_129_, 0);
v_initialLCtxSize_145_ = lean_ctor_get(v_a_129_, 1);
v_dischargeDepth_146_ = lean_ctor_get(v_a_129_, 2);
v_isSharedCheck_196_ = !lean_is_exclusive(v_a_129_);
if (v_isSharedCheck_196_ == 0)
{
v___x_148_ = v_a_129_;
v_isShared_149_ = v_isSharedCheck_196_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_dischargeDepth_146_);
lean_inc(v_initialLCtxSize_145_);
lean_inc(v_config_144_);
lean_dec(v_a_129_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_196_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
uint8_t v___x_150_; 
v___x_150_ = lean_nat_dec_lt(v_maxDischargeDepth_143_, v_dischargeDepth_146_);
lean_dec(v_maxDischargeDepth_143_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_persistentCache_154_; lean_object* v_transientCache_155_; lean_object* v_funext_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_160_; 
lean_del_object(v___x_141_);
v___x_151_ = lean_st_ref_get(v_a_130_);
v___x_152_ = lean_st_ref_get(v_a_130_);
v___x_153_ = lean_st_ref_get(v_a_130_);
v_persistentCache_154_ = lean_ctor_get(v___x_151_, 1);
lean_inc_ref(v_persistentCache_154_);
lean_dec(v___x_151_);
v_transientCache_155_ = lean_ctor_get(v___x_152_, 2);
lean_inc_ref(v_transientCache_155_);
lean_dec(v___x_152_);
v_funext_156_ = lean_ctor_get(v___x_153_, 3);
lean_inc_ref(v_funext_156_);
lean_dec(v___x_153_);
v___x_157_ = lean_unsigned_to_nat(1u);
v___x_158_ = lean_nat_add(v_dischargeDepth_146_, v___x_157_);
lean_dec(v_dischargeDepth_146_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 2, v___x_158_);
v___x_160_ = v___x_148_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_config_144_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_initialLCtxSize_145_);
lean_ctor_set(v_reuseFailAlloc_191_, 2, v___x_158_);
v___x_160_ = v_reuseFailAlloc_191_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_object* v___x_161_; 
lean_inc(v_a_130_);
lean_inc_ref(v_e_127_);
v___x_161_ = lean_sym_simp(v_e_127_, v_a_128_, v___x_160_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_179_; 
v_a_162_ = lean_ctor_get(v___x_161_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_161_);
if (v_isSharedCheck_179_ == 0)
{
v___x_164_ = v___x_161_;
v_isShared_165_ = v_isSharedCheck_179_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_161_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_179_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_168_; 
v___x_166_ = l___private_Lean_Meta_Sym_Simp_Discharger_0__Lean_Meta_Sym_Simp_resultToDischargeResult(v_e_127_, v_a_162_);
lean_inc_ref(v___x_166_);
if (v_isShared_165_ == 0)
{
lean_ctor_set_tag(v___x_164_, 1);
lean_ctor_set(v___x_164_, 0, v___x_166_);
v___x_168_ = v___x_164_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_166_);
v___x_168_ = v_reuseFailAlloc_178_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
lean_object* v___x_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
v___x_169_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_130_, v_persistentCache_154_, v_transientCache_155_, v_funext_156_, v___x_168_);
lean_dec_ref(v___x_168_);
lean_dec(v_a_130_);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_176_ == 0)
{
lean_object* v_unused_177_; 
v_unused_177_ = lean_ctor_get(v___x_169_, 0);
lean_dec(v_unused_177_);
v___x_171_ = v___x_169_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_dec(v___x_169_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_166_);
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_166_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v_e_127_);
v_a_180_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_a_180_);
lean_dec_ref(v___x_161_);
v___x_181_ = lean_box(0);
v___x_182_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf___lam__0(v_a_130_, v_persistentCache_154_, v_transientCache_155_, v_funext_156_, v___x_181_);
lean_dec(v_a_130_);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v___x_182_, 0);
lean_dec(v_unused_190_);
v___x_184_ = v___x_182_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_dec(v___x_182_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set_tag(v___x_184_, 1);
lean_ctor_set(v___x_184_, 0, v_a_180_);
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_180_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
}
else
{
lean_object* v___x_192_; lean_object* v___x_194_; 
lean_del_object(v___x_148_);
lean_dec(v_dischargeDepth_146_);
lean_dec(v_initialLCtxSize_145_);
lean_dec_ref(v_config_144_);
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec(v_a_128_);
lean_dec_ref(v_e_127_);
v___x_192_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0));
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 0, v___x_192_);
v___x_194_ = v___x_141_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_192_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec(v_a_136_);
lean_dec_ref(v_a_135_);
lean_dec(v_a_134_);
lean_dec_ref(v_a_133_);
lean_dec(v_a_132_);
lean_dec_ref(v_a_131_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_e_127_);
v_a_198_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_138_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_138_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeSimpSelf___boxed(lean_object* v_e_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Meta_Sym_Simp_dischargeSimpSelf(v_e_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg(){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeSimpSelf___closed__0));
v___x_220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___redArg___boxed(lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone(lean_object* v_x_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Meta_Sym_Simp_dischargeNone___redArg();
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object* v_x_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_Sym_Simp_dischargeNone(v_x_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_x_235_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(lean_object* v_e_250_, lean_object* v_as_251_, size_t v_sz_252_, size_t v_i_253_, lean_object* v_b_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
uint8_t v___x_260_; 
v___x_260_ = lean_usize_dec_lt(v_i_253_, v_sz_252_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec_ref(v_e_250_);
v___x_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_261_, 0, v_b_254_);
return v___x_261_;
}
else
{
lean_object* v_snd_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_312_; 
v_snd_262_ = lean_ctor_get(v_b_254_, 1);
v_isSharedCheck_312_ = !lean_is_exclusive(v_b_254_);
if (v_isSharedCheck_312_ == 0)
{
lean_object* v_unused_313_; 
v_unused_313_ = lean_ctor_get(v_b_254_, 0);
lean_dec(v_unused_313_);
v___x_264_ = v_b_254_;
v_isShared_265_ = v_isSharedCheck_312_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_snd_262_);
lean_dec(v_b_254_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_312_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_266_; lean_object* v_a_268_; lean_object* v_a_275_; 
v___x_266_ = lean_box(0);
v_a_275_ = lean_array_uget(v_as_251_, v_i_253_);
if (lean_obj_tag(v_a_275_) == 0)
{
v_a_268_ = v_snd_262_;
goto v___jp_267_;
}
else
{
lean_object* v_val_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_311_; 
v_val_276_ = lean_ctor_get(v_a_275_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v_a_275_);
if (v_isSharedCheck_311_ == 0)
{
v___x_278_ = v_a_275_;
v_isShared_279_ = v_isSharedCheck_311_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_val_276_);
lean_dec(v_a_275_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_311_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = lean_box(0);
v___x_281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_282_ = l_Lean_LocalDecl_isAuxDecl(v_val_276_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = l_Lean_LocalDecl_type(v_val_276_);
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc_ref(v_e_250_);
v___x_284_ = l_Lean_Meta_isExprDefEq(v___x_283_, v_e_250_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_302_; 
v_a_285_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_302_ == 0)
{
v___x_287_ = v___x_284_;
v_isShared_288_ = v_isSharedCheck_302_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_284_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_302_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
uint8_t v___x_289_; 
v___x_289_ = lean_unbox(v_a_285_);
if (v___x_289_ == 0)
{
lean_del_object(v___x_287_);
lean_dec(v_a_285_);
lean_del_object(v___x_278_);
lean_dec(v_val_276_);
lean_dec(v_snd_262_);
v_a_268_ = v___x_281_;
goto v___jp_267_;
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_294_; 
lean_del_object(v___x_264_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec_ref(v_e_250_);
v___x_290_ = l_Lean_LocalDecl_toExpr(v_val_276_);
v___x_291_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_unbox(v_a_285_);
lean_dec(v_a_285_);
lean_ctor_set_uint8(v___x_291_, sizeof(void*)*1, v___x_292_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 0, v___x_291_);
v___x_294_ = v___x_278_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_291_);
v___x_294_ = v_reuseFailAlloc_301_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_280_);
v___x_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v_snd_262_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_297_);
v___x_299_ = v___x_287_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_del_object(v___x_278_);
lean_dec(v_val_276_);
lean_del_object(v___x_264_);
lean_dec(v_snd_262_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
lean_dec_ref(v_e_250_);
v_a_303_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_284_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_284_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
else
{
lean_del_object(v___x_278_);
lean_dec(v_val_276_);
lean_dec(v_snd_262_);
v_a_268_ = v___x_281_;
goto v___jp_267_;
}
}
}
v___jp_267_:
{
lean_object* v___x_270_; 
if (v_isShared_265_ == 0)
{
lean_ctor_set(v___x_264_, 1, v_a_268_);
lean_ctor_set(v___x_264_, 0, v___x_266_);
v___x_270_ = v___x_264_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_a_268_);
v___x_270_ = v_reuseFailAlloc_274_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
size_t v___x_271_; size_t v___x_272_; 
v___x_271_ = ((size_t)1ULL);
v___x_272_ = lean_usize_add(v_i_253_, v___x_271_);
v_i_253_ = v___x_272_;
v_b_254_ = v___x_270_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_e_314_, lean_object* v_as_315_, lean_object* v_sz_316_, lean_object* v_i_317_, lean_object* v_b_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
size_t v_sz_boxed_324_; size_t v_i_boxed_325_; lean_object* v_res_326_; 
v_sz_boxed_324_ = lean_unbox_usize(v_sz_316_);
lean_dec(v_sz_316_);
v_i_boxed_325_ = lean_unbox_usize(v_i_317_);
lean_dec(v_i_317_);
v_res_326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_314_, v_as_315_, v_sz_boxed_324_, v_i_boxed_325_, v_b_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec_ref(v_as_315_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(lean_object* v_e_327_, lean_object* v_as_328_, size_t v_sz_329_, size_t v_i_330_, lean_object* v_b_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_usize_dec_lt(v_i_330_, v_sz_329_);
if (v___x_342_ == 0)
{
lean_object* v___x_343_; 
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec_ref(v_e_327_);
v___x_343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_343_, 0, v_b_331_);
return v___x_343_;
}
else
{
lean_object* v_snd_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_394_; 
v_snd_344_ = lean_ctor_get(v_b_331_, 1);
v_isSharedCheck_394_ = !lean_is_exclusive(v_b_331_);
if (v_isSharedCheck_394_ == 0)
{
lean_object* v_unused_395_; 
v_unused_395_ = lean_ctor_get(v_b_331_, 0);
lean_dec(v_unused_395_);
v___x_346_ = v_b_331_;
v_isShared_347_ = v_isSharedCheck_394_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_snd_344_);
lean_dec(v_b_331_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_394_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_348_; lean_object* v_a_350_; lean_object* v_a_357_; 
v___x_348_ = lean_box(0);
v_a_357_ = lean_array_uget(v_as_328_, v_i_330_);
if (lean_obj_tag(v_a_357_) == 0)
{
v_a_350_ = v_snd_344_;
goto v___jp_349_;
}
else
{
lean_object* v_val_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_393_; 
v_val_358_ = lean_ctor_get(v_a_357_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v_a_357_);
if (v_isSharedCheck_393_ == 0)
{
v___x_360_ = v_a_357_;
v_isShared_361_ = v_isSharedCheck_393_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_val_358_);
lean_dec(v_a_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_393_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_box(0);
v___x_363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg___closed__0));
v___x_364_ = l_Lean_LocalDecl_isAuxDecl(v_val_358_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = l_Lean_LocalDecl_type(v_val_358_);
lean_inc(v___y_340_);
lean_inc_ref(v___y_339_);
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc_ref(v_e_327_);
v___x_366_ = l_Lean_Meta_isExprDefEq(v___x_365_, v_e_327_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_384_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_384_ == 0)
{
v___x_369_ = v___x_366_;
v_isShared_370_ = v_isSharedCheck_384_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_dec(v___x_366_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_384_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
uint8_t v___x_371_; 
v___x_371_ = lean_unbox(v_a_367_);
if (v___x_371_ == 0)
{
lean_del_object(v___x_369_);
lean_dec(v_a_367_);
lean_del_object(v___x_360_);
lean_dec(v_val_358_);
lean_dec(v_snd_344_);
v_a_350_ = v___x_363_;
goto v___jp_349_;
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_376_; 
lean_del_object(v___x_346_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec_ref(v_e_327_);
v___x_372_ = l_Lean_LocalDecl_toExpr(v_val_358_);
v___x_373_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_373_, 0, v___x_372_);
v___x_374_ = lean_unbox(v_a_367_);
lean_dec(v_a_367_);
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*1, v___x_374_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v___x_373_);
v___x_376_ = v___x_360_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_373_);
v___x_376_ = v_reuseFailAlloc_383_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v___x_362_);
v___x_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v_snd_344_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 0, v___x_379_);
v___x_381_ = v___x_369_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
lean_del_object(v___x_360_);
lean_dec(v_val_358_);
lean_del_object(v___x_346_);
lean_dec(v_snd_344_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec_ref(v_e_327_);
v_a_385_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_366_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_366_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_del_object(v___x_360_);
lean_dec(v_val_358_);
lean_dec(v_snd_344_);
v_a_350_ = v___x_363_;
goto v___jp_349_;
}
}
}
v___jp_349_:
{
lean_object* v___x_352_; 
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v_a_350_);
lean_ctor_set(v___x_346_, 0, v___x_348_);
v___x_352_ = v___x_346_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v___x_348_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_a_350_);
v___x_352_ = v_reuseFailAlloc_356_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((size_t)1ULL);
v___x_354_ = lean_usize_add(v_i_330_, v___x_353_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_327_, v_as_328_, v_sz_329_, v___x_354_, v___x_352_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
return v___x_355_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1___boxed(lean_object* v_e_396_, lean_object* v_as_397_, lean_object* v_sz_398_, lean_object* v_i_399_, lean_object* v_b_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
size_t v_sz_boxed_411_; size_t v_i_boxed_412_; lean_object* v_res_413_; 
v_sz_boxed_411_ = lean_unbox_usize(v_sz_398_);
lean_dec(v_sz_398_);
v_i_boxed_412_ = lean_unbox_usize(v_i_399_);
lean_dec(v_i_399_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_396_, v_as_397_, v_sz_boxed_411_, v_i_boxed_412_, v_b_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v_as_397_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_e_417_, lean_object* v_as_418_, size_t v_sz_419_, size_t v_i_420_, lean_object* v_b_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = lean_usize_dec_lt(v_i_420_, v_sz_419_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec_ref(v_e_417_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_b_421_);
return v___x_428_;
}
else
{
lean_object* v_snd_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_480_; 
v_snd_429_ = lean_ctor_get(v_b_421_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_b_421_);
if (v_isSharedCheck_480_ == 0)
{
lean_object* v_unused_481_; 
v_unused_481_ = lean_ctor_get(v_b_421_, 0);
lean_dec(v_unused_481_);
v___x_431_ = v_b_421_;
v_isShared_432_ = v_isSharedCheck_480_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_snd_429_);
lean_dec(v_b_421_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_480_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v_a_435_; lean_object* v_a_442_; 
v___x_433_ = lean_box(0);
v_a_442_ = lean_array_uget(v_as_418_, v_i_420_);
if (lean_obj_tag(v_a_442_) == 0)
{
v_a_435_ = v_snd_429_;
goto v___jp_434_;
}
else
{
lean_object* v_val_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_479_; 
v_val_443_ = lean_ctor_get(v_a_442_, 0);
v_isSharedCheck_479_ = !lean_is_exclusive(v_a_442_);
if (v_isSharedCheck_479_ == 0)
{
v___x_445_ = v_a_442_;
v_isShared_446_ = v_isSharedCheck_479_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_val_443_);
lean_dec(v_a_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_479_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_447_ = lean_box(0);
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_449_ = l_Lean_LocalDecl_isAuxDecl(v_val_443_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = l_Lean_LocalDecl_type(v_val_443_);
lean_inc(v___y_425_);
lean_inc_ref(v___y_424_);
lean_inc(v___y_423_);
lean_inc_ref(v___y_422_);
lean_inc_ref(v_e_417_);
v___x_451_ = l_Lean_Meta_isExprDefEq(v___x_450_, v_e_417_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
if (lean_obj_tag(v___x_451_) == 0)
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_470_; 
v_a_452_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_470_ == 0)
{
v___x_454_ = v___x_451_;
v_isShared_455_ = v_isSharedCheck_470_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_451_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_470_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
uint8_t v___x_456_; 
v___x_456_ = lean_unbox(v_a_452_);
if (v___x_456_ == 0)
{
lean_del_object(v___x_454_);
lean_dec(v_a_452_);
lean_del_object(v___x_445_);
lean_dec(v_val_443_);
lean_dec(v_snd_429_);
v_a_435_ = v___x_448_;
goto v___jp_434_;
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; lean_object* v___x_461_; 
lean_del_object(v___x_431_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec_ref(v_e_417_);
v___x_457_ = l_Lean_LocalDecl_toExpr(v_val_443_);
v___x_458_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_458_, 0, v___x_457_);
v___x_459_ = lean_unbox(v_a_452_);
lean_dec(v_a_452_);
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v___x_459_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v___x_458_);
v___x_461_ = v___x_445_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_458_);
v___x_461_ = v_reuseFailAlloc_469_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_447_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
v___x_464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_snd_429_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 0, v___x_465_);
v___x_467_ = v___x_454_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
}
else
{
lean_object* v_a_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_478_; 
lean_del_object(v___x_445_);
lean_dec(v_val_443_);
lean_del_object(v___x_431_);
lean_dec(v_snd_429_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec_ref(v_e_417_);
v_a_471_ = lean_ctor_get(v___x_451_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v___x_451_);
if (v_isSharedCheck_478_ == 0)
{
v___x_473_ = v___x_451_;
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_a_471_);
lean_dec(v___x_451_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_478_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_476_; 
if (v_isShared_474_ == 0)
{
v___x_476_ = v___x_473_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
else
{
lean_del_object(v___x_445_);
lean_dec(v_val_443_);
lean_dec(v_snd_429_);
v_a_435_ = v___x_448_;
goto v___jp_434_;
}
}
}
v___jp_434_:
{
lean_object* v___x_437_; 
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v_a_435_);
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_437_ = v___x_431_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_a_435_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
size_t v___x_438_; size_t v___x_439_; 
v___x_438_ = ((size_t)1ULL);
v___x_439_ = lean_usize_add(v_i_420_, v___x_438_);
v_i_420_ = v___x_439_;
v_b_421_ = v___x_437_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_e_482_, lean_object* v_as_483_, lean_object* v_sz_484_, lean_object* v_i_485_, lean_object* v_b_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
size_t v_sz_boxed_492_; size_t v_i_boxed_493_; lean_object* v_res_494_; 
v_sz_boxed_492_ = lean_unbox_usize(v_sz_484_);
lean_dec(v_sz_484_);
v_i_boxed_493_ = lean_unbox_usize(v_i_485_);
lean_dec(v_i_485_);
v_res_494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_482_, v_as_483_, v_sz_boxed_492_, v_i_boxed_493_, v_b_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec_ref(v_as_483_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(lean_object* v_e_495_, lean_object* v_as_496_, size_t v_sz_497_, size_t v_i_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_lt(v_i_498_, v_sz_497_);
if (v___x_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec_ref(v_e_495_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v_b_499_);
return v___x_511_;
}
else
{
lean_object* v_snd_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_563_; 
v_snd_512_ = lean_ctor_get(v_b_499_, 1);
v_isSharedCheck_563_ = !lean_is_exclusive(v_b_499_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v_b_499_, 0);
lean_dec(v_unused_564_);
v___x_514_ = v_b_499_;
v_isShared_515_ = v_isSharedCheck_563_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snd_512_);
lean_dec(v_b_499_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_563_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v_a_518_; lean_object* v_a_525_; 
v___x_516_ = lean_box(0);
v_a_525_ = lean_array_uget(v_as_496_, v_i_498_);
if (lean_obj_tag(v_a_525_) == 0)
{
v_a_518_ = v_snd_512_;
goto v___jp_517_;
}
else
{
lean_object* v_val_526_; lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_562_; 
v_val_526_ = lean_ctor_get(v_a_525_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_a_525_);
if (v_isSharedCheck_562_ == 0)
{
v___x_528_ = v_a_525_;
v_isShared_529_ = v_isSharedCheck_562_;
goto v_resetjp_527_;
}
else
{
lean_inc(v_val_526_);
lean_dec(v_a_525_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_562_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_530_ = lean_box(0);
v___x_531_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg___closed__0));
v___x_532_ = l_Lean_LocalDecl_isAuxDecl(v_val_526_);
if (v___x_532_ == 0)
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = l_Lean_LocalDecl_type(v_val_526_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
lean_inc_ref(v_e_495_);
v___x_534_ = l_Lean_Meta_isExprDefEq(v___x_533_, v_e_495_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_553_; 
v_a_535_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_553_ == 0)
{
v___x_537_ = v___x_534_;
v_isShared_538_ = v_isSharedCheck_553_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_534_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_553_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
uint8_t v___x_539_; 
v___x_539_ = lean_unbox(v_a_535_);
if (v___x_539_ == 0)
{
lean_del_object(v___x_537_);
lean_dec(v_a_535_);
lean_del_object(v___x_528_);
lean_dec(v_val_526_);
lean_dec(v_snd_512_);
v_a_518_ = v___x_531_;
goto v___jp_517_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; lean_object* v___x_544_; 
lean_del_object(v___x_514_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec_ref(v_e_495_);
v___x_540_ = l_Lean_LocalDecl_toExpr(v_val_526_);
v___x_541_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_541_, 0, v___x_540_);
v___x_542_ = lean_unbox(v_a_535_);
lean_dec(v_a_535_);
lean_ctor_set_uint8(v___x_541_, sizeof(void*)*1, v___x_542_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_541_);
v___x_544_ = v___x_528_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_541_);
v___x_544_ = v_reuseFailAlloc_552_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_550_; 
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v___x_530_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
v___x_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v_snd_512_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_548_);
v___x_550_ = v___x_537_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v___x_548_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
else
{
lean_object* v_a_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_561_; 
lean_del_object(v___x_528_);
lean_dec(v_val_526_);
lean_del_object(v___x_514_);
lean_dec(v_snd_512_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec_ref(v_e_495_);
v_a_554_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_561_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_561_ == 0)
{
v___x_556_ = v___x_534_;
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_a_554_);
lean_dec(v___x_534_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_561_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_559_; 
if (v_isShared_557_ == 0)
{
v___x_559_ = v___x_556_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_a_554_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
}
}
else
{
lean_del_object(v___x_528_);
lean_dec(v_val_526_);
lean_dec(v_snd_512_);
v_a_518_ = v___x_531_;
goto v___jp_517_;
}
}
}
v___jp_517_:
{
lean_object* v___x_520_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v_a_518_);
lean_ctor_set(v___x_514_, 0, v___x_516_);
v___x_520_ = v___x_514_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_516_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_a_518_);
v___x_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
size_t v___x_521_; size_t v___x_522_; lean_object* v___x_523_; 
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_498_, v___x_521_);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_495_, v_as_496_, v_sz_497_, v___x_522_, v___x_520_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
return v___x_523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2___boxed(lean_object* v_e_565_, lean_object* v_as_566_, lean_object* v_sz_567_, lean_object* v_i_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
size_t v_sz_boxed_580_; size_t v_i_boxed_581_; lean_object* v_res_582_; 
v_sz_boxed_580_ = lean_unbox_usize(v_sz_567_);
lean_dec(v_sz_567_);
v_i_boxed_581_ = lean_unbox_usize(v_i_568_);
lean_dec(v_i_568_);
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_565_, v_as_566_, v_sz_boxed_580_, v_i_boxed_581_, v_b_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_574_);
lean_dec_ref(v___y_573_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v_as_566_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(lean_object* v_e_583_, lean_object* v_inh_584_, lean_object* v_n_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
if (lean_obj_tag(v_n_585_) == 0)
{
lean_object* v_cs_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_631_; 
v_cs_597_ = lean_ctor_get(v_n_585_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v_n_585_);
if (v_isSharedCheck_631_ == 0)
{
v___x_599_ = v_n_585_;
v_isShared_600_ = v_isSharedCheck_631_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_cs_597_);
lean_dec(v_n_585_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_631_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; size_t v_sz_603_; size_t v___x_604_; lean_object* v___x_605_; 
v___x_601_ = lean_box(0);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v_b_586_);
v_sz_603_ = lean_array_size(v_cs_597_);
v___x_604_ = ((size_t)0ULL);
v___x_605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_e_583_, v_inh_584_, v_cs_597_, v_sz_603_, v___x_604_, v___x_602_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec_ref(v_cs_597_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_622_; 
v_a_606_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_622_ == 0)
{
v___x_608_ = v___x_605_;
v_isShared_609_ = v_isSharedCheck_622_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_605_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_622_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v_fst_610_; 
v_fst_610_ = lean_ctor_get(v_a_606_, 0);
if (lean_obj_tag(v_fst_610_) == 0)
{
lean_object* v_snd_611_; lean_object* v___x_613_; 
v_snd_611_ = lean_ctor_get(v_a_606_, 1);
lean_inc(v_snd_611_);
lean_dec(v_a_606_);
if (v_isShared_600_ == 0)
{
lean_ctor_set_tag(v___x_599_, 1);
lean_ctor_set(v___x_599_, 0, v_snd_611_);
v___x_613_ = v___x_599_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_snd_611_);
v___x_613_ = v_reuseFailAlloc_617_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_615_; 
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v___x_613_);
v___x_615_ = v___x_608_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
}
else
{
lean_object* v_val_618_; lean_object* v___x_620_; 
lean_inc_ref(v_fst_610_);
lean_dec(v_a_606_);
lean_del_object(v___x_599_);
v_val_618_ = lean_ctor_get(v_fst_610_, 0);
lean_inc(v_val_618_);
lean_dec_ref(v_fst_610_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 0, v_val_618_);
v___x_620_ = v___x_608_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_val_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_del_object(v___x_599_);
v_a_623_ = lean_ctor_get(v___x_605_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_605_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_605_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
}
else
{
lean_object* v_vs_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_666_; 
v_vs_632_ = lean_ctor_get(v_n_585_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v_n_585_);
if (v_isSharedCheck_666_ == 0)
{
v___x_634_ = v_n_585_;
v_isShared_635_ = v_isSharedCheck_666_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_vs_632_);
lean_dec(v_n_585_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_666_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; size_t v_sz_638_; size_t v___x_639_; lean_object* v___x_640_; 
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_b_586_);
v_sz_638_ = lean_array_size(v_vs_632_);
v___x_639_ = ((size_t)0ULL);
v___x_640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2(v_e_583_, v_vs_632_, v_sz_638_, v___x_639_, v___x_637_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec_ref(v_vs_632_);
if (lean_obj_tag(v___x_640_) == 0)
{
lean_object* v_a_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_657_; 
v_a_641_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_657_ == 0)
{
v___x_643_ = v___x_640_;
v_isShared_644_ = v_isSharedCheck_657_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_a_641_);
lean_dec(v___x_640_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_657_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_fst_645_; 
v_fst_645_ = lean_ctor_get(v_a_641_, 0);
if (lean_obj_tag(v_fst_645_) == 0)
{
lean_object* v_snd_646_; lean_object* v___x_648_; 
v_snd_646_ = lean_ctor_get(v_a_641_, 1);
lean_inc(v_snd_646_);
lean_dec(v_a_641_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v_snd_646_);
v___x_648_ = v___x_634_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_snd_646_);
v___x_648_ = v_reuseFailAlloc_652_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
lean_object* v___x_650_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_648_);
v___x_650_ = v___x_643_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
lean_object* v_val_653_; lean_object* v___x_655_; 
lean_inc_ref(v_fst_645_);
lean_dec(v_a_641_);
lean_del_object(v___x_634_);
v_val_653_ = lean_ctor_get(v_fst_645_, 0);
lean_inc(v_val_653_);
lean_dec_ref(v_fst_645_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v_val_653_);
v___x_655_ = v___x_643_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_val_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
else
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_665_; 
lean_del_object(v___x_634_);
v_a_658_ = lean_ctor_get(v___x_640_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_665_ == 0)
{
v___x_660_ = v___x_640_;
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_640_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_665_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_663_; 
if (v_isShared_661_ == 0)
{
v___x_663_ = v___x_660_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(lean_object* v_e_667_, lean_object* v_inh_668_, lean_object* v_as_669_, size_t v_sz_670_, size_t v_i_671_, lean_object* v_b_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
uint8_t v___x_683_; 
v___x_683_ = lean_usize_dec_lt(v_i_671_, v_sz_670_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec_ref(v_e_667_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v_b_672_);
return v___x_684_;
}
else
{
lean_object* v_snd_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_719_; 
v_snd_685_ = lean_ctor_get(v_b_672_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_b_672_);
if (v_isSharedCheck_719_ == 0)
{
lean_object* v_unused_720_; 
v_unused_720_ = lean_ctor_get(v_b_672_, 0);
lean_dec(v_unused_720_);
v___x_687_ = v_b_672_;
v_isShared_688_ = v_isSharedCheck_719_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snd_685_);
lean_dec(v_b_672_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_719_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_a_689_; lean_object* v___x_690_; 
v_a_689_ = lean_array_uget_borrowed(v_as_669_, v_i_671_);
lean_inc(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v_snd_685_);
lean_inc(v_a_689_);
lean_inc_ref(v_e_667_);
v___x_690_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_e_667_, v_inh_668_, v_a_689_, v_snd_685_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_710_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_710_ == 0)
{
v___x_693_ = v___x_690_;
v_isShared_694_ = v_isSharedCheck_710_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_710_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
if (lean_obj_tag(v_a_691_) == 0)
{
lean_object* v___x_695_; lean_object* v___x_697_; 
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec_ref(v_e_667_);
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v_a_691_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_695_);
v___x_697_ = v___x_687_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_snd_685_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 0, v___x_697_);
v___x_699_ = v___x_693_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
lean_del_object(v___x_693_);
lean_dec(v_snd_685_);
v_a_702_ = lean_ctor_get(v_a_691_, 0);
lean_inc(v_a_702_);
lean_dec_ref(v_a_691_);
v___x_703_ = lean_box(0);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v_a_702_);
lean_ctor_set(v___x_687_, 0, v___x_703_);
v___x_705_ = v___x_687_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_709_, 1, v_a_702_);
v___x_705_ = v_reuseFailAlloc_709_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
size_t v___x_706_; size_t v___x_707_; 
v___x_706_ = ((size_t)1ULL);
v___x_707_ = lean_usize_add(v_i_671_, v___x_706_);
v_i_671_ = v___x_707_;
v_b_672_ = v___x_705_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_del_object(v___x_687_);
lean_dec(v_snd_685_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v___y_678_);
lean_dec_ref(v_e_667_);
v_a_711_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_690_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_690_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1___boxed(lean_object* v_e_721_, lean_object* v_inh_722_, lean_object* v_as_723_, lean_object* v_sz_724_, lean_object* v_i_725_, lean_object* v_b_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
size_t v_sz_boxed_737_; size_t v_i_boxed_738_; lean_object* v_res_739_; 
v_sz_boxed_737_ = lean_unbox_usize(v_sz_724_);
lean_dec(v_sz_724_);
v_i_boxed_738_ = lean_unbox_usize(v_i_725_);
lean_dec(v_i_725_);
v_res_739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__1(v_e_721_, v_inh_722_, v_as_723_, v_sz_boxed_737_, v_i_boxed_738_, v_b_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v_as_723_);
lean_dec_ref(v_inh_722_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0___boxed(lean_object* v_e_740_, lean_object* v_inh_741_, lean_object* v_n_742_, lean_object* v_b_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_e_740_, v_inh_741_, v_n_742_, v_b_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v_inh_741_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(lean_object* v_e_755_, lean_object* v_t_756_, lean_object* v_init_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_root_768_; lean_object* v_tail_769_; lean_object* v___x_770_; 
v_root_768_ = lean_ctor_get(v_t_756_, 0);
lean_inc_ref(v_root_768_);
v_tail_769_ = lean_ctor_get(v_t_756_, 1);
lean_inc_ref(v_tail_769_);
lean_dec_ref(v_t_756_);
lean_inc(v___y_766_);
lean_inc_ref(v___y_765_);
lean_inc(v___y_764_);
lean_inc_ref(v___y_763_);
lean_inc_ref(v_init_757_);
lean_inc_ref(v_e_755_);
v___x_770_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0(v_e_755_, v_init_757_, v_root_768_, v_init_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec_ref(v_init_757_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_807_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_807_ == 0)
{
v___x_773_ = v___x_770_;
v_isShared_774_ = v_isSharedCheck_807_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_770_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_807_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
if (lean_obj_tag(v_a_771_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; 
lean_dec_ref(v_tail_769_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v_e_755_);
v_a_775_ = lean_ctor_get(v_a_771_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v_a_771_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v_a_775_);
v___x_777_ = v___x_773_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v___x_781_; size_t v_sz_782_; size_t v___x_783_; lean_object* v___x_784_; 
lean_del_object(v___x_773_);
v_a_779_ = lean_ctor_get(v_a_771_, 0);
lean_inc(v_a_779_);
lean_dec_ref(v_a_771_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v_a_779_);
v_sz_782_ = lean_array_size(v_tail_769_);
v___x_783_ = ((size_t)0ULL);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1(v_e_755_, v_tail_769_, v_sz_782_, v___x_783_, v___x_781_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec_ref(v_tail_769_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_798_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_798_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_798_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_798_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_fst_789_; 
v_fst_789_ = lean_ctor_get(v_a_785_, 0);
if (lean_obj_tag(v_fst_789_) == 0)
{
lean_object* v_snd_790_; lean_object* v___x_792_; 
v_snd_790_ = lean_ctor_get(v_a_785_, 1);
lean_inc(v_snd_790_);
lean_dec(v_a_785_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_snd_790_);
v___x_792_ = v___x_787_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_snd_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
else
{
lean_object* v_val_794_; lean_object* v___x_796_; 
lean_inc_ref(v_fst_789_);
lean_dec(v_a_785_);
v_val_794_ = lean_ctor_get(v_fst_789_, 0);
lean_inc(v_val_794_);
lean_dec_ref(v_fst_789_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v_val_794_);
v___x_796_ = v___x_787_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_val_794_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
v_a_799_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_784_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_784_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_tail_769_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v_e_755_);
v_a_808_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_770_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_770_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0___boxed(lean_object* v_e_816_, lean_object* v_t_817_, lean_object* v_init_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_816_, v_t_817_, v_init_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_823_);
lean_dec_ref(v___y_822_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption(lean_object* v_e_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_lctx_846_; lean_object* v_decls_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_lctx_846_ = lean_ctor_get(v_a_841_, 2);
v_decls_847_ = lean_ctor_get(v_lctx_846_, 1);
lean_inc_ref(v_decls_847_);
v___x_848_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__0));
v___x_849_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0(v_e_835_, v_decls_847_, v___x_848_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_863_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_863_ == 0)
{
v___x_852_ = v___x_849_;
v_isShared_853_ = v_isSharedCheck_863_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_863_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v_fst_854_; 
v_fst_854_ = lean_ctor_get(v_a_850_, 0);
lean_inc(v_fst_854_);
lean_dec(v_a_850_);
if (lean_obj_tag(v_fst_854_) == 0)
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_dischargeAssumption___closed__1));
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_855_);
v___x_857_ = v___x_852_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
else
{
lean_object* v_val_859_; lean_object* v___x_861_; 
v_val_859_ = lean_ctor_get(v_fst_854_, 0);
lean_inc(v_val_859_);
lean_dec_ref(v_fst_854_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v_val_859_);
v___x_861_ = v___x_852_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_val_859_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_849_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_849_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_dischargeAssumption___boxed(lean_object* v_e_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Meta_Sym_Simp_dischargeAssumption(v_e_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(lean_object* v_e_884_, lean_object* v_as_885_, size_t v_sz_886_, size_t v_i_887_, lean_object* v_b_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___redArg(v_e_884_, v_as_885_, v_sz_886_, v_i_887_, v_b_888_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4___boxed(lean_object* v_e_900_, lean_object* v_as_901_, lean_object* v_sz_902_, lean_object* v_i_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
size_t v_sz_boxed_915_; size_t v_i_boxed_916_; lean_object* v_res_917_; 
v_sz_boxed_915_ = lean_unbox_usize(v_sz_902_);
lean_dec(v_sz_902_);
v_i_boxed_916_ = lean_unbox_usize(v_i_903_);
lean_dec(v_i_903_);
v_res_917_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__1_spec__4(v_e_900_, v_as_901_, v_sz_boxed_915_, v_i_boxed_916_, v_b_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v_as_901_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(lean_object* v_e_918_, lean_object* v_as_919_, size_t v_sz_920_, size_t v_i_921_, lean_object* v_b_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___redArg(v_e_918_, v_as_919_, v_sz_920_, v_i_921_, v_b_922_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_e_934_, lean_object* v_as_935_, lean_object* v_sz_936_, lean_object* v_i_937_, lean_object* v_b_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
size_t v_sz_boxed_949_; size_t v_i_boxed_950_; lean_object* v_res_951_; 
v_sz_boxed_949_ = lean_unbox_usize(v_sz_936_);
lean_dec(v_sz_936_);
v_i_boxed_950_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_res_951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Sym_Simp_dischargeAssumption_spec__0_spec__0_spec__2_spec__3(v_e_934_, v_as_935_, v_sz_boxed_949_, v_i_boxed_950_, v_b_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v_as_935_);
return v_res_951_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Discharger(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
}
#ifdef __cplusplus
}
#endif
