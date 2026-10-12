// Lean compiler output
// Module: Lean.Data.OpenDecl
// Imports: public import Init.Data.ToString.Name public import Init.Data.ToString.Extra
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
lean_object* l_Lean_Name_instToString___lam__0(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t l_List_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_simple_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_simple_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_explicit_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_explicit_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqOpenDecl_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqOpenDecl_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqOpenDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqOpenDecl_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqOpenDecl___closed__0 = (const lean_object*)&l_Lean_instBEqOpenDecl___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqOpenDecl = (const lean_object*)&l_Lean_instBEqOpenDecl___closed__0_value;
static const lean_ctor_object l_Lean_OpenDecl_instInhabited___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_OpenDecl_instInhabited___closed__0 = (const lean_object*)&l_Lean_OpenDecl_instInhabited___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_OpenDecl_instInhabited = (const lean_object*)&l_Lean_OpenDecl_instInhabited___closed__0_value;
static const lean_string_object l_Lean_OpenDecl_instToString___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " hiding "};
static const lean_object* l_Lean_OpenDecl_instToString___lam__0___closed__0 = (const lean_object*)&l_Lean_OpenDecl_instToString___lam__0___closed__0_value;
static const lean_string_object l_Lean_OpenDecl_instToString___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 3, .m_data = " → "};
static const lean_object* l_Lean_OpenDecl_instToString___lam__0___closed__1 = (const lean_object*)&l_Lean_OpenDecl_instToString___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_OpenDecl_instToString___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_OpenDecl_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_OpenDecl_instToString___closed__0 = (const lean_object*)&l_Lean_OpenDecl_instToString___closed__0_value;
static const lean_closure_object l_Lean_OpenDecl_instToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_OpenDecl_instToString___closed__1 = (const lean_object*)&l_Lean_OpenDecl_instToString___closed__1_value;
static const lean_closure_object l_Lean_OpenDecl_instToString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_OpenDecl_instToString___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_OpenDecl_instToString___closed__1_value),((lean_object*)&l_Lean_OpenDecl_instToString___closed__0_value)} };
static const lean_object* l_Lean_OpenDecl_instToString___closed__2 = (const lean_object*)&l_Lean_OpenDecl_instToString___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_OpenDecl_instToString = (const lean_object*)&l_Lean_OpenDecl_instToString___closed__2_value;
static const lean_string_object l_Lean_rootNamespace___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_root_"};
static const lean_object* l_Lean_rootNamespace___closed__0 = (const lean_object*)&l_Lean_rootNamespace___closed__0_value;
static const lean_ctor_object l_Lean_rootNamespace___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_rootNamespace___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 175, 53, 50, 212, 152, 178, 8)}};
static const lean_object* l_Lean_rootNamespace___closed__1 = (const lean_object*)&l_Lean_rootNamespace___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_rootNamespace = (const lean_object*)&l_Lean_rootNamespace___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_removeRoot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_OpenDecl_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
lean_object* v_ns_7_; lean_object* v_except_8_; lean_object* v___x_9_; 
v_ns_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_ns_7_);
v_except_8_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_except_8_);
lean_dec_ref(v_t_5_);
v___x_9_ = lean_apply_2(v_k_6_, v_ns_7_, v_except_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_OpenDecl_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_simple_elim___redArg(lean_object* v_t_22_, lean_object* v_simple_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_22_, v_simple_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_simple_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_simple_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_26_, v_simple_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_explicit_elim___redArg(lean_object* v_t_30_, lean_object* v_explicit_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_30_, v_explicit_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_explicit_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_explicit_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_34_, v_explicit_36_);
return v___x_37_;
}
}
uint8_t l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_38_) == 0)
{
if (lean_obj_tag(v_x_39_) == 0)
{
uint8_t v___x_40_; 
v___x_40_ = 1;
return v___x_40_;
}
else
{
uint8_t v___x_41_; 
v___x_41_ = 0;
return v___x_41_;
}
}
else
{
if (lean_obj_tag(v_x_39_) == 0)
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
else
{
lean_object* v_head_43_; lean_object* v_tail_44_; lean_object* v_head_45_; lean_object* v_tail_46_; uint8_t v___x_47_; 
v_head_43_ = lean_ctor_get(v_x_38_, 0);
v_tail_44_ = lean_ctor_get(v_x_38_, 1);
v_head_45_ = lean_ctor_get(v_x_39_, 0);
v_tail_46_ = lean_ctor_get(v_x_39_, 1);
v___x_47_ = lean_name_eq(v_head_43_, v_head_45_);
if (v___x_47_ == 0)
{
return v___x_47_;
}
else
{
v_x_38_ = v_tail_44_;
v_x_39_ = v_tail_46_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_38_ = stack[0].m_obj;
lean_object* v_x_39_ = stack[1].m_obj;
uint8_t v_res_49_;
v_res_49_ = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(v_x_38_, v_x_39_);
stack->m_num = v_res_49_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0___boxed(lean_object* v_x_50_, lean_object* v_x_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(v_x_50_, v_x_51_);
lean_dec(v_x_51_);
lean_dec(v_x_50_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
uint8_t l_Lean_instBEqOpenDecl_beq(lean_object* v_x_54_, lean_object* v_x_55_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
if (lean_obj_tag(v_x_55_) == 0)
{
lean_object* v_ns_56_; lean_object* v_except_57_; lean_object* v_ns_58_; lean_object* v_except_59_; uint8_t v___x_60_; 
v_ns_56_ = lean_ctor_get(v_x_54_, 0);
v_except_57_ = lean_ctor_get(v_x_54_, 1);
v_ns_58_ = lean_ctor_get(v_x_55_, 0);
v_except_59_ = lean_ctor_get(v_x_55_, 1);
v___x_60_ = lean_name_eq(v_ns_56_, v_ns_58_);
if (v___x_60_ == 0)
{
return v___x_60_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(v_except_57_, v_except_59_);
return v___x_61_;
}
}
else
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
else
{
if (lean_obj_tag(v_x_55_) == 1)
{
lean_object* v_id_63_; lean_object* v_declName_64_; lean_object* v_id_65_; lean_object* v_declName_66_; uint8_t v___x_67_; 
v_id_63_ = lean_ctor_get(v_x_54_, 0);
v_declName_64_ = lean_ctor_get(v_x_54_, 1);
v_id_65_ = lean_ctor_get(v_x_55_, 0);
v_declName_66_ = lean_ctor_get(v_x_55_, 1);
v___x_67_ = lean_name_eq(v_id_63_, v_id_65_);
if (v___x_67_ == 0)
{
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
v___x_68_ = lean_name_eq(v_declName_64_, v_declName_66_);
return v___x_68_;
}
}
else
{
uint8_t v___x_69_; 
v___x_69_ = 0;
return v___x_69_;
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqOpenDecl_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_54_ = stack[0].m_obj;
lean_object* v_x_55_ = stack[1].m_obj;
uint8_t v_res_70_;
v_res_70_ = l_Lean_instBEqOpenDecl_beq(v_x_54_, v_x_55_);
stack->m_num = v_res_70_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqOpenDecl_beq___boxed(lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Lean_instBEqOpenDecl_beq(v_x_71_, v_x_72_);
lean_dec_ref(v_x_72_);
lean_dec_ref(v_x_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_instToString___lam__0(lean_object* v___x_83_, lean_object* v___f_84_, lean_object* v_decl_85_){
_start:
{
if (lean_obj_tag(v_decl_85_) == 0)
{
lean_object* v_ns_86_; lean_object* v_except_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_ns_86_ = lean_ctor_get(v_decl_85_, 0);
lean_inc(v_ns_86_);
v_except_87_ = lean_ctor_get(v_decl_85_, 1);
lean_inc_n(v_except_87_, 2);
lean_dec_ref_known(v_decl_85_, 2);
v___x_88_ = 1;
v___x_89_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ns_86_, v___x_88_);
v___x_90_ = lean_box(0);
v___x_91_ = l_List_beq___redArg(v___x_83_, v_except_87_, v___x_90_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_92_ = ((lean_object*)(l_Lean_OpenDecl_instToString___lam__0___closed__0));
v___x_93_ = l_List_toString___redArg(v___f_84_, v_except_87_);
v___x_94_ = lean_string_append(v___x_92_, v___x_93_);
lean_dec_ref(v___x_93_);
v___x_95_ = lean_string_append(v___x_89_, v___x_94_);
lean_dec_ref(v___x_94_);
return v___x_95_;
}
else
{
lean_dec(v_except_87_);
lean_dec_ref(v___f_84_);
return v___x_89_;
}
}
else
{
lean_object* v_id_96_; lean_object* v_declName_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
lean_dec_ref(v___f_84_);
lean_dec_ref(v___x_83_);
v_id_96_ = lean_ctor_get(v_decl_85_, 0);
lean_inc(v_id_96_);
v_declName_97_ = lean_ctor_get(v_decl_85_, 1);
lean_inc(v_declName_97_);
lean_dec_ref_known(v_decl_85_, 2);
v___x_98_ = 1;
v___x_99_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_96_, v___x_98_);
v___x_100_ = ((lean_object*)(l_Lean_OpenDecl_instToString___lam__0___closed__1));
v___x_101_ = lean_string_append(v___x_99_, v___x_100_);
v___x_102_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_97_, v___x_98_);
v___x_103_ = lean_string_append(v___x_101_, v___x_102_);
lean_dec_ref(v___x_102_);
return v___x_103_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeRoot(lean_object* v_n_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = ((lean_object*)(l_Lean_rootNamespace));
v___x_116_ = lean_box(0);
v___x_117_ = l_Lean_Name_replacePrefix(v_n_114_, v___x_115_, v___x_116_);
return v___x_117_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_OpenDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_OpenDecl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_OpenDecl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_OpenDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_OpenDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_OpenDecl(builtin);
}
#ifdef __cplusplus
}
#endif
