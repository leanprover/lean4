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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_OpenDecl_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
lean_object* v_ns_8_; lean_object* v_except_9_; lean_object* v___x_10_; 
v_ns_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_ns_8_);
v_except_9_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_except_9_);
lean_dec_ref(v_t_6_);
v___x_10_ = lean_apply_2(v_k_7_, v_ns_8_, v_except_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_OpenDecl_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_simple_elim___redArg(lean_object* v_t_23_, lean_object* v_simple_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_23_, v_simple_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_simple_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_simple_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_27_, v_simple_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_explicit_elim___redArg(lean_object* v_t_31_, lean_object* v_explicit_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_31_, v_explicit_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_explicit_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_explicit_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_OpenDecl_ctorElim___redArg(v_t_35_, v_explicit_37_);
return v___x_38_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqOpenDecl_beq_spec__0(lean_object* v_x_39_, lean_object* v_x_40_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
if (lean_obj_tag(v_x_40_) == 0)
{
uint8_t v___x_41_; 
v___x_41_ = 1;
return v___x_41_;
}
else
{
uint8_t v___x_42_; 
v___x_42_ = 0;
return v___x_42_;
}
}
else
{
if (lean_obj_tag(v_x_40_) == 0)
{
uint8_t v___x_43_; 
v___x_43_ = 0;
return v___x_43_;
}
else
{
lean_object* v_head_44_; lean_object* v_tail_45_; lean_object* v_head_46_; lean_object* v_tail_47_; uint8_t v___x_48_; 
v_head_44_ = lean_ctor_get(v_x_39_, 0);
v_tail_45_ = lean_ctor_get(v_x_39_, 1);
v_head_46_ = lean_ctor_get(v_x_40_, 0);
v_tail_47_ = lean_ctor_get(v_x_40_, 1);
v___x_48_ = lean_name_eq(v_head_44_, v_head_46_);
if (v___x_48_ == 0)
{
return v___x_48_;
}
else
{
v_x_39_ = v_tail_45_;
v_x_40_ = v_tail_47_;
goto _start;
}
}
}
}
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
LEAN_EXPORT uint8_t l_Lean_instBEqOpenDecl_beq(lean_object* v_x_54_, lean_object* v_x_55_){
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
LEAN_EXPORT lean_object* l_Lean_instBEqOpenDecl_beq___boxed(lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Lean_instBEqOpenDecl_beq(v_x_70_, v_x_71_);
lean_dec_ref(v_x_71_);
lean_dec_ref(v_x_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpenDecl_instToString___lam__0(lean_object* v___x_82_, lean_object* v___f_83_, lean_object* v_decl_84_){
_start:
{
if (lean_obj_tag(v_decl_84_) == 0)
{
lean_object* v_ns_85_; lean_object* v_except_86_; uint8_t v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_ns_85_ = lean_ctor_get(v_decl_84_, 0);
lean_inc(v_ns_85_);
v_except_86_ = lean_ctor_get(v_decl_84_, 1);
lean_inc_n(v_except_86_, 2);
lean_dec_ref(v_decl_84_);
v___x_87_ = 1;
v___x_88_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ns_85_, v___x_87_);
v___x_89_ = lean_box(0);
v___x_90_ = l_List_beq___redArg(v___x_82_, v_except_86_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = ((lean_object*)(l_Lean_OpenDecl_instToString___lam__0___closed__0));
v___x_92_ = l_List_toString___redArg(v___f_83_, v_except_86_);
v___x_93_ = lean_string_append(v___x_91_, v___x_92_);
lean_dec_ref(v___x_92_);
v___x_94_ = lean_string_append(v___x_88_, v___x_93_);
lean_dec_ref(v___x_93_);
return v___x_94_;
}
else
{
lean_dec(v_except_86_);
lean_dec_ref(v___f_83_);
return v___x_88_;
}
}
else
{
lean_object* v_id_95_; lean_object* v_declName_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
lean_dec_ref(v___f_83_);
lean_dec_ref(v___x_82_);
v_id_95_ = lean_ctor_get(v_decl_84_, 0);
lean_inc(v_id_95_);
v_declName_96_ = lean_ctor_get(v_decl_84_, 1);
lean_inc(v_declName_96_);
lean_dec_ref(v_decl_84_);
v___x_97_ = 1;
v___x_98_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_95_, v___x_97_);
v___x_99_ = ((lean_object*)(l_Lean_OpenDecl_instToString___lam__0___closed__1));
v___x_100_ = lean_string_append(v___x_98_, v___x_99_);
v___x_101_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_96_, v___x_97_);
v___x_102_ = lean_string_append(v___x_100_, v___x_101_);
lean_dec_ref(v___x_101_);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_removeRoot(lean_object* v_n_113_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = ((lean_object*)(l_Lean_rootNamespace));
v___x_115_ = lean_box(0);
v___x_116_ = l_Lean_Name_replacePrefix(v_n_113_, v___x_114_, v___x_115_);
return v___x_116_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Extra(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_OpenDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
