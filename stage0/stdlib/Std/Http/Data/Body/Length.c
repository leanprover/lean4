// Lean compiler output
// Module: Std.Http.Data.Body.Length
// Imports: public import Init.Data.Repr
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_chunked_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_chunked_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_fixed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_fixed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Http_Body_instReprLength_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Std.Http.Body.Length.chunked"};
static const lean_object* l_Std_Http_Body_instReprLength_repr___closed__0 = (const lean_object*)&l_Std_Http_Body_instReprLength_repr___closed__0_value;
static const lean_ctor_object l_Std_Http_Body_instReprLength_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Body_instReprLength_repr___closed__0_value)}};
static const lean_object* l_Std_Http_Body_instReprLength_repr___closed__1 = (const lean_object*)&l_Std_Http_Body_instReprLength_repr___closed__1_value;
static lean_once_cell_t l_Std_Http_Body_instReprLength_repr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_instReprLength_repr___closed__2;
static lean_once_cell_t l_Std_Http_Body_instReprLength_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Http_Body_instReprLength_repr___closed__3;
static const lean_string_object l_Std_Http_Body_instReprLength_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Std.Http.Body.Length.fixed"};
static const lean_object* l_Std_Http_Body_instReprLength_repr___closed__4 = (const lean_object*)&l_Std_Http_Body_instReprLength_repr___closed__4_value;
static const lean_ctor_object l_Std_Http_Body_instReprLength_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Http_Body_instReprLength_repr___closed__4_value)}};
static const lean_object* l_Std_Http_Body_instReprLength_repr___closed__5 = (const lean_object*)&l_Std_Http_Body_instReprLength_repr___closed__5_value;
static const lean_ctor_object l_Std_Http_Body_instReprLength_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Http_Body_instReprLength_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Http_Body_instReprLength_repr___closed__6 = (const lean_object*)&l_Std_Http_Body_instReprLength_repr___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Http_Body_instReprLength_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instReprLength_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instReprLength___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instReprLength_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instReprLength___closed__0 = (const lean_object*)&l_Std_Http_Body_instReprLength___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instReprLength = (const lean_object*)&l_Std_Http_Body_instReprLength___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Body_instBEqLength_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqLength_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_Http_Body_instBEqLength___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Http_Body_instBEqLength_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Http_Body_instBEqLength___closed__0 = (const lean_object*)&l_Std_Http_Body_instBEqLength___closed__0_value;
LEAN_EXPORT const lean_object* l_Std_Http_Body_instBEqLength = (const lean_object*)&l_Std_Http_Body_instBEqLength___closed__0_value;
LEAN_EXPORT uint8_t l_Std_Http_Body_Length_isChunked(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_isChunked___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Http_Body_Length_isFixed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_isFixed___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorIdx(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_Http_Body_Length_ctorIdx(v_x_4_);
lean_dec(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
return v_k_7_;
}
else
{
lean_object* v_n_8_; lean_object* v___x_9_; 
v_n_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_n_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_n_8_);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Std_Http_Body_Length_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_chunked_elim___redArg(lean_object* v_t_22_, lean_object* v_chunked_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_22_, v_chunked_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_chunked_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_chunked_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_26_, v_chunked_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_fixed_elim___redArg(lean_object* v_t_30_, lean_object* v_fixed_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_30_, v_fixed_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_fixed_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_fixed_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_34_, v_fixed_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Std_Http_Body_instReprLength_repr___closed__2(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(2u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Std_Http_Body_instReprLength_repr___closed__3(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(1u);
v___x_44_ = lean_nat_to_int(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instReprLength_repr(lean_object* v_x_51_, lean_object* v_prec_52_){
_start:
{
lean_object* v___y_54_; 
if (lean_obj_tag(v_x_51_) == 0)
{
lean_object* v___x_60_; uint8_t v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(1024u);
v___x_61_ = lean_nat_dec_le(v___x_60_, v_prec_52_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; 
v___x_62_ = lean_obj_once(&l_Std_Http_Body_instReprLength_repr___closed__2, &l_Std_Http_Body_instReprLength_repr___closed__2_once, _init_l_Std_Http_Body_instReprLength_repr___closed__2);
v___y_54_ = v___x_62_;
goto v___jp_53_;
}
else
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&l_Std_Http_Body_instReprLength_repr___closed__3, &l_Std_Http_Body_instReprLength_repr___closed__3_once, _init_l_Std_Http_Body_instReprLength_repr___closed__3);
v___y_54_ = v___x_63_;
goto v___jp_53_;
}
}
else
{
lean_object* v_n_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_84_; 
v_n_64_ = lean_ctor_get(v_x_51_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_51_);
if (v_isSharedCheck_84_ == 0)
{
v___x_66_ = v_x_51_;
v_isShared_67_ = v_isSharedCheck_84_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_n_64_);
lean_dec(v_x_51_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_84_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v___y_69_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(1024u);
v___x_81_ = lean_nat_dec_le(v___x_80_, v_prec_52_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Std_Http_Body_instReprLength_repr___closed__2, &l_Std_Http_Body_instReprLength_repr___closed__2_once, _init_l_Std_Http_Body_instReprLength_repr___closed__2);
v___y_69_ = v___x_82_;
goto v___jp_68_;
}
else
{
lean_object* v___x_83_; 
v___x_83_ = lean_obj_once(&l_Std_Http_Body_instReprLength_repr___closed__3, &l_Std_Http_Body_instReprLength_repr___closed__3_once, _init_l_Std_Http_Body_instReprLength_repr___closed__3);
v___y_69_ = v___x_83_;
goto v___jp_68_;
}
v___jp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_70_ = ((lean_object*)(l_Std_Http_Body_instReprLength_repr___closed__6));
v___x_71_ = l_Nat_reprFast(v_n_64_);
if (v_isShared_67_ == 0)
{
lean_ctor_set_tag(v___x_66_, 3);
lean_ctor_set(v___x_66_, 0, v___x_71_);
v___x_73_ = v___x_66_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_79_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_70_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
lean_inc(v___y_69_);
v___x_75_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_75_, 0, v___y_69_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = 0;
v___x_77_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_77_, 0, v___x_75_);
lean_ctor_set_uint8(v___x_77_, sizeof(void*)*1, v___x_76_);
v___x_78_ = l_Repr_addAppParen(v___x_77_, v_prec_52_);
return v___x_78_;
}
}
}
}
v___jp_53_:
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_55_ = ((lean_object*)(l_Std_Http_Body_instReprLength_repr___closed__1));
lean_inc(v___y_54_);
v___x_56_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_56_, 0, v___y_54_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = 0;
v___x_58_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_58_, 0, v___x_56_);
lean_ctor_set_uint8(v___x_58_, sizeof(void*)*1, v___x_57_);
v___x_59_ = l_Repr_addAppParen(v___x_58_, v_prec_52_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instReprLength_repr___boxed(lean_object* v_x_85_, lean_object* v_prec_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Std_Http_Body_instReprLength_repr(v_x_85_, v_prec_86_);
lean_dec(v_prec_86_);
return v_res_87_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Body_instBEqLength_beq(lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
if (lean_obj_tag(v_x_91_) == 0)
{
uint8_t v___x_92_; 
v___x_92_ = 1;
return v___x_92_;
}
else
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
}
else
{
if (lean_obj_tag(v_x_91_) == 1)
{
lean_object* v_n_94_; lean_object* v_n_95_; uint8_t v___x_96_; 
v_n_94_ = lean_ctor_get(v_x_90_, 0);
v_n_95_ = lean_ctor_get(v_x_91_, 0);
v___x_96_ = lean_nat_dec_eq(v_n_94_, v_n_95_);
return v___x_96_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instBEqLength_beq___boxed(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
uint8_t v_res_100_; lean_object* v_r_101_; 
v_res_100_ = l_Std_Http_Body_instBEqLength_beq(v_x_98_, v_x_99_);
lean_dec(v_x_99_);
lean_dec(v_x_98_);
v_r_101_ = lean_box(v_res_100_);
return v_r_101_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Body_Length_isChunked(lean_object* v_x_104_){
_start:
{
if (lean_obj_tag(v_x_104_) == 0)
{
uint8_t v___x_105_; 
v___x_105_ = 1;
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_isChunked___boxed(lean_object* v_x_107_){
_start:
{
uint8_t v_res_108_; lean_object* v_r_109_; 
v_res_108_ = l_Std_Http_Body_Length_isChunked(v_x_107_);
lean_dec(v_x_107_);
v_r_109_ = lean_box(v_res_108_);
return v_r_109_;
}
}
LEAN_EXPORT uint8_t l_Std_Http_Body_Length_isFixed(lean_object* v_x_110_){
_start:
{
if (lean_obj_tag(v_x_110_) == 1)
{
uint8_t v___x_111_; 
v___x_111_ = 1;
return v___x_111_;
}
else
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_isFixed___boxed(lean_object* v_x_113_){
_start:
{
uint8_t v_res_114_; lean_object* v_r_115_; 
v_res_114_ = l_Std_Http_Body_Length_isFixed(v_x_113_);
lean_dec(v_x_113_);
v_r_115_ = lean_box(v_res_114_);
return v_r_115_;
}
}
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Body_Length(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Http_Data_Body_Length(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Repr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Http_Data_Body_Length(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Repr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Http_Data_Body_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Http_Data_Body_Length(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Http_Data_Body_Length(builtin);
}
#ifdef __cplusplus
}
#endif
