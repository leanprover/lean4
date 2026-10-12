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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Http_Body_Length_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
lean_object* v_n_7_; lean_object* v___x_8_; 
v_n_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_n_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_n_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Http_Body_Length_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_chunked_elim___redArg(lean_object* v_t_21_, lean_object* v_chunked_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_21_, v_chunked_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_chunked_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_chunked_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_25_, v_chunked_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_fixed_elim___redArg(lean_object* v_t_29_, lean_object* v_fixed_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_29_, v_fixed_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_fixed_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_fixed_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_Http_Body_Length_ctorElim___redArg(v_t_33_, v_fixed_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_Http_Body_instReprLength_repr___closed__2(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_unsigned_to_nat(2u);
v___x_41_ = lean_nat_to_int(v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Std_Http_Body_instReprLength_repr___closed__3(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_to_int(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instReprLength_repr(lean_object* v_x_50_, lean_object* v_prec_51_){
_start:
{
lean_object* v___y_53_; 
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v___x_59_; uint8_t v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(1024u);
v___x_60_ = lean_nat_dec_le(v___x_59_, v_prec_51_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_obj_once(&l_Std_Http_Body_instReprLength_repr___closed__2, &l_Std_Http_Body_instReprLength_repr___closed__2_once, _init_l_Std_Http_Body_instReprLength_repr___closed__2);
v___y_53_ = v___x_61_;
goto v___jp_52_;
}
else
{
lean_object* v___x_62_; 
v___x_62_ = lean_obj_once(&l_Std_Http_Body_instReprLength_repr___closed__3, &l_Std_Http_Body_instReprLength_repr___closed__3_once, _init_l_Std_Http_Body_instReprLength_repr___closed__3);
v___y_53_ = v___x_62_;
goto v___jp_52_;
}
}
else
{
lean_object* v_n_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_83_; 
v_n_63_ = lean_ctor_get(v_x_50_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_83_ == 0)
{
v___x_65_ = v_x_50_;
v_isShared_66_ = v_isSharedCheck_83_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_n_63_);
lean_dec(v_x_50_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_83_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___y_68_; lean_object* v___x_79_; uint8_t v___x_80_; 
v___x_79_ = lean_unsigned_to_nat(1024u);
v___x_80_ = lean_nat_dec_le(v___x_79_, v_prec_51_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; 
v___x_81_ = lean_obj_once(&l_Std_Http_Body_instReprLength_repr___closed__2, &l_Std_Http_Body_instReprLength_repr___closed__2_once, _init_l_Std_Http_Body_instReprLength_repr___closed__2);
v___y_68_ = v___x_81_;
goto v___jp_67_;
}
else
{
lean_object* v___x_82_; 
v___x_82_ = lean_obj_once(&l_Std_Http_Body_instReprLength_repr___closed__3, &l_Std_Http_Body_instReprLength_repr___closed__3_once, _init_l_Std_Http_Body_instReprLength_repr___closed__3);
v___y_68_ = v___x_82_;
goto v___jp_67_;
}
v___jp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_72_; 
v___x_69_ = ((lean_object*)(l_Std_Http_Body_instReprLength_repr___closed__6));
v___x_70_ = l_Nat_reprFast(v_n_63_);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 3);
lean_ctor_set(v___x_65_, 0, v___x_70_);
v___x_72_ = v___x_65_;
goto v_reusejp_71_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_70_);
v___x_72_ = v_reuseFailAlloc_78_;
goto v_reusejp_71_;
}
v_reusejp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_69_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
lean_inc(v___y_68_);
v___x_74_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_74_, 0, v___y_68_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = 0;
v___x_76_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_75_);
v___x_77_ = l_Repr_addAppParen(v___x_76_, v_prec_51_);
return v___x_77_;
}
}
}
}
v___jp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_54_ = ((lean_object*)(l_Std_Http_Body_instReprLength_repr___closed__1));
lean_inc(v___y_53_);
v___x_55_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_55_, 0, v___y_53_);
lean_ctor_set(v___x_55_, 1, v___x_54_);
v___x_56_ = 0;
v___x_57_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_57_, 0, v___x_55_);
lean_ctor_set_uint8(v___x_57_, sizeof(void*)*1, v___x_56_);
v___x_58_ = l_Repr_addAppParen(v___x_57_, v_prec_51_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Http_Body_instReprLength_repr___boxed(lean_object* v_x_84_, lean_object* v_prec_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Std_Http_Body_instReprLength_repr(v_x_84_, v_prec_85_);
lean_dec(v_prec_85_);
return v_res_86_;
}
}
uint8_t l_Std_Http_Body_instBEqLength_beq(lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_89_) == 0)
{
if (lean_obj_tag(v_x_90_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 1;
return v___x_91_;
}
else
{
uint8_t v___x_92_; 
v___x_92_ = 0;
return v___x_92_;
}
}
else
{
if (lean_obj_tag(v_x_90_) == 1)
{
lean_object* v_n_93_; lean_object* v_n_94_; uint8_t v___x_95_; 
v_n_93_ = lean_ctor_get(v_x_89_, 0);
v_n_94_ = lean_ctor_get(v_x_90_, 0);
v___x_95_ = lean_nat_dec_eq(v_n_93_, v_n_94_);
return v___x_95_;
}
else
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
}
}
LEAN_EXPORT void l_Std_Http_Body_instBEqLength_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_89_ = stack[0].m_obj;
lean_object* v_x_90_ = stack[1].m_obj;
uint8_t v_res_97_;
v_res_97_ = l_Std_Http_Body_instBEqLength_beq(v_x_89_, v_x_90_);
stack->m_num = v_res_97_;
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
uint8_t l_Std_Http_Body_Length_isChunked(lean_object* v_x_104_){
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
LEAN_EXPORT void l_Std_Http_Body_Length_isChunked_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_104_ = stack[0].m_obj;
uint8_t v_res_107_;
v_res_107_ = l_Std_Http_Body_Length_isChunked(v_x_104_);
stack->m_num = v_res_107_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_isChunked___boxed(lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Std_Http_Body_Length_isChunked(v_x_108_);
lean_dec(v_x_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
uint8_t l_Std_Http_Body_Length_isFixed(lean_object* v_x_111_){
_start:
{
if (lean_obj_tag(v_x_111_) == 1)
{
uint8_t v___x_112_; 
v___x_112_ = 1;
return v___x_112_;
}
else
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
}
}
LEAN_EXPORT void l_Std_Http_Body_Length_isFixed_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_111_ = stack[0].m_obj;
uint8_t v_res_114_;
v_res_114_ = l_Std_Http_Body_Length_isFixed(v_x_111_);
stack->m_num = v_res_114_;
}
LEAN_EXPORT lean_object* l_Std_Http_Body_Length_isFixed___boxed(lean_object* v_x_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Std_Http_Body_Length_isFixed(v_x_115_);
lean_dec(v_x_115_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
lean_object* runtime_initialize_Init_Data_Repr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Http_Data_Body_Length(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
