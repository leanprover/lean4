// Lean compiler output
// Module: Lean.Elab.WhereFinally
// Imports: public import Lean.Parser.Term
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
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0 = (const lean_object*)&l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedWhereFinallyView_default = (const lean_object*)&l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_instInhabitedWhereFinallyView = (const lean_object*)&l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_WhereFinallyView_none = (const lean_object*)&l_Lean_Elab_instInhabitedWhereFinallyView_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Elab_WhereFinallyView_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_mkWhereFinallyView___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "`where ... finally` does not currently support any named sub-sections `| sectionName => ...`"};
static const lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_mkWhereFinallyView___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_mkWhereFinallyView___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_WhereFinallyView_isNone(lean_object* v_o_6_){
_start:
{
lean_object* v_ref_7_; lean_object* v_tactic_8_; uint8_t v___x_9_; 
v_ref_7_ = lean_ctor_get(v_o_6_, 0);
v_tactic_8_ = lean_ctor_get(v_o_6_, 1);
v___x_9_ = l_Lean_Syntax_isMissing(v_ref_7_);
if (v___x_9_ == 0)
{
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = l_Lean_Syntax_isMissing(v_tactic_8_);
return v___x_10_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_WhereFinallyView_isNone_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_6_ = stack[0].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Lean_Elab_WhereFinallyView_isNone(v_o_6_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_isNone___boxed(lean_object* v_o_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Elab_WhereFinallyView_isNone(v_o_12_);
lean_dec_ref(v_o_12_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(lean_object* v_whereFinally_15_, lean_object* v_toPure_16_, lean_object* v_____r_17_){
_start:
{
lean_object* v___x_18_; lean_object* v_tactic_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v_tactic_19_ = l_Lean_Syntax_getArg(v_whereFinally_15_, v___x_18_);
v___x_20_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_20_, 0, v_whereFinally_15_);
lean_ctor_set(v___x_20_, 1, v_tactic_19_);
v___x_21_ = lean_apply_2(v_toPure_16_, lean_box(0), v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__1(lean_object* v___f_22_, lean_object* v_____r_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_apply_1(v___f_22_, v_____r_23_);
return v___x_24_;
}
}
static lean_object* _init_l_Lean_Elab_mkWhereFinallyView___redArg___closed__1(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = ((lean_object*)(l_Lean_Elab_mkWhereFinallyView___redArg___closed__0));
v___x_27_ = l_Lean_stringToMessageData(v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg(lean_object* v_inst_28_, lean_object* v_inst_29_, lean_object* v_stx_30_){
_start:
{
lean_object* v_toApplicative_31_; lean_object* v_toBind_32_; lean_object* v_toPure_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v_whereFinally_37_; uint8_t v___x_38_; 
v_toApplicative_31_ = lean_ctor_get(v_inst_28_, 0);
v_toBind_32_ = lean_ctor_get(v_inst_28_, 1);
v_toPure_33_ = lean_ctor_get(v_toApplicative_31_, 1);
v___x_34_ = lean_unsigned_to_nat(2u);
v___x_35_ = l_Lean_Syntax_getArg(v_stx_30_, v___x_34_);
v___x_36_ = lean_unsigned_to_nat(0u);
v_whereFinally_37_ = l_Lean_Syntax_getArg(v___x_35_, v___x_36_);
lean_dec(v___x_35_);
v___x_38_ = l_Lean_Syntax_isMissing(v_whereFinally_37_);
if (v___x_38_ == 0)
{
lean_object* v___f_39_; lean_object* v___f_40_; lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
lean_inc(v_toBind_32_);
lean_inc(v_toPure_33_);
lean_inc(v_whereFinally_37_);
v___f_39_ = lean_alloc_closure((void*)(l_Lean_Elab_mkWhereFinallyView___redArg___lam__0), 3, 2);
lean_closure_set(v___f_39_, 0, v_whereFinally_37_);
lean_closure_set(v___f_39_, 1, v_toPure_33_);
v___f_40_ = lean_alloc_closure((void*)(l_Lean_Elab_mkWhereFinallyView___redArg___lam__1), 2, 1);
lean_closure_set(v___f_40_, 0, v___f_39_);
v___x_45_ = l_Lean_Syntax_getArg(v_whereFinally_37_, v___x_34_);
v___x_46_ = l_Lean_Syntax_getArg(v___x_45_, v___x_36_);
lean_dec(v___x_45_);
v___x_47_ = l_Lean_Syntax_isMissing(v___x_46_);
lean_dec(v___x_46_);
if (v___x_47_ == 0)
{
lean_dec(v_whereFinally_37_);
goto v___jp_41_;
}
else
{
if (v___x_38_ == 0)
{
lean_object* v___x_48_; lean_object* v___x_49_; 
lean_inc(v_toPure_33_);
lean_dec_ref(v___f_40_);
lean_dec(v_toBind_32_);
lean_dec(v_stx_30_);
lean_dec_ref(v_inst_29_);
lean_dec_ref(v_inst_28_);
v___x_48_ = lean_box(0);
v___x_49_ = l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(v_whereFinally_37_, v_toPure_33_, v___x_48_);
return v___x_49_;
}
else
{
lean_dec(v_whereFinally_37_);
goto v___jp_41_;
}
}
v___jp_41_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = lean_obj_once(&l_Lean_Elab_mkWhereFinallyView___redArg___closed__1, &l_Lean_Elab_mkWhereFinallyView___redArg___closed__1_once, _init_l_Lean_Elab_mkWhereFinallyView___redArg___closed__1);
v___x_43_ = l_Lean_throwErrorAt___redArg(v_inst_28_, v_inst_29_, v_stx_30_, v___x_42_);
v___x_44_ = lean_apply_4(v_toBind_32_, lean_box(0), lean_box(0), v___x_43_, v___f_40_);
return v___x_44_;
}
}
else
{
lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_58_; 
lean_inc(v_toPure_33_);
lean_dec(v_whereFinally_37_);
lean_dec_ref(v_inst_29_);
v_isSharedCheck_58_ = !lean_is_exclusive(v_inst_28_);
if (v_isSharedCheck_58_ == 0)
{
lean_object* v_unused_59_; lean_object* v_unused_60_; 
v_unused_59_ = lean_ctor_get(v_inst_28_, 1);
lean_dec(v_unused_59_);
v_unused_60_ = lean_ctor_get(v_inst_28_, 0);
lean_dec(v_unused_60_);
v___x_51_ = v_inst_28_;
v_isShared_52_ = v_isSharedCheck_58_;
goto v_resetjp_50_;
}
else
{
lean_dec(v_inst_28_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_58_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_53_; lean_object* v___x_55_; 
v___x_53_ = lean_box(0);
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 1, v___x_53_);
lean_ctor_set(v___x_51_, 0, v_stx_30_);
v___x_55_ = v___x_51_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_stx_30_);
lean_ctor_set(v_reuseFailAlloc_57_, 1, v___x_53_);
v___x_55_ = v_reuseFailAlloc_57_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
lean_object* v___x_56_; 
v___x_56_ = lean_apply_2(v_toPure_33_, lean_box(0), v___x_55_);
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView(lean_object* v_m_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_stx_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Elab_mkWhereFinallyView___redArg(v_inst_62_, v_inst_63_, v_stx_64_);
return v___x_65_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_WhereFinally(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_WhereFinally(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_WhereFinally(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_WhereFinally(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_WhereFinally(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_WhereFinally(builtin);
}
#ifdef __cplusplus
}
#endif
