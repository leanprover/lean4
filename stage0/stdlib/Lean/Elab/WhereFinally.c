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
LEAN_EXPORT uint8_t l_Lean_Elab_WhereFinallyView_isNone(lean_object* v_o_6_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_WhereFinallyView_isNone___boxed(lean_object* v_o_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Lean_Elab_WhereFinallyView_isNone(v_o_11_);
lean_dec_ref(v_o_11_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(lean_object* v_inst_14_, lean_object* v_whereFinally_15_, lean_object* v_____r_16_){
_start:
{
lean_object* v_toApplicative_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_28_; 
v_toApplicative_17_ = lean_ctor_get(v_inst_14_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v_inst_14_);
if (v_isSharedCheck_28_ == 0)
{
lean_object* v_unused_29_; 
v_unused_29_ = lean_ctor_get(v_inst_14_, 1);
lean_dec(v_unused_29_);
v___x_19_ = v_inst_14_;
v_isShared_20_ = v_isSharedCheck_28_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_toApplicative_17_);
lean_dec(v_inst_14_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_28_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v_toPure_21_; lean_object* v___x_22_; lean_object* v_tactic_23_; lean_object* v___x_25_; 
v_toPure_21_ = lean_ctor_get(v_toApplicative_17_, 1);
lean_inc(v_toPure_21_);
lean_dec_ref(v_toApplicative_17_);
v___x_22_ = lean_unsigned_to_nat(1u);
v_tactic_23_ = l_Lean_Syntax_getArg(v_whereFinally_15_, v___x_22_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 1, v_tactic_23_);
lean_ctor_set(v___x_19_, 0, v_whereFinally_15_);
v___x_25_ = v___x_19_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_whereFinally_15_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_tactic_23_);
v___x_25_ = v_reuseFailAlloc_27_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; 
v___x_26_ = lean_apply_2(v_toPure_21_, lean_box(0), v___x_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg___lam__1(lean_object* v___f_30_, lean_object* v_____r_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_apply_1(v___f_30_, v_____r_31_);
return v___x_32_;
}
}
static lean_object* _init_l_Lean_Elab_mkWhereFinallyView___redArg___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = ((lean_object*)(l_Lean_Elab_mkWhereFinallyView___redArg___closed__0));
v___x_35_ = l_Lean_stringToMessageData(v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView___redArg(lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_stx_38_){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v_whereFinally_42_; uint8_t v___x_43_; 
v___x_39_ = lean_unsigned_to_nat(2u);
v___x_40_ = l_Lean_Syntax_getArg(v_stx_38_, v___x_39_);
v___x_41_ = lean_unsigned_to_nat(0u);
v_whereFinally_42_ = l_Lean_Syntax_getArg(v___x_40_, v___x_41_);
lean_dec(v___x_40_);
v___x_43_ = l_Lean_Syntax_isMissing(v_whereFinally_42_);
if (v___x_43_ == 0)
{
lean_object* v___f_44_; lean_object* v___f_45_; lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
lean_inc(v_whereFinally_42_);
lean_inc_ref(v_inst_36_);
v___f_44_ = lean_alloc_closure((void*)(l_Lean_Elab_mkWhereFinallyView___redArg___lam__0), 3, 2);
lean_closure_set(v___f_44_, 0, v_inst_36_);
lean_closure_set(v___f_44_, 1, v_whereFinally_42_);
v___f_45_ = lean_alloc_closure((void*)(l_Lean_Elab_mkWhereFinallyView___redArg___lam__1), 2, 1);
lean_closure_set(v___f_45_, 0, v___f_44_);
v___x_51_ = l_Lean_Syntax_getArg(v_whereFinally_42_, v___x_39_);
v___x_52_ = l_Lean_Syntax_getArg(v___x_51_, v___x_41_);
lean_dec(v___x_51_);
v___x_53_ = l_Lean_Syntax_isMissing(v___x_52_);
lean_dec(v___x_52_);
if (v___x_53_ == 0)
{
lean_dec(v_whereFinally_42_);
goto v___jp_46_;
}
else
{
if (v___x_43_ == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec_ref(v___f_45_);
lean_dec(v_stx_38_);
lean_dec_ref(v_inst_37_);
v___x_54_ = lean_box(0);
v___x_55_ = l_Lean_Elab_mkWhereFinallyView___redArg___lam__0(v_inst_36_, v_whereFinally_42_, v___x_54_);
return v___x_55_;
}
else
{
lean_dec(v_whereFinally_42_);
goto v___jp_46_;
}
}
v___jp_46_:
{
lean_object* v_toBind_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_toBind_47_ = lean_ctor_get(v_inst_36_, 1);
lean_inc(v_toBind_47_);
v___x_48_ = lean_obj_once(&l_Lean_Elab_mkWhereFinallyView___redArg___closed__1, &l_Lean_Elab_mkWhereFinallyView___redArg___closed__1_once, _init_l_Lean_Elab_mkWhereFinallyView___redArg___closed__1);
v___x_49_ = l_Lean_throwErrorAt___redArg(v_inst_36_, v_inst_37_, v_stx_38_, v___x_48_);
v___x_50_ = lean_apply_4(v_toBind_47_, lean_box(0), lean_box(0), v___x_49_, v___f_45_);
return v___x_50_;
}
}
else
{
lean_object* v_toApplicative_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_66_; 
lean_dec(v_whereFinally_42_);
lean_dec_ref(v_inst_37_);
v_toApplicative_56_ = lean_ctor_get(v_inst_36_, 0);
v_isSharedCheck_66_ = !lean_is_exclusive(v_inst_36_);
if (v_isSharedCheck_66_ == 0)
{
lean_object* v_unused_67_; 
v_unused_67_ = lean_ctor_get(v_inst_36_, 1);
lean_dec(v_unused_67_);
v___x_58_ = v_inst_36_;
v_isShared_59_ = v_isSharedCheck_66_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_toApplicative_56_);
lean_dec(v_inst_36_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_66_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v_toPure_60_; lean_object* v___x_61_; lean_object* v___x_63_; 
v_toPure_60_ = lean_ctor_get(v_toApplicative_56_, 1);
lean_inc(v_toPure_60_);
lean_dec_ref(v_toApplicative_56_);
v___x_61_ = lean_box(0);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_61_);
lean_ctor_set(v___x_58_, 0, v_stx_38_);
v___x_63_ = v___x_58_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_stx_38_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___x_61_);
v___x_63_ = v_reuseFailAlloc_65_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; 
v___x_64_ = lean_apply_2(v_toPure_60_, lean_box(0), v___x_63_);
return v___x_64_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkWhereFinallyView(lean_object* v_m_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_stx_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Elab_mkWhereFinallyView___redArg(v_inst_69_, v_inst_70_, v_stx_71_);
return v___x_72_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_WhereFinally(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
