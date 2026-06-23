// Lean compiler output
// Module: Lean.Meta.PPBinder
// Imports: public import Lean.Meta.Basic
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
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_bracket(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__0 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__0_value;
static lean_once_cell_t l_Lean_LocalDecl_ppAsBinder___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_LocalDecl_ppAsBinder___closed__1;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__2 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__2_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__3 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__3_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__4 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__4_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__5 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__5_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦃"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__6 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__6_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⦄"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__7 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__7_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__8 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__8_value;
static const lean_string_object l_Lean_LocalDecl_ppAsBinder___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_LocalDecl_ppAsBinder___closed__9 = (const lean_object*)&l_Lean_LocalDecl_ppAsBinder___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ppAsBinder(lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_LocalDecl_ppAsBinder___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__0));
v___x_3_ = l_Lean_stringToMessageData(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalDecl_ppAsBinder(lean_object* v_x_12_){
_start:
{
if (lean_obj_tag(v_x_12_) == 0)
{
lean_object* v_fvarId_13_; lean_object* v_type_14_; uint8_t v_bi_15_; lean_object* v_fst_17_; lean_object* v_snd_18_; 
v_fvarId_13_ = lean_ctor_get(v_x_12_, 1);
lean_inc(v_fvarId_13_);
v_type_14_ = lean_ctor_get(v_x_12_, 3);
lean_inc_ref(v_type_14_);
v_bi_15_ = lean_ctor_get_uint8(v_x_12_, sizeof(void*)*4);
lean_dec_ref_known(v_x_12_, 4);
switch(v_bi_15_)
{
case 0:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__2));
v___x_28_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__3));
v_fst_17_ = v___x_27_;
v_snd_18_ = v___x_28_;
goto v___jp_16_;
}
case 1:
{
lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_29_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__4));
v___x_30_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__5));
v_fst_17_ = v___x_29_;
v_snd_18_ = v___x_30_;
goto v___jp_16_;
}
case 2:
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__6));
v___x_32_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__7));
v_fst_17_ = v___x_31_;
v_snd_18_ = v___x_32_;
goto v___jp_16_;
}
default: 
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__8));
v___x_34_ = ((lean_object*)(l_Lean_LocalDecl_ppAsBinder___closed__9));
v_fst_17_ = v___x_33_;
v_snd_18_ = v___x_34_;
goto v___jp_16_;
}
}
v___jp_16_:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_19_ = l_Lean_mkFVar(v_fvarId_13_);
v___x_20_ = l_Lean_MessageData_ofExpr(v___x_19_);
v___x_21_ = lean_obj_once(&l_Lean_LocalDecl_ppAsBinder___closed__1, &l_Lean_LocalDecl_ppAsBinder___closed__1_once, _init_l_Lean_LocalDecl_ppAsBinder___closed__1);
v___x_22_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_22_, 0, v___x_20_);
lean_ctor_set(v___x_22_, 1, v___x_21_);
v___x_23_ = l_Lean_MessageData_ofExpr(v_type_14_);
v___x_24_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_22_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
lean_inc_ref(v_snd_18_);
lean_inc_ref(v_fst_17_);
v___x_25_ = l_Lean_MessageData_bracket(v_fst_17_, v___x_24_, v_snd_18_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
else
{
lean_object* v___x_35_; 
lean_dec_ref_known(v_x_12_, 5);
v___x_35_ = lean_box(0);
return v___x_35_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___redArg(lean_object* v_fvarId_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_36_, v_a_37_, v_a_38_, v_a_39_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_50_; 
v_a_42_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_50_ == 0)
{
v___x_44_ = v___x_41_;
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_41_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_46_ = l_Lean_LocalDecl_ppAsBinder(v_a_42_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 0, v___x_46_);
v___x_48_ = v___x_44_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
else
{
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
v_a_51_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v___x_41_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_41_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___redArg___boxed(lean_object* v_fvarId_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_FVarId_ppAsBinder___redArg(v_fvarId_59_, v_a_60_, v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec_ref(v_a_60_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder(lean_object* v_fvarId_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_65_, v_a_66_, v_a_68_, v_a_69_);
if (lean_obj_tag(v___x_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_80_; 
v_a_72_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_80_ == 0)
{
v___x_74_ = v___x_71_;
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_76_ = l_Lean_LocalDecl_ppAsBinder(v_a_72_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_76_);
v___x_78_ = v___x_74_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
else
{
lean_object* v_a_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_88_; 
v_a_81_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_88_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_88_ == 0)
{
v___x_83_ = v___x_71_;
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_a_81_);
lean_dec(v___x_71_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_88_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_87_; 
v_reuseFailAlloc_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_87_, 0, v_a_81_);
v___x_86_ = v_reuseFailAlloc_87_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_FVarId_ppAsBinder___boxed(lean_object* v_fvarId_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Lean_FVarId_ppAsBinder(v_fvarId_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_a_93_);
lean_dec_ref(v_a_92_);
lean_dec(v_a_91_);
lean_dec_ref(v_a_90_);
return v_res_95_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_PPBinder(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_PPBinder(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_PPBinder(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_PPBinder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_PPBinder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_PPBinder(builtin);
}
#ifdef __cplusplus
}
#endif
