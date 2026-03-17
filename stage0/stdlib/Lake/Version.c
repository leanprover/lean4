// Lean compiler output
// Module: Lake.Version
// Imports: public import Init.Prelude import Init.Data.ToString import Init.Data.String.TakeDrop
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_Lean_githash;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
extern uint8_t l_Lean_version_isRelease;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_versionString;
LEAN_EXPORT lean_object* l_Lake_version_major;
LEAN_EXPORT lean_object* l_Lake_version_minor;
LEAN_EXPORT lean_object* l_Lake_version_patch;
LEAN_EXPORT uint8_t l_Lake_version_isRelease;
static const lean_string_object l_Lake_version_specialDesc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "src"};
static const lean_object* l_Lake_version_specialDesc___closed__0 = (const lean_object*)&l_Lake_version_specialDesc___closed__0_value;
static const lean_string_object l_Lake_version_specialDesc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "src+"};
static const lean_object* l_Lake_version_specialDesc___closed__1 = (const lean_object*)&l_Lake_version_specialDesc___closed__1_value;
static lean_once_cell_t l_Lake_version_specialDesc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__2;
static lean_once_cell_t l_Lake_version_specialDesc___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__3;
static lean_once_cell_t l_Lake_version_specialDesc___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__4;
static lean_once_cell_t l_Lake_version_specialDesc___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__5;
static lean_once_cell_t l_Lake_version_specialDesc___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__6;
static lean_once_cell_t l_Lake_version_specialDesc___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_version_specialDesc___closed__7;
static lean_once_cell_t l_Lake_version_specialDesc___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_version_specialDesc___closed__8;
LEAN_EXPORT lean_object* l_Lake_version_specialDesc;
static lean_once_cell_t l_Lake_versionStringCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__0;
static const lean_string_object l_Lake_versionStringCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_versionStringCore___closed__1 = (const lean_object*)&l_Lake_versionStringCore___closed__1_value;
static lean_once_cell_t l_Lake_versionStringCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__2;
static lean_once_cell_t l_Lake_versionStringCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__3;
static lean_once_cell_t l_Lake_versionStringCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__4;
static lean_once_cell_t l_Lake_versionStringCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__5;
static lean_once_cell_t l_Lake_versionStringCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionStringCore___closed__6;
LEAN_EXPORT lean_object* l_Lake_versionStringCore;
static const lean_string_object l_Lake_versionString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_versionString___closed__0 = (const lean_object*)&l_Lake_versionString___closed__0_value;
static lean_once_cell_t l_Lake_versionString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lake_versionString___closed__1;
static const lean_string_object l_Lake_versionString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lake_versionString___closed__2 = (const lean_object*)&l_Lake_versionString___closed__2_value;
static lean_once_cell_t l_Lake_versionString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionString___closed__3;
static lean_once_cell_t l_Lake_versionString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_versionString___closed__4;
LEAN_EXPORT lean_object* l_Lake_versionString;
static const lean_string_object l_Lake_uiVersionString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lake version "};
static const lean_object* l_Lake_uiVersionString___closed__0 = (const lean_object*)&l_Lake_uiVersionString___closed__0_value;
static lean_once_cell_t l_Lake_uiVersionString___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_uiVersionString___closed__1;
static const lean_string_object l_Lake_uiVersionString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " (Lean version "};
static const lean_object* l_Lake_uiVersionString___closed__2 = (const lean_object*)&l_Lake_uiVersionString___closed__2_value;
static lean_once_cell_t l_Lake_uiVersionString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_uiVersionString___closed__3;
static lean_once_cell_t l_Lake_uiVersionString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_uiVersionString___closed__4;
static const lean_string_object l_Lake_uiVersionString___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lake_uiVersionString___closed__5 = (const lean_object*)&l_Lake_uiVersionString___closed__5_value;
static lean_once_cell_t l_Lake_uiVersionString___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_uiVersionString___closed__6;
LEAN_EXPORT lean_object* l_Lake_uiVersionString;
static lean_object* _init_l_Lake_version_major(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_unsigned_to_nat(5u);
return v___x_1_;
}
}
static lean_object* _init_l_Lake_version_minor(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
}
static lean_object* _init_l_Lake_version_patch(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(0u);
return v___x_3_;
}
}
static uint8_t _init_l_Lake_version_isRelease(void){
_start:
{
uint8_t v___x_4_; 
v___x_4_ = l_Lean_version_isRelease;
return v___x_4_;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__2(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = l_Lean_githash;
v___x_8_ = lean_string_utf8_byte_size(v___x_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_9_ = lean_obj_once(&l_Lake_version_specialDesc___closed__2, &l_Lake_version_specialDesc___closed__2_once, _init_l_Lake_version_specialDesc___closed__2);
v___x_10_ = lean_unsigned_to_nat(0u);
v___x_11_ = l_Lean_githash;
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_9_);
return v___x_12_;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__4(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lean_unsigned_to_nat(7u);
v___x_14_ = lean_unsigned_to_nat(0u);
v___x_15_ = lean_obj_once(&l_Lake_version_specialDesc___closed__3, &l_Lake_version_specialDesc___closed__3_once, _init_l_Lake_version_specialDesc___closed__3);
v___x_16_ = l_String_Slice_Pos_nextn(v___x_15_, v___x_14_, v___x_13_);
return v___x_16_;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__5(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = lean_obj_once(&l_Lake_version_specialDesc___closed__4, &l_Lake_version_specialDesc___closed__4_once, _init_l_Lake_version_specialDesc___closed__4);
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = l_Lean_githash;
v___x_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_20_, 0, v___x_19_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_17_);
return v___x_20_;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__6(void){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; 
v___x_21_ = lean_obj_once(&l_Lake_version_specialDesc___closed__5, &l_Lake_version_specialDesc___closed__5_once, _init_l_Lake_version_specialDesc___closed__5);
v___x_22_ = l_String_Slice_toString(v___x_21_);
return v___x_22_;
}
}
static lean_object* _init_l_Lake_version_specialDesc___closed__7(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_23_ = lean_obj_once(&l_Lake_version_specialDesc___closed__6, &l_Lake_version_specialDesc___closed__6_once, _init_l_Lake_version_specialDesc___closed__6);
v___x_24_ = ((lean_object*)(l_Lake_version_specialDesc___closed__1));
v___x_25_ = lean_string_append(v___x_24_, v___x_23_);
return v___x_25_;
}
}
static uint8_t _init_l_Lake_version_specialDesc___closed__8(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v___x_27_ = lean_obj_once(&l_Lake_version_specialDesc___closed__2, &l_Lake_version_specialDesc___closed__2_once, _init_l_Lake_version_specialDesc___closed__2);
v___x_28_ = lean_nat_dec_eq(v___x_27_, v___x_26_);
return v___x_28_;
}
}
static lean_object* _init_l_Lake_version_specialDesc(void){
_start:
{
uint8_t v___y_30_; uint8_t v___x_33_; 
v___x_33_ = l_Lean_version_isRelease;
if (v___x_33_ == 0)
{
v___y_30_ = v___x_33_;
goto v___jp_29_;
}
else
{
uint8_t v___x_34_; 
v___x_34_ = lean_uint8_once(&l_Lake_version_specialDesc___closed__8, &l_Lake_version_specialDesc___closed__8_once, _init_l_Lake_version_specialDesc___closed__8);
if (v___x_34_ == 0)
{
v___y_30_ = v___x_33_;
goto v___jp_29_;
}
else
{
lean_object* v___x_35_; 
v___x_35_ = ((lean_object*)(l_Lake_version_specialDesc___closed__0));
return v___x_35_;
}
}
v___jp_29_:
{
if (v___y_30_ == 0)
{
lean_object* v___x_31_; 
v___x_31_ = ((lean_object*)(l_Lake_version_specialDesc___closed__0));
return v___x_31_;
}
else
{
lean_object* v___x_32_; 
v___x_32_ = lean_obj_once(&l_Lake_version_specialDesc___closed__7, &l_Lake_version_specialDesc___closed__7_once, _init_l_Lake_version_specialDesc___closed__7);
return v___x_32_;
}
}
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__0(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(5u);
v___x_37_ = l_Nat_reprFast(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__2(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = ((lean_object*)(l_Lake_versionStringCore___closed__1));
v___x_40_ = lean_obj_once(&l_Lake_versionStringCore___closed__0, &l_Lake_versionStringCore___closed__0_once, _init_l_Lake_versionStringCore___closed__0);
v___x_41_ = lean_string_append(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__3(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = l_Nat_reprFast(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__4(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_obj_once(&l_Lake_versionStringCore___closed__3, &l_Lake_versionStringCore___closed__3_once, _init_l_Lake_versionStringCore___closed__3);
v___x_45_ = lean_obj_once(&l_Lake_versionStringCore___closed__2, &l_Lake_versionStringCore___closed__2_once, _init_l_Lake_versionStringCore___closed__2);
v___x_46_ = lean_string_append(v___x_45_, v___x_44_);
return v___x_46_;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__5(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_47_ = ((lean_object*)(l_Lake_versionStringCore___closed__1));
v___x_48_ = lean_obj_once(&l_Lake_versionStringCore___closed__4, &l_Lake_versionStringCore___closed__4_once, _init_l_Lake_versionStringCore___closed__4);
v___x_49_ = lean_string_append(v___x_48_, v___x_47_);
return v___x_49_;
}
}
static lean_object* _init_l_Lake_versionStringCore___closed__6(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_50_ = lean_obj_once(&l_Lake_versionStringCore___closed__3, &l_Lake_versionStringCore___closed__3_once, _init_l_Lake_versionStringCore___closed__3);
v___x_51_ = lean_obj_once(&l_Lake_versionStringCore___closed__5, &l_Lake_versionStringCore___closed__5_once, _init_l_Lake_versionStringCore___closed__5);
v___x_52_ = lean_string_append(v___x_51_, v___x_50_);
return v___x_52_;
}
}
static lean_object* _init_l_Lake_versionStringCore(void){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_obj_once(&l_Lake_versionStringCore___closed__6, &l_Lake_versionStringCore___closed__6_once, _init_l_Lake_versionStringCore___closed__6);
return v___x_53_;
}
}
static uint8_t _init_l_Lake_versionString___closed__1(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; uint8_t v___x_57_; 
v___x_55_ = ((lean_object*)(l_Lake_versionString___closed__0));
v___x_56_ = l_Lake_version_specialDesc;
v___x_57_ = lean_string_dec_eq(v___x_56_, v___x_55_);
return v___x_57_;
}
}
static lean_object* _init_l_Lake_versionString___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = ((lean_object*)(l_Lake_versionString___closed__2));
v___x_60_ = l_Lake_versionStringCore;
v___x_61_ = lean_string_append(v___x_60_, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lake_versionString___closed__4(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_62_ = l_Lake_version_specialDesc;
v___x_63_ = lean_obj_once(&l_Lake_versionString___closed__3, &l_Lake_versionString___closed__3_once, _init_l_Lake_versionString___closed__3);
v___x_64_ = lean_string_append(v___x_63_, v___x_62_);
return v___x_64_;
}
}
static lean_object* _init_l_Lake_versionString(void){
_start:
{
uint8_t v___x_65_; 
v___x_65_ = lean_uint8_once(&l_Lake_versionString___closed__1, &l_Lake_versionString___closed__1_once, _init_l_Lake_versionString___closed__1);
if (v___x_65_ == 0)
{
lean_object* v___x_66_; 
v___x_66_ = lean_obj_once(&l_Lake_versionString___closed__4, &l_Lake_versionString___closed__4_once, _init_l_Lake_versionString___closed__4);
return v___x_66_;
}
else
{
lean_object* v___x_67_; 
v___x_67_ = l_Lake_versionStringCore;
return v___x_67_;
}
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__1(void){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_69_ = l_Lake_versionString;
v___x_70_ = ((lean_object*)(l_Lake_uiVersionString___closed__0));
v___x_71_ = lean_string_append(v___x_70_, v___x_69_);
return v___x_71_;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__3(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_73_ = ((lean_object*)(l_Lake_uiVersionString___closed__2));
v___x_74_ = lean_obj_once(&l_Lake_uiVersionString___closed__1, &l_Lake_uiVersionString___closed__1_once, _init_l_Lake_uiVersionString___closed__1);
v___x_75_ = lean_string_append(v___x_74_, v___x_73_);
return v___x_75_;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__4(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_76_ = l_Lean_versionString;
v___x_77_ = lean_obj_once(&l_Lake_uiVersionString___closed__3, &l_Lake_uiVersionString___closed__3_once, _init_l_Lake_uiVersionString___closed__3);
v___x_78_ = lean_string_append(v___x_77_, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lake_uiVersionString___closed__6(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = ((lean_object*)(l_Lake_uiVersionString___closed__5));
v___x_81_ = lean_obj_once(&l_Lake_uiVersionString___closed__4, &l_Lake_uiVersionString___closed__4_once, _init_l_Lake_uiVersionString___closed__4);
v___x_82_ = lean_string_append(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Lake_uiVersionString(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_obj_once(&l_Lake_uiVersionString___closed__6, &l_Lake_uiVersionString___closed__6_once, _init_l_Lake_uiVersionString___closed__6);
return v___x_83_;
}
}
lean_object* runtime_initialize_Init_Prelude(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Version(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_version_major = _init_l_Lake_version_major();
lean_mark_persistent(l_Lake_version_major);
l_Lake_version_minor = _init_l_Lake_version_minor();
lean_mark_persistent(l_Lake_version_minor);
l_Lake_version_patch = _init_l_Lake_version_patch();
lean_mark_persistent(l_Lake_version_patch);
l_Lake_version_isRelease = _init_l_Lake_version_isRelease();
l_Lake_version_specialDesc = _init_l_Lake_version_specialDesc();
lean_mark_persistent(l_Lake_version_specialDesc);
l_Lake_versionStringCore = _init_l_Lake_versionStringCore();
lean_mark_persistent(l_Lake_versionStringCore);
l_Lake_versionString = _init_l_Lake_versionString();
lean_mark_persistent(l_Lake_versionString);
l_Lake_uiVersionString = _init_l_Lake_uiVersionString();
lean_mark_persistent(l_Lake_uiVersionString);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Version(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Prelude(uint8_t builtin);
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Version(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Prelude(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Version(builtin);
}
#ifdef __cplusplus
}
#endif
