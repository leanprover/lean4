// Lean compiler output
// Module: Init.Data.OfScientific
// Imports: public import Init.Data.Float.Float32 import Init.Data.Nat.Log2 import Init.Meta import Init.Data.Array.Lemmas
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
double lean_float_of_bits(uint64_t);
float lean_float32_of_bits(uint32_t);
uint32_t l_Float32_Model_ofScientific(lean_object*, lean_object*);
float lean_float32_of_bits(uint32_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
float lean_uint64_to_float32(uint64_t);
float lean_float32_mul(float, float);
float lean_float32_div(float, float);
uint64_t l_Float_Model_ofScientific(lean_object*, lean_object*);
double lean_float_of_bits(uint64_t);
double lean_uint64_to_float(uint64_t);
double lean_float_mul(double, double);
double lean_float_div(double, double);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
double lean_float_negate(double);
float lean_float32_negate(float);
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__0;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__1;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__2;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__3;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__4;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__5;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__6;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__7;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__8;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__9;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__10;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__11;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__12;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__13;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__14;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__15;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__16;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__17;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__18;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__19;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__20;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__21;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Float_exactlyRepresentablePowersOfTen___closed__22;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__1;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__2;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__3;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__4;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__5;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__6;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__7;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__8;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__9;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__10;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__11;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__12;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__13;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__14;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__15;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__16;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__17;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__18;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__19;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__20;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__21;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__22;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__23;
static lean_once_cell_t l_Float_exactlyRepresentablePowersOfTen___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_exactlyRepresentablePowersOfTen___closed__23;
LEAN_EXPORT lean_object* l_Float_exactlyRepresentablePowersOfTen;
LEAN_EXPORT double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Float_ofScientific___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instOfScientificFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float_ofScientific___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOfScientificFloat___closed__0 = (const lean_object*)&l_instOfScientificFloat___closed__0_value;
LEAN_EXPORT const lean_object* l_instOfScientificFloat = (const lean_object*)&l_instOfScientificFloat___closed__0_value;
LEAN_EXPORT double lean_float_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Float_ofNat___boxed(lean_object*);
static lean_once_cell_t l_Float_ofInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float_ofInt___closed__0;
LEAN_EXPORT double l_Float_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Float_ofInt___boxed(lean_object*);
LEAN_EXPORT double l_instOfNatFloat(lean_object*);
LEAN_EXPORT lean_object* l_instOfNatFloat___boxed(lean_object*);
LEAN_EXPORT double l_Nat_toFloat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toFloat___boxed(lean_object*);
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__0;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__1;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__2;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__3;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__4;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__5;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__6;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__7;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__8;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__9;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static float l_Float32_exactlyRepresentablePowersOfTen___closed__10;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__1;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__2;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__3;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__4;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__5;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__6;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__7;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__8;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__9;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__10;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__11;
static lean_once_cell_t l_Float32_exactlyRepresentablePowersOfTen___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Float32_exactlyRepresentablePowersOfTen___closed__11;
LEAN_EXPORT lean_object* l_Float32_exactlyRepresentablePowersOfTen;
LEAN_EXPORT float l_Float32_ofScientific(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Float32_ofScientific___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instOfScientificFloat32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Float32_ofScientific___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instOfScientificFloat32___closed__0 = (const lean_object*)&l_instOfScientificFloat32___closed__0_value;
LEAN_EXPORT const lean_object* l_instOfScientificFloat32 = (const lean_object*)&l_instOfScientificFloat32___closed__0_value;
LEAN_EXPORT float lean_float32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Float32_ofNat___boxed(lean_object*);
LEAN_EXPORT float l_Float32_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Float32_ofInt___boxed(lean_object*);
LEAN_EXPORT float l_instOfNatFloat32(lean_object*);
LEAN_EXPORT lean_object* l_instOfNatFloat32___boxed(lean_object*);
LEAN_EXPORT float l_Nat_toFloat32(lean_object*);
LEAN_EXPORT lean_object* l_Nat_toFloat32___boxed(lean_object*);
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__0(void){
_start:
{
uint64_t v___x_1_; double v___x_2_; 
v___x_1_ = 4607182418800017408ULL;
v___x_2_ = lean_float_of_bits(v___x_1_);
return v___x_2_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__1(void){
_start:
{
uint64_t v___x_3_; double v___x_4_; 
v___x_3_ = 4621819117588971520ULL;
v___x_4_ = lean_float_of_bits(v___x_3_);
return v___x_4_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__2(void){
_start:
{
uint64_t v___x_5_; double v___x_6_; 
v___x_5_ = 4636737291354636288ULL;
v___x_6_ = lean_float_of_bits(v___x_5_);
return v___x_6_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__3(void){
_start:
{
uint64_t v___x_7_; double v___x_8_; 
v___x_7_ = 4652007308841189376ULL;
v___x_8_ = lean_float_of_bits(v___x_7_);
return v___x_8_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__4(void){
_start:
{
uint64_t v___x_9_; double v___x_10_; 
v___x_9_ = 4666723172467343360ULL;
v___x_10_ = lean_float_of_bits(v___x_9_);
return v___x_10_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__5(void){
_start:
{
uint64_t v___x_11_; double v___x_12_; 
v___x_11_ = 4681608360884174848ULL;
v___x_12_ = lean_float_of_bits(v___x_11_);
return v___x_12_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__6(void){
_start:
{
uint64_t v___x_13_; double v___x_14_; 
v___x_13_ = 4696837146684686336ULL;
v___x_14_ = lean_float_of_bits(v___x_13_);
return v___x_14_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__7(void){
_start:
{
uint64_t v___x_15_; double v___x_16_; 
v___x_15_ = 4711630319722168320ULL;
v___x_16_ = lean_float_of_bits(v___x_15_);
return v___x_16_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__8(void){
_start:
{
uint64_t v___x_17_; double v___x_18_; 
v___x_17_ = 4726483295884279808ULL;
v___x_18_ = lean_float_of_bits(v___x_17_);
return v___x_18_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__9(void){
_start:
{
uint64_t v___x_19_; double v___x_20_; 
v___x_19_ = 4741671816366391296ULL;
v___x_20_ = lean_float_of_bits(v___x_19_);
return v___x_20_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__10(void){
_start:
{
uint64_t v___x_21_; double v___x_22_; 
v___x_21_ = 4756540486875873280ULL;
v___x_22_ = lean_float_of_bits(v___x_21_);
return v___x_22_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__11(void){
_start:
{
uint64_t v___x_23_; double v___x_24_; 
v___x_23_ = 4771362005757984768ULL;
v___x_24_ = lean_float_of_bits(v___x_23_);
return v___x_24_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__12(void){
_start:
{
uint64_t v___x_25_; double v___x_26_; 
v___x_25_ = 4786511204640096256ULL;
v___x_26_ = lean_float_of_bits(v___x_25_);
return v___x_26_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__13(void){
_start:
{
uint64_t v___x_27_; double v___x_28_; 
v___x_27_ = 4801453603149578240ULL;
v___x_28_ = lean_float_of_bits(v___x_27_);
return v___x_28_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__14(void){
_start:
{
uint64_t v___x_29_; double v___x_30_; 
v___x_29_ = 4816244402031689728ULL;
v___x_30_ = lean_float_of_bits(v___x_29_);
return v___x_30_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__15(void){
_start:
{
uint64_t v___x_31_; double v___x_32_; 
v___x_31_ = 4831355200913801216ULL;
v___x_32_ = lean_float_of_bits(v___x_31_);
return v___x_32_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__16(void){
_start:
{
uint64_t v___x_33_; double v___x_34_; 
v___x_33_ = 4846369599423283200ULL;
v___x_34_ = lean_float_of_bits(v___x_33_);
return v___x_34_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__17(void){
_start:
{
uint64_t v___x_35_; double v___x_36_; 
v___x_35_ = 4861130398305394688ULL;
v___x_36_ = lean_float_of_bits(v___x_35_);
return v___x_36_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__18(void){
_start:
{
uint64_t v___x_37_; double v___x_38_; 
v___x_37_ = 4876203697187506176ULL;
v___x_38_ = lean_float_of_bits(v___x_37_);
return v___x_38_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__19(void){
_start:
{
uint64_t v___x_39_; double v___x_40_; 
v___x_39_ = 4891288408196988160ULL;
v___x_40_ = lean_float_of_bits(v___x_39_);
return v___x_40_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__20(void){
_start:
{
uint64_t v___x_41_; double v___x_42_; 
v___x_41_ = 4906019910204099648ULL;
v___x_42_ = lean_float_of_bits(v___x_41_);
return v___x_42_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__21(void){
_start:
{
uint64_t v___x_43_; double v___x_44_; 
v___x_43_ = 4921056587992461136ULL;
v___x_44_ = lean_float_of_bits(v___x_43_);
return v___x_44_;
}
}
static double _init_l_Float_exactlyRepresentablePowersOfTen___closed__22(void){
_start:
{
uint64_t v___x_45_; double v___x_46_; 
v___x_45_ = 4936209963552724370ULL;
v___x_46_ = lean_float_of_bits(v___x_45_);
return v___x_46_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__1(void){
_start:
{
double v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__22, &l_Float_exactlyRepresentablePowersOfTen___closed__22_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__22);
v___x_48_ = lean_box_float(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__2(void){
_start:
{
double v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__21, &l_Float_exactlyRepresentablePowersOfTen___closed__21_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__21);
v___x_50_ = lean_box_float(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__3(void){
_start:
{
double v___x_51_; lean_object* v___x_52_; 
v___x_51_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__20, &l_Float_exactlyRepresentablePowersOfTen___closed__20_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__20);
v___x_52_ = lean_box_float(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__4(void){
_start:
{
double v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__19, &l_Float_exactlyRepresentablePowersOfTen___closed__19_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__19);
v___x_54_ = lean_box_float(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__5(void){
_start:
{
double v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__18, &l_Float_exactlyRepresentablePowersOfTen___closed__18_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__18);
v___x_56_ = lean_box_float(v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__6(void){
_start:
{
double v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__17, &l_Float_exactlyRepresentablePowersOfTen___closed__17_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__17);
v___x_58_ = lean_box_float(v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__7(void){
_start:
{
double v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__16, &l_Float_exactlyRepresentablePowersOfTen___closed__16_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__16);
v___x_60_ = lean_box_float(v___x_59_);
return v___x_60_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__8(void){
_start:
{
double v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__15, &l_Float_exactlyRepresentablePowersOfTen___closed__15_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__15);
v___x_62_ = lean_box_float(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__9(void){
_start:
{
double v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__14, &l_Float_exactlyRepresentablePowersOfTen___closed__14_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__14);
v___x_64_ = lean_box_float(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__10(void){
_start:
{
double v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__13, &l_Float_exactlyRepresentablePowersOfTen___closed__13_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__13);
v___x_66_ = lean_box_float(v___x_65_);
return v___x_66_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__11(void){
_start:
{
double v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__12, &l_Float_exactlyRepresentablePowersOfTen___closed__12_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__12);
v___x_68_ = lean_box_float(v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__12(void){
_start:
{
double v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__11, &l_Float_exactlyRepresentablePowersOfTen___closed__11_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__11);
v___x_70_ = lean_box_float(v___x_69_);
return v___x_70_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__13(void){
_start:
{
double v___x_71_; lean_object* v___x_72_; 
v___x_71_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__10, &l_Float_exactlyRepresentablePowersOfTen___closed__10_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__10);
v___x_72_ = lean_box_float(v___x_71_);
return v___x_72_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__14(void){
_start:
{
double v___x_73_; lean_object* v___x_74_; 
v___x_73_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__9, &l_Float_exactlyRepresentablePowersOfTen___closed__9_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__9);
v___x_74_ = lean_box_float(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__15(void){
_start:
{
double v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__8, &l_Float_exactlyRepresentablePowersOfTen___closed__8_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__8);
v___x_76_ = lean_box_float(v___x_75_);
return v___x_76_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__16(void){
_start:
{
double v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__7, &l_Float_exactlyRepresentablePowersOfTen___closed__7_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__7);
v___x_78_ = lean_box_float(v___x_77_);
return v___x_78_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__17(void){
_start:
{
double v___x_79_; lean_object* v___x_80_; 
v___x_79_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__6, &l_Float_exactlyRepresentablePowersOfTen___closed__6_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__6);
v___x_80_ = lean_box_float(v___x_79_);
return v___x_80_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__18(void){
_start:
{
double v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__5, &l_Float_exactlyRepresentablePowersOfTen___closed__5_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__5);
v___x_82_ = lean_box_float(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__19(void){
_start:
{
double v___x_83_; lean_object* v___x_84_; 
v___x_83_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__4, &l_Float_exactlyRepresentablePowersOfTen___closed__4_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__4);
v___x_84_ = lean_box_float(v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__20(void){
_start:
{
double v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__3, &l_Float_exactlyRepresentablePowersOfTen___closed__3_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__3);
v___x_86_ = lean_box_float(v___x_85_);
return v___x_86_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__21(void){
_start:
{
double v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__2, &l_Float_exactlyRepresentablePowersOfTen___closed__2_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__2);
v___x_88_ = lean_box_float(v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__22(void){
_start:
{
double v___x_89_; lean_object* v___x_90_; 
v___x_89_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__1, &l_Float_exactlyRepresentablePowersOfTen___closed__1_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__1);
v___x_90_ = lean_box_float(v___x_89_);
return v___x_90_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__23(void){
_start:
{
double v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_float_once(&l_Float_exactlyRepresentablePowersOfTen___closed__0, &l_Float_exactlyRepresentablePowersOfTen___closed__0_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__0);
v___x_92_ = lean_box_float(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen___closed__23(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_93_ = lean_unsigned_to_nat(23u);
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_93_);
v___x_95_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__23;
v___x_96_ = lean_array_push(v___x_94_, v___x_95_);
v___x_97_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__22;
v___x_98_ = lean_array_push(v___x_96_, v___x_97_);
v___x_99_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__21;
v___x_100_ = lean_array_push(v___x_98_, v___x_99_);
v___x_101_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__20;
v___x_102_ = lean_array_push(v___x_100_, v___x_101_);
v___x_103_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__19;
v___x_104_ = lean_array_push(v___x_102_, v___x_103_);
v___x_105_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__18;
v___x_106_ = lean_array_push(v___x_104_, v___x_105_);
v___x_107_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__17;
v___x_108_ = lean_array_push(v___x_106_, v___x_107_);
v___x_109_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__16;
v___x_110_ = lean_array_push(v___x_108_, v___x_109_);
v___x_111_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__15;
v___x_112_ = lean_array_push(v___x_110_, v___x_111_);
v___x_113_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__14;
v___x_114_ = lean_array_push(v___x_112_, v___x_113_);
v___x_115_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__13;
v___x_116_ = lean_array_push(v___x_114_, v___x_115_);
v___x_117_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__12;
v___x_118_ = lean_array_push(v___x_116_, v___x_117_);
v___x_119_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__11;
v___x_120_ = lean_array_push(v___x_118_, v___x_119_);
v___x_121_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__10;
v___x_122_ = lean_array_push(v___x_120_, v___x_121_);
v___x_123_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__9;
v___x_124_ = lean_array_push(v___x_122_, v___x_123_);
v___x_125_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__8;
v___x_126_ = lean_array_push(v___x_124_, v___x_125_);
v___x_127_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__7;
v___x_128_ = lean_array_push(v___x_126_, v___x_127_);
v___x_129_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__6;
v___x_130_ = lean_array_push(v___x_128_, v___x_129_);
v___x_131_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__5;
v___x_132_ = lean_array_push(v___x_130_, v___x_131_);
v___x_133_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__4;
v___x_134_ = lean_array_push(v___x_132_, v___x_133_);
v___x_135_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__3;
v___x_136_ = lean_array_push(v___x_134_, v___x_135_);
v___x_137_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__2;
v___x_138_ = lean_array_push(v___x_136_, v___x_137_);
v___x_139_ = l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__1;
v___x_140_ = lean_array_push(v___x_138_, v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Float_exactlyRepresentablePowersOfTen(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&l_Float_exactlyRepresentablePowersOfTen___closed__23, &l_Float_exactlyRepresentablePowersOfTen___closed__23_once, _init_l_Float_exactlyRepresentablePowersOfTen___closed__23);
return v___x_141_;
}
}
LEAN_EXPORT double l_Float_ofScientific(lean_object* v_m_142_, uint8_t v_s_143_, lean_object* v_e_144_){
_start:
{
lean_object* v___y_146_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_cstr_to_nat("9007199254740992");
v___x_153_ = lean_nat_dec_lt(v_m_142_, v___x_152_);
if (v___x_153_ == 0)
{
goto v___jp_149_;
}
else
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = lean_unsigned_to_nat(22u);
v___x_155_ = lean_nat_dec_le(v_e_144_, v___x_154_);
if (v___x_155_ == 0)
{
goto v___jp_149_;
}
else
{
lean_object* v___x_156_; lean_object* v_powerOfTen_157_; 
v___x_156_ = l_Float_exactlyRepresentablePowersOfTen;
v_powerOfTen_157_ = lean_array_fget_borrowed(v___x_156_, v_e_144_);
lean_dec(v_e_144_);
if (v_s_143_ == 0)
{
uint64_t v___x_158_; double v___x_159_; double v___x_160_; double v___x_161_; 
v___x_158_ = lean_uint64_of_nat(v_m_142_);
lean_dec(v_m_142_);
v___x_159_ = lean_uint64_to_float(v___x_158_);
v___x_160_ = lean_unbox_float(v_powerOfTen_157_);
v___x_161_ = lean_float_mul(v___x_159_, v___x_160_);
return v___x_161_;
}
else
{
uint64_t v___x_162_; double v___x_163_; double v___x_164_; double v___x_165_; 
v___x_162_ = lean_uint64_of_nat(v_m_142_);
lean_dec(v_m_142_);
v___x_163_ = lean_uint64_to_float(v___x_162_);
v___x_164_ = lean_unbox_float(v_powerOfTen_157_);
v___x_165_ = lean_float_div(v___x_163_, v___x_164_);
return v___x_165_;
}
}
}
v___jp_145_:
{
uint64_t v___x_147_; double v___x_148_; 
v___x_147_ = l_Float_Model_ofScientific(v_m_142_, v___y_146_);
lean_dec(v___y_146_);
v___x_148_ = lean_float_of_bits(v___x_147_);
return v___x_148_;
}
v___jp_149_:
{
if (v_s_143_ == 0)
{
lean_object* v___x_150_; 
v___x_150_ = lean_nat_to_int(v_e_144_);
v___y_146_ = v___x_150_;
goto v___jp_145_;
}
else
{
lean_object* v___x_151_; 
v___x_151_ = l_Int_negOfNat(v_e_144_);
lean_dec(v_e_144_);
v___y_146_ = v___x_151_;
goto v___jp_145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float_ofScientific___boxed(lean_object* v_m_166_, lean_object* v_s_167_, lean_object* v_e_168_){
_start:
{
uint8_t v_s_boxed_169_; double v_res_170_; lean_object* v_r_171_; 
v_s_boxed_169_ = lean_unbox(v_s_167_);
v_res_170_ = l_Float_ofScientific(v_m_166_, v_s_boxed_169_, v_e_168_);
v_r_171_ = lean_box_float(v_res_170_);
return v_r_171_;
}
}
LEAN_EXPORT double lean_float_of_nat(lean_object* v_n_174_){
_start:
{
uint8_t v___x_175_; lean_object* v___x_176_; double v___x_177_; 
v___x_175_ = 0;
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = l_Float_ofScientific(v_n_174_, v___x_175_, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Float_ofNat___boxed(lean_object* v_n_178_){
_start:
{
double v_res_179_; lean_object* v_r_180_; 
v_res_179_ = lean_float_of_nat(v_n_178_);
v_r_180_ = lean_box_float(v_res_179_);
return v_r_180_;
}
}
static lean_object* _init_l_Float_ofInt___closed__0(void){
_start:
{
lean_object* v_natZero_181_; lean_object* v_intZero_182_; 
v_natZero_181_ = lean_unsigned_to_nat(0u);
v_intZero_182_ = lean_nat_to_int(v_natZero_181_);
return v_intZero_182_;
}
}
LEAN_EXPORT double l_Float_ofInt(lean_object* v_x_183_){
_start:
{
lean_object* v_intZero_184_; uint8_t v_isNeg_185_; 
v_intZero_184_ = lean_obj_once(&l_Float_ofInt___closed__0, &l_Float_ofInt___closed__0_once, _init_l_Float_ofInt___closed__0);
v_isNeg_185_ = lean_int_dec_lt(v_x_183_, v_intZero_184_);
if (v_isNeg_185_ == 0)
{
lean_object* v_a_186_; double v___x_187_; 
v_a_186_ = lean_nat_abs(v_x_183_);
v___x_187_ = lean_float_of_nat(v_a_186_);
return v___x_187_;
}
else
{
lean_object* v_abs_188_; lean_object* v_one_189_; lean_object* v_a_190_; lean_object* v___x_191_; double v___x_192_; double v___x_193_; 
v_abs_188_ = lean_nat_abs(v_x_183_);
v_one_189_ = lean_unsigned_to_nat(1u);
v_a_190_ = lean_nat_sub(v_abs_188_, v_one_189_);
lean_dec(v_abs_188_);
v___x_191_ = lean_nat_add(v_a_190_, v_one_189_);
lean_dec(v_a_190_);
v___x_192_ = lean_float_of_nat(v___x_191_);
v___x_193_ = lean_float_negate(v___x_192_);
return v___x_193_;
}
}
}
LEAN_EXPORT lean_object* l_Float_ofInt___boxed(lean_object* v_x_194_){
_start:
{
double v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Float_ofInt(v_x_194_);
lean_dec(v_x_194_);
v_r_196_ = lean_box_float(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT double l_instOfNatFloat(lean_object* v_n_197_){
_start:
{
double v___x_198_; 
v___x_198_ = lean_float_of_nat(v_n_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_instOfNatFloat___boxed(lean_object* v_n_199_){
_start:
{
double v_res_200_; lean_object* v_r_201_; 
v_res_200_ = l_instOfNatFloat(v_n_199_);
v_r_201_ = lean_box_float(v_res_200_);
return v_r_201_;
}
}
LEAN_EXPORT double l_Nat_toFloat(lean_object* v_n_202_){
_start:
{
double v___x_203_; 
v___x_203_ = lean_float_of_nat(v_n_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Nat_toFloat___boxed(lean_object* v_n_204_){
_start:
{
double v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Nat_toFloat(v_n_204_);
v_r_206_ = lean_box_float(v_res_205_);
return v_r_206_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__0(void){
_start:
{
uint32_t v___x_207_; float v___x_208_; 
v___x_207_ = 1065353216;
v___x_208_ = lean_float32_of_bits(v___x_207_);
return v___x_208_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__1(void){
_start:
{
uint32_t v___x_209_; float v___x_210_; 
v___x_209_ = 1092616192;
v___x_210_ = lean_float32_of_bits(v___x_209_);
return v___x_210_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__2(void){
_start:
{
uint32_t v___x_211_; float v___x_212_; 
v___x_211_ = 1120403456;
v___x_212_ = lean_float32_of_bits(v___x_211_);
return v___x_212_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__3(void){
_start:
{
uint32_t v___x_213_; float v___x_214_; 
v___x_213_ = 1148846080;
v___x_214_ = lean_float32_of_bits(v___x_213_);
return v___x_214_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__4(void){
_start:
{
uint32_t v___x_215_; float v___x_216_; 
v___x_215_ = 1176256512;
v___x_216_ = lean_float32_of_bits(v___x_215_);
return v___x_216_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__5(void){
_start:
{
uint32_t v___x_217_; float v___x_218_; 
v___x_217_ = 1203982336;
v___x_218_ = lean_float32_of_bits(v___x_217_);
return v___x_218_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__6(void){
_start:
{
uint32_t v___x_219_; float v___x_220_; 
v___x_219_ = 1232348160;
v___x_220_ = lean_float32_of_bits(v___x_219_);
return v___x_220_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__7(void){
_start:
{
uint32_t v___x_221_; float v___x_222_; 
v___x_221_ = 1259902592;
v___x_222_ = lean_float32_of_bits(v___x_221_);
return v___x_222_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__8(void){
_start:
{
uint32_t v___x_223_; float v___x_224_; 
v___x_223_ = 1287568416;
v___x_224_ = lean_float32_of_bits(v___x_223_);
return v___x_224_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__9(void){
_start:
{
uint32_t v___x_225_; float v___x_226_; 
v___x_225_ = 1315859240;
v___x_226_ = lean_float32_of_bits(v___x_225_);
return v___x_226_;
}
}
static float _init_l_Float32_exactlyRepresentablePowersOfTen___closed__10(void){
_start:
{
uint32_t v___x_227_; float v___x_228_; 
v___x_227_ = 1343554297;
v___x_228_ = lean_float32_of_bits(v___x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__1(void){
_start:
{
float v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__10, &l_Float32_exactlyRepresentablePowersOfTen___closed__10_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__10);
v___x_230_ = lean_box_float32(v___x_229_);
return v___x_230_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__2(void){
_start:
{
float v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__9, &l_Float32_exactlyRepresentablePowersOfTen___closed__9_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__9);
v___x_232_ = lean_box_float32(v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__3(void){
_start:
{
float v___x_233_; lean_object* v___x_234_; 
v___x_233_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__8, &l_Float32_exactlyRepresentablePowersOfTen___closed__8_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__8);
v___x_234_ = lean_box_float32(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__4(void){
_start:
{
float v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__7, &l_Float32_exactlyRepresentablePowersOfTen___closed__7_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__7);
v___x_236_ = lean_box_float32(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__5(void){
_start:
{
float v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__6, &l_Float32_exactlyRepresentablePowersOfTen___closed__6_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__6);
v___x_238_ = lean_box_float32(v___x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__6(void){
_start:
{
float v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__5, &l_Float32_exactlyRepresentablePowersOfTen___closed__5_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__5);
v___x_240_ = lean_box_float32(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__7(void){
_start:
{
float v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__4, &l_Float32_exactlyRepresentablePowersOfTen___closed__4_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__4);
v___x_242_ = lean_box_float32(v___x_241_);
return v___x_242_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__8(void){
_start:
{
float v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__3, &l_Float32_exactlyRepresentablePowersOfTen___closed__3_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__3);
v___x_244_ = lean_box_float32(v___x_243_);
return v___x_244_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__9(void){
_start:
{
float v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__2, &l_Float32_exactlyRepresentablePowersOfTen___closed__2_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__2);
v___x_246_ = lean_box_float32(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__10(void){
_start:
{
float v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__1, &l_Float32_exactlyRepresentablePowersOfTen___closed__1_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__1);
v___x_248_ = lean_box_float32(v___x_247_);
return v___x_248_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__11(void){
_start:
{
float v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_float32_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__0, &l_Float32_exactlyRepresentablePowersOfTen___closed__0_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__0);
v___x_250_ = lean_box_float32(v___x_249_);
return v___x_250_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_251_ = lean_unsigned_to_nat(11u);
v___x_252_ = lean_mk_empty_array_with_capacity(v___x_251_);
v___x_253_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__11;
v___x_254_ = lean_array_push(v___x_252_, v___x_253_);
v___x_255_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__10;
v___x_256_ = lean_array_push(v___x_254_, v___x_255_);
v___x_257_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__9;
v___x_258_ = lean_array_push(v___x_256_, v___x_257_);
v___x_259_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__8;
v___x_260_ = lean_array_push(v___x_258_, v___x_259_);
v___x_261_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__7;
v___x_262_ = lean_array_push(v___x_260_, v___x_261_);
v___x_263_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__6;
v___x_264_ = lean_array_push(v___x_262_, v___x_263_);
v___x_265_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__5;
v___x_266_ = lean_array_push(v___x_264_, v___x_265_);
v___x_267_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__4;
v___x_268_ = lean_array_push(v___x_266_, v___x_267_);
v___x_269_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__3;
v___x_270_ = lean_array_push(v___x_268_, v___x_269_);
v___x_271_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__2;
v___x_272_ = lean_array_push(v___x_270_, v___x_271_);
v___x_273_ = l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__1;
v___x_274_ = lean_array_push(v___x_272_, v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Float32_exactlyRepresentablePowersOfTen(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = lean_obj_once(&l_Float32_exactlyRepresentablePowersOfTen___closed__11, &l_Float32_exactlyRepresentablePowersOfTen___closed__11_once, _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11);
return v___x_275_;
}
}
LEAN_EXPORT float l_Float32_ofScientific(lean_object* v_m_276_, uint8_t v_s_277_, lean_object* v_e_278_){
_start:
{
lean_object* v___y_280_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_unsigned_to_nat(8388608u);
v___x_287_ = lean_nat_dec_lt(v_m_276_, v___x_286_);
if (v___x_287_ == 0)
{
goto v___jp_283_;
}
else
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(10u);
v___x_289_ = lean_nat_dec_le(v_e_278_, v___x_288_);
if (v___x_289_ == 0)
{
goto v___jp_283_;
}
else
{
lean_object* v___x_290_; lean_object* v_powerOfTen_291_; 
v___x_290_ = l_Float32_exactlyRepresentablePowersOfTen;
v_powerOfTen_291_ = lean_array_fget_borrowed(v___x_290_, v_e_278_);
lean_dec(v_e_278_);
if (v_s_277_ == 0)
{
uint64_t v___x_292_; float v___x_293_; float v___x_294_; float v___x_295_; 
v___x_292_ = lean_uint64_of_nat(v_m_276_);
lean_dec(v_m_276_);
v___x_293_ = lean_uint64_to_float32(v___x_292_);
v___x_294_ = lean_unbox_float32(v_powerOfTen_291_);
v___x_295_ = lean_float32_mul(v___x_293_, v___x_294_);
return v___x_295_;
}
else
{
uint64_t v___x_296_; float v___x_297_; float v___x_298_; float v___x_299_; 
v___x_296_ = lean_uint64_of_nat(v_m_276_);
lean_dec(v_m_276_);
v___x_297_ = lean_uint64_to_float32(v___x_296_);
v___x_298_ = lean_unbox_float32(v_powerOfTen_291_);
v___x_299_ = lean_float32_div(v___x_297_, v___x_298_);
return v___x_299_;
}
}
}
v___jp_279_:
{
uint32_t v___x_281_; float v___x_282_; 
v___x_281_ = l_Float32_Model_ofScientific(v_m_276_, v___y_280_);
lean_dec(v___y_280_);
v___x_282_ = lean_float32_of_bits(v___x_281_);
return v___x_282_;
}
v___jp_283_:
{
if (v_s_277_ == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_nat_to_int(v_e_278_);
v___y_280_ = v___x_284_;
goto v___jp_279_;
}
else
{
lean_object* v___x_285_; 
v___x_285_ = l_Int_negOfNat(v_e_278_);
lean_dec(v_e_278_);
v___y_280_ = v___x_285_;
goto v___jp_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Float32_ofScientific___boxed(lean_object* v_m_300_, lean_object* v_s_301_, lean_object* v_e_302_){
_start:
{
uint8_t v_s_boxed_303_; float v_res_304_; lean_object* v_r_305_; 
v_s_boxed_303_ = lean_unbox(v_s_301_);
v_res_304_ = l_Float32_ofScientific(v_m_300_, v_s_boxed_303_, v_e_302_);
v_r_305_ = lean_box_float32(v_res_304_);
return v_r_305_;
}
}
LEAN_EXPORT float lean_float32_of_nat(lean_object* v_n_308_){
_start:
{
uint8_t v___x_309_; lean_object* v___x_310_; float v___x_311_; 
v___x_309_ = 0;
v___x_310_ = lean_unsigned_to_nat(0u);
v___x_311_ = l_Float32_ofScientific(v_n_308_, v___x_309_, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Float32_ofNat___boxed(lean_object* v_n_312_){
_start:
{
float v_res_313_; lean_object* v_r_314_; 
v_res_313_ = lean_float32_of_nat(v_n_312_);
v_r_314_ = lean_box_float32(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT float l_Float32_ofInt(lean_object* v_x_315_){
_start:
{
lean_object* v_intZero_316_; uint8_t v_isNeg_317_; 
v_intZero_316_ = lean_obj_once(&l_Float_ofInt___closed__0, &l_Float_ofInt___closed__0_once, _init_l_Float_ofInt___closed__0);
v_isNeg_317_ = lean_int_dec_lt(v_x_315_, v_intZero_316_);
if (v_isNeg_317_ == 0)
{
lean_object* v_a_318_; float v___x_319_; 
v_a_318_ = lean_nat_abs(v_x_315_);
v___x_319_ = lean_float32_of_nat(v_a_318_);
return v___x_319_;
}
else
{
lean_object* v_abs_320_; lean_object* v_one_321_; lean_object* v_a_322_; lean_object* v___x_323_; float v___x_324_; float v___x_325_; 
v_abs_320_ = lean_nat_abs(v_x_315_);
v_one_321_ = lean_unsigned_to_nat(1u);
v_a_322_ = lean_nat_sub(v_abs_320_, v_one_321_);
lean_dec(v_abs_320_);
v___x_323_ = lean_nat_add(v_a_322_, v_one_321_);
lean_dec(v_a_322_);
v___x_324_ = lean_float32_of_nat(v___x_323_);
v___x_325_ = lean_float32_negate(v___x_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Float32_ofInt___boxed(lean_object* v_x_326_){
_start:
{
float v_res_327_; lean_object* v_r_328_; 
v_res_327_ = l_Float32_ofInt(v_x_326_);
lean_dec(v_x_326_);
v_r_328_ = lean_box_float32(v_res_327_);
return v_r_328_;
}
}
LEAN_EXPORT float l_instOfNatFloat32(lean_object* v_n_329_){
_start:
{
float v___x_330_; 
v___x_330_ = lean_float32_of_nat(v_n_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_instOfNatFloat32___boxed(lean_object* v_n_331_){
_start:
{
float v_res_332_; lean_object* v_r_333_; 
v_res_332_ = l_instOfNatFloat32(v_n_331_);
v_r_333_ = lean_box_float32(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT float l_Nat_toFloat32(lean_object* v_n_334_){
_start:
{
float v___x_335_; 
v___x_335_ = lean_float32_of_nat(v_n_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Nat_toFloat32___boxed(lean_object* v_n_336_){
_start:
{
float v_res_337_; lean_object* v_r_338_; 
v_res_337_ = l_Nat_toFloat32(v_n_336_);
v_r_338_ = lean_box_float32(v_res_337_);
return v_r_338_;
}
}
lean_object* runtime_initialize_Init_Data_Float_Float32(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Lemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_OfScientific(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Float_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__1 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__1();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__1);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__2 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__2();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__2);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__3 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__3();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__3);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__4 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__4();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__4);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__5 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__5();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__5);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__6 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__6();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__6);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__7 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__7();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__7);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__8 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__8();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__8);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__9 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__9();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__9);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__10 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__10();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__10);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__11 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__11();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__11);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__12 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__12();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__12);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__13 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__13();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__13);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__14 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__14();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__14);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__15 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__15();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__15);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__16 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__16();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__16);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__17 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__17();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__17);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__18 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__18();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__18);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__19 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__19();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__19);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__20 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__20();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__20);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__21 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__21();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__21);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__22 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__22();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__22);
l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__23 = _init_l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__23();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen___closed__23___boxed__const__23);
l_Float_exactlyRepresentablePowersOfTen = _init_l_Float_exactlyRepresentablePowersOfTen();
lean_mark_persistent(l_Float_exactlyRepresentablePowersOfTen);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__1 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__1();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__1);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__2 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__2();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__2);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__3 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__3();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__3);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__4 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__4();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__4);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__5 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__5();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__5);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__6 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__6();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__6);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__7 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__7();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__7);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__8 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__8();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__8);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__9 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__9();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__9);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__10 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__10();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__10);
l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__11 = _init_l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__11();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen___closed__11___boxed__const__11);
l_Float32_exactlyRepresentablePowersOfTen = _init_l_Float32_exactlyRepresentablePowersOfTen();
lean_mark_persistent(l_Float32_exactlyRepresentablePowersOfTen);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_OfScientific(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Float_Float32(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_Meta(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_OfScientific(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float_Float32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_OfScientific(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_OfScientific(builtin);
}
#ifdef __cplusplus
}
#endif
