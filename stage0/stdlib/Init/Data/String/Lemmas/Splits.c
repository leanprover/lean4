// Lean compiler output
// Module: Init.Data.String.Lemmas.Splits
// Imports: public import Init.Data.String.Basic public import Init.Data.String.FindPos import Init.Data.ByteArray.Lemmas import Init.Data.String.Lemmas.Basic import Init.Data.Nat.MinMax import Init.Data.String.Lemmas.IsEmpty import Init.Data.String.Lemmas.Order import Init.Data.String.OrderInstances import Init.Data.Nat.Order import Init.Omega import Init.Data.String.Lemmas.FindPos import Init.Data.List.TakeDrop import Init.Data.List.Nat.TakeDrop
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
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateRight___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateRight___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateLeft___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateRight___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateRight___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateLeft___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateLeft___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofEqAppend___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofEqAppend___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofEqAppend(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofEqAppend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofEqAppend___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofEqAppend___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofEqAppend(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_ofEqAppend___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateRight___redArg(lean_object* v_p_1_, lean_object* v_t_u2082_2_){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_string_utf8_byte_size(v_t_u2082_2_);
v___x_4_ = lean_nat_add(v_p_1_, v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateRight___redArg___boxed(lean_object* v_p_5_, lean_object* v_t_u2082_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_String_Slice_Pos_Splits_rotateRight___redArg(v_p_5_, v_t_u2082_6_);
lean_dec_ref(v_t_u2082_6_);
lean_dec(v_p_5_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateRight(lean_object* v_s_8_, lean_object* v_p_9_, lean_object* v_t_u2081_10_, lean_object* v_t_u2082_11_, lean_object* v_t_u2083_12_, lean_object* v_h_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = lean_string_utf8_byte_size(v_t_u2082_11_);
v___x_15_ = lean_nat_add(v_p_9_, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateRight___boxed(lean_object* v_s_16_, lean_object* v_p_17_, lean_object* v_t_u2081_18_, lean_object* v_t_u2082_19_, lean_object* v_t_u2083_20_, lean_object* v_h_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_String_Slice_Pos_Splits_rotateRight(v_s_16_, v_p_17_, v_t_u2081_18_, v_t_u2082_19_, v_t_u2083_20_, v_h_21_);
lean_dec_ref(v_t_u2083_20_);
lean_dec_ref(v_t_u2082_19_);
lean_dec_ref(v_t_u2081_18_);
lean_dec(v_p_17_);
lean_dec_ref(v_s_16_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateLeft___redArg(lean_object* v_t_u2081_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_string_utf8_byte_size(v_t_u2081_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateLeft___redArg___boxed(lean_object* v_t_u2081_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_String_Slice_Pos_Splits_rotateLeft___redArg(v_t_u2081_25_);
lean_dec_ref(v_t_u2081_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateLeft(lean_object* v_s_27_, lean_object* v_p_28_, lean_object* v_t_u2081_29_, lean_object* v_t_u2082_30_, lean_object* v_t_u2083_31_, lean_object* v_h_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_string_utf8_byte_size(v_t_u2081_29_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_Splits_rotateLeft___boxed(lean_object* v_s_34_, lean_object* v_p_35_, lean_object* v_t_u2081_36_, lean_object* v_t_u2082_37_, lean_object* v_t_u2083_38_, lean_object* v_h_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_String_Slice_Pos_Splits_rotateLeft(v_s_34_, v_p_35_, v_t_u2081_36_, v_t_u2082_37_, v_t_u2083_38_, v_h_39_);
lean_dec_ref(v_t_u2083_38_);
lean_dec_ref(v_t_u2082_37_);
lean_dec_ref(v_t_u2081_36_);
lean_dec(v_p_35_);
lean_dec_ref(v_s_34_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateRight___redArg(lean_object* v_p_41_, lean_object* v_t_u2082_42_){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_string_utf8_byte_size(v_t_u2082_42_);
v___x_44_ = lean_nat_add(v_p_41_, v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateRight___redArg___boxed(lean_object* v_p_45_, lean_object* v_t_u2082_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_String_Pos_Splits_rotateRight___redArg(v_p_45_, v_t_u2082_46_);
lean_dec_ref(v_t_u2082_46_);
lean_dec(v_p_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateRight(lean_object* v_s_48_, lean_object* v_p_49_, lean_object* v_t_u2081_50_, lean_object* v_t_u2082_51_, lean_object* v_t_u2083_52_, lean_object* v_h_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_string_utf8_byte_size(v_t_u2082_51_);
v___x_55_ = lean_nat_add(v_p_49_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateRight___boxed(lean_object* v_s_56_, lean_object* v_p_57_, lean_object* v_t_u2081_58_, lean_object* v_t_u2082_59_, lean_object* v_t_u2083_60_, lean_object* v_h_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_String_Pos_Splits_rotateRight(v_s_56_, v_p_57_, v_t_u2081_58_, v_t_u2082_59_, v_t_u2083_60_, v_h_61_);
lean_dec_ref(v_t_u2083_60_);
lean_dec_ref(v_t_u2082_59_);
lean_dec_ref(v_t_u2081_58_);
lean_dec(v_p_57_);
lean_dec_ref(v_s_56_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateLeft___redArg(lean_object* v_t_u2081_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_string_utf8_byte_size(v_t_u2081_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateLeft___redArg___boxed(lean_object* v_t_u2081_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_String_Pos_Splits_rotateLeft___redArg(v_t_u2081_65_);
lean_dec_ref(v_t_u2081_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateLeft(lean_object* v_s_67_, lean_object* v_p_68_, lean_object* v_t_u2081_69_, lean_object* v_t_u2082_70_, lean_object* v_t_u2083_71_, lean_object* v_h_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_string_utf8_byte_size(v_t_u2081_69_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Splits_rotateLeft___boxed(lean_object* v_s_74_, lean_object* v_p_75_, lean_object* v_t_u2081_76_, lean_object* v_t_u2082_77_, lean_object* v_t_u2083_78_, lean_object* v_h_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_String_Pos_Splits_rotateLeft(v_s_74_, v_p_75_, v_t_u2081_76_, v_t_u2082_77_, v_t_u2083_78_, v_h_79_);
lean_dec_ref(v_t_u2083_78_);
lean_dec_ref(v_t_u2082_77_);
lean_dec_ref(v_t_u2081_76_);
lean_dec(v_p_75_);
lean_dec_ref(v_s_74_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofEqAppend___redArg(lean_object* v_t_u2081_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = lean_string_utf8_byte_size(v_t_u2081_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofEqAppend___redArg___boxed(lean_object* v_t_u2081_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_String_Slice_Pos_ofEqAppend___redArg(v_t_u2081_83_);
lean_dec_ref(v_t_u2081_83_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofEqAppend(lean_object* v_s_85_, lean_object* v_t_u2081_86_, lean_object* v_t_u2082_87_, lean_object* v_h_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_string_utf8_byte_size(v_t_u2081_86_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_ofEqAppend___boxed(lean_object* v_s_90_, lean_object* v_t_u2081_91_, lean_object* v_t_u2082_92_, lean_object* v_h_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_String_Slice_Pos_ofEqAppend(v_s_90_, v_t_u2081_91_, v_t_u2082_92_, v_h_93_);
lean_dec_ref(v_t_u2082_92_);
lean_dec_ref(v_t_u2081_91_);
lean_dec_ref(v_s_90_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofEqAppend___redArg(lean_object* v_t_u2081_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = lean_string_utf8_byte_size(v_t_u2081_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofEqAppend___redArg___boxed(lean_object* v_t_u2081_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_String_Pos_ofEqAppend___redArg(v_t_u2081_97_);
lean_dec_ref(v_t_u2081_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofEqAppend(lean_object* v_s_99_, lean_object* v_t_u2081_100_, lean_object* v_t_u2082_101_, lean_object* v_h_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_string_utf8_byte_size(v_t_u2081_100_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_ofEqAppend___boxed(lean_object* v_s_104_, lean_object* v_t_u2081_105_, lean_object* v_t_u2082_106_, lean_object* v_h_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_String_Pos_ofEqAppend(v_s_104_, v_t_u2081_105_, v_t_u2082_106_, v_h_107_);
lean_dec_ref(v_t_u2082_106_);
lean_dec_ref(v_t_u2081_105_);
lean_dec_ref(v_s_104_);
return v_res_108_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_ByteArray_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_IsEmpty(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Order(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Order(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_Splits(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ByteArray_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_Splits(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_Splits(builtin);
}
#ifdef __cplusplus
}
#endif
