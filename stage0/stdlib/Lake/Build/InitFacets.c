// Lean compiler output
// Module: Lake.Build.InitFacets
// Imports: public import Lake.Config.FacetConfig import Lake.Build.Module import Lake.Build.Package import Lake.Build.Library import Lake.Build.Executable import Lake.Build.ExternLib import Lake.Build.InputFile
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
extern lean_object* l_Lake_ExternLib_initFacetConfigs;
extern lean_object* l_Lake_LeanExe_initFacetConfigs;
extern lean_object* l_Lake_LeanLib_initFacetConfigs;
extern lean_object* l_Lake_Package_initFacetConfigs;
extern lean_object* l_Lake_Module_initFacetConfigs;
lean_object* l_Lake_FacetConfigMap_insert(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_InputFile_initFacetConfigs;
extern lean_object* l_Lake_InputDir_initFacetConfigs;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_initFacetConfigs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__0;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__1;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__2;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__3;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__4;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__5;
static lean_once_cell_t l_Lake_initFacetConfigs___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_initFacetConfigs___closed__6;
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(lean_object* v_init_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_v_4_; lean_object* v_l_5_; lean_object* v_r_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_k_3_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_k_3_);
v_v_4_ = lean_ctor_get(v_x_2_, 2);
lean_inc(v_v_4_);
v_l_5_ = lean_ctor_get(v_x_2_, 3);
lean_inc(v_l_5_);
v_r_6_ = lean_ctor_get(v_x_2_, 4);
lean_inc(v_r_6_);
lean_dec_ref(v_x_2_);
v___x_7_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v_init_1_, v_l_5_);
v___x_8_ = l_Lake_FacetConfigMap_insert(v_k_3_, v_v_4_, v___x_7_);
v_init_1_ = v___x_8_;
v_x_2_ = v_r_6_;
goto _start;
}
else
{
return v_init_1_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert___redArg(lean_object* v_group_10_, lean_object* v_map_11_){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v_map_11_, v_group_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert(lean_object* v_k_13_, lean_object* v_group_14_, lean_object* v_map_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v_map_15_, v_group_14_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert___boxed(lean_object* v_k_17_, lean_object* v_group_18_, lean_object* v_map_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert(v_k_17_, v_group_18_, v_map_19_);
lean_dec(v_k_17_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0(lean_object* v_init_21_, lean_object* v_t_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v_init_21_, v_t_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__0(void){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = l_Lake_Module_initFacetConfigs;
v___x_25_ = lean_box(1);
v___x_26_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_25_, v___x_24_);
return v___x_26_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__1(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = l_Lake_Package_initFacetConfigs;
v___x_28_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__0, &l_Lake_initFacetConfigs___closed__0_once, _init_l_Lake_initFacetConfigs___closed__0);
v___x_29_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_28_, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__2(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = l_Lake_LeanLib_initFacetConfigs;
v___x_31_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__1, &l_Lake_initFacetConfigs___closed__1_once, _init_l_Lake_initFacetConfigs___closed__1);
v___x_32_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_31_, v___x_30_);
return v___x_32_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__3(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = l_Lake_LeanExe_initFacetConfigs;
v___x_34_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__2, &l_Lake_initFacetConfigs___closed__2_once, _init_l_Lake_initFacetConfigs___closed__2);
v___x_35_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__4(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = l_Lake_ExternLib_initFacetConfigs;
v___x_37_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__3, &l_Lake_initFacetConfigs___closed__3_once, _init_l_Lake_initFacetConfigs___closed__3);
v___x_38_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_37_, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__5(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = l_Lake_InputFile_initFacetConfigs;
v___x_40_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__4, &l_Lake_initFacetConfigs___closed__4_once, _init_l_Lake_initFacetConfigs___closed__4);
v___x_41_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_40_, v___x_39_);
return v___x_41_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__6(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_42_ = l_Lake_InputDir_initFacetConfigs;
v___x_43_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__5, &l_Lake_initFacetConfigs___closed__5_once, _init_l_Lake_initFacetConfigs___closed__5);
v___x_44_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lake_Build_InitFacets_0__Lake_initFacetConfigs_insert_spec__0_spec__0(v___x_43_, v___x_42_);
return v___x_44_;
}
}
static lean_object* _init_l_Lake_initFacetConfigs(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_obj_once(&l_Lake_initFacetConfigs___closed__6, &l_Lake_initFacetConfigs___closed__6_once, _init_l_Lake_initFacetConfigs___closed__6);
return v___x_45_;
}
}
lean_object* runtime_initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Module(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Package(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Library(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_Executable(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_ExternLib(uint8_t builtin);
lean_object* runtime_initialize_Lake_Build_InputFile(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_InitFacets(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Library(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Executable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_ExternLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_initFacetConfigs = _init_l_Lake_initFacetConfigs();
lean_mark_persistent(l_Lake_initFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_InitFacets(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Config_FacetConfig(uint8_t builtin);
lean_object* initialize_Lake_Build_Module(uint8_t builtin);
lean_object* initialize_Lake_Build_Package(uint8_t builtin);
lean_object* initialize_Lake_Build_Library(uint8_t builtin);
lean_object* initialize_Lake_Build_Executable(uint8_t builtin);
lean_object* initialize_Lake_Build_ExternLib(uint8_t builtin);
lean_object* initialize_Lake_Build_InputFile(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_InitFacets(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_FacetConfig(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Library(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Executable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_ExternLib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_InputFile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_InitFacets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_InitFacets(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_InitFacets(builtin);
}
#ifdef __cplusplus
}
#endif
