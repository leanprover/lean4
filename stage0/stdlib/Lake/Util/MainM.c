// Lean compiler output
// Module: Lake.Util.MainM
// Imports: public import Lake.Util.Log public import Lake.Util.Exit
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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lake_OutStream_get(lean_object*);
uint8_t l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_instMonadST(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lake_Log_maxLv(lean_object*);
uint8_t l_Lake_instOrdLogLevel_ord(uint8_t, uint8_t);
lean_object* l_instMonadEST(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_instMonadFinallyEST___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_instMonadMainM___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadMainM___closed__0;
LEAN_EXPORT lean_object* l_Lake_instMonadMainM;
static const lean_closure_object l_Lake_instMonadFinallyMainM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadFinallyEST___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadFinallyMainM___closed__0 = (const lean_object*)&l_Lake_instMonadFinallyMainM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadFinallyMainM = (const lean_object*)&l_Lake_instMonadFinallyMainM___closed__0_value;
static const lean_closure_object l_Lake_instMonadLiftBaseIOMainM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadLiftBaseIOEIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadLiftBaseIOMainM___closed__0 = (const lean_object*)&l_Lake_instMonadLiftBaseIOMainM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadLiftBaseIOMainM = (const lean_object*)&l_Lake_instMonadLiftBaseIOMainM___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_mk___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_mk___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_mk(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_mk___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_MainM_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_run___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_MainM_run(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_run___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_exit___redArg(uint32_t);
LEAN_EXPORT lean_object* l_Lake_MainM_exit___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_exit(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_MainM_exit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadExit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_exit___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MainM_instMonadExit___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadExit___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadExit = (const lean_object*)&l_Lake_MainM_instMonadExit___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg();
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_failure(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_failure___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_orElse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_failure___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0 = (const lean_object*)&l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0_value;
static const lean_closure_object l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_orElse___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1 = (const lean_object*)&l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative;
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLog___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLog___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadLog___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_instMonadLog___lam__0___boxed, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_MainM_instMonadLog___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadLog___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadLog = (const lean_object*)&l_Lake_MainM_instMonadLog___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_error___redArg(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_MainM_error___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_error(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_MainM_error___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadError___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadError___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_instMonadError___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MainM_instMonadError___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadError___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadError = (const lean_object*)&l_Lake_MainM_instMonadError___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLiftIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLiftIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadLiftIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_instMonadLiftIO___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MainM_instMonadLiftIO___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadLiftIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadLiftIO = (const lean_object*)&l_Lake_MainM_instMonadLiftIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_MainM_runLogIO___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_MainM_runLogIO___redArg___closed__0;
static const lean_array_object l_Lake_MainM_runLogIO___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_MainM_runLogIO___redArg___closed__1 = (const lean_object*)&l_Lake_MainM_runLogIO___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadLiftLogIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_liftLogIO___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MainM_instMonadLiftLogIO___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadLiftLogIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadLiftLogIO = (const lean_object*)&l_Lake_MainM_instMonadLiftLogIO___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_MainM_liftLoggerIO___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_MainM_instMonadLiftLoggerIO___closed__0 = (const lean_object*)&l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_MainM_instMonadLiftLoggerIO = (const lean_object*)&l_Lake_MainM_instMonadLiftLoggerIO___closed__0_value;
static lean_object* _init_l_Lake_instMonadMainM___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lake_instMonadMainM(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_once(&l_Lake_instMonadMainM___closed__0, &l_Lake_instMonadMainM___closed__0_once, _init_l_Lake_instMonadMainM___closed__0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_mk___redArg(lean_object* v_x_7_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_1(v_x_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_mk___redArg___boxed(lean_object* v_x_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lake_MainM_mk___redArg(v_x_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_mk(lean_object* v_00_u03b1_13_, lean_object* v_x_14_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_apply_1(v_x_14_, lean_box(0));
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_mk___boxed(lean_object* v_00_u03b1_17_, lean_object* v_x_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lake_MainM_mk(v_00_u03b1_17_, v_x_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___redArg(lean_object* v_self_21_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_apply_1(v_self_21_, lean_box(0));
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___redArg___boxed(lean_object* v_self_24_, lean_object* v_a_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lake_MainM_toEIO___redArg(v_self_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO(lean_object* v_00_u03b1_27_, lean_object* v_self_28_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lean_apply_1(v_self_28_, lean_box(0));
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toEIO___boxed(lean_object* v_00_u03b1_31_, lean_object* v_self_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lake_MainM_toEIO(v_00_u03b1_31_, v_self_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___redArg(lean_object* v_self_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_apply_1(v_self_35_, lean_box(0));
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_37_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_37_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
lean_ctor_set_tag(v___x_40_, 1);
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___x_37_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_37_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_37_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_37_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
lean_ctor_set_tag(v___x_48_, 0);
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___redArg___boxed(lean_object* v_self_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_MainM_toBaseIO___redArg(v_self_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO(lean_object* v_00_u03b1_57_, lean_object* v_self_58_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_apply_1(v_self_58_, lean_box(0));
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
v_a_61_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_60_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_60_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
lean_ctor_set_tag(v___x_63_, 1);
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
else
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
v_a_69_ = lean_ctor_get(v___x_60_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v___x_60_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_60_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set_tag(v___x_71_, 0);
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_toBaseIO___boxed(lean_object* v_00_u03b1_77_, lean_object* v_self_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lake_MainM_toBaseIO(v_00_u03b1_77_, v_self_78_);
return v_res_80_;
}
}
LEAN_EXPORT uint32_t l_Lake_MainM_run___redArg(lean_object* v_self_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = lean_apply_1(v_self_81_, lean_box(0));
if (lean_obj_tag(v___x_83_) == 0)
{
uint32_t v___x_84_; 
lean_dec_ref(v___x_83_);
v___x_84_ = 0;
return v___x_84_;
}
else
{
lean_object* v_a_85_; uint32_t v___x_86_; 
v_a_85_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_a_85_);
lean_dec_ref(v___x_83_);
v___x_86_ = lean_unbox_uint32(v_a_85_);
lean_dec(v_a_85_);
return v___x_86_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_run___redArg___boxed(lean_object* v_self_87_, lean_object* v_a_88_){
_start:
{
uint32_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lake_MainM_run___redArg(v_self_87_);
v_r_90_ = lean_box_uint32(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT uint32_t l_Lake_MainM_run(lean_object* v_00_u03b1_91_, lean_object* v_self_92_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_apply_1(v_self_92_, lean_box(0));
if (lean_obj_tag(v___x_94_) == 0)
{
uint32_t v___x_95_; 
lean_dec_ref(v___x_94_);
v___x_95_ = 0;
return v___x_95_;
}
else
{
lean_object* v_a_96_; uint32_t v___x_97_; 
v_a_96_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_96_);
lean_dec_ref(v___x_94_);
v___x_97_ = lean_unbox_uint32(v_a_96_);
lean_dec(v_a_96_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_run___boxed(lean_object* v_00_u03b1_98_, lean_object* v_self_99_, lean_object* v_a_100_){
_start:
{
uint32_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Lake_MainM_run(v_00_u03b1_98_, v_self_99_);
v_r_102_ = lean_box_uint32(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_exit___redArg(uint32_t v_rc_103_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_box_uint32(v_rc_103_);
v___x_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_exit___redArg___boxed(lean_object* v_rc_107_, lean_object* v_a_108_){
_start:
{
uint32_t v_rc_boxed_109_; lean_object* v_res_110_; 
v_rc_boxed_109_ = lean_unbox_uint32(v_rc_107_);
lean_dec(v_rc_107_);
v_res_110_ = l_Lake_MainM_exit___redArg(v_rc_boxed_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_exit(lean_object* v_00_u03b1_111_, uint32_t v_rc_112_){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_box_uint32(v_rc_112_);
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_exit___boxed(lean_object* v_00_u03b1_116_, lean_object* v_rc_117_, lean_object* v_a_118_){
_start:
{
uint32_t v_rc_boxed_119_; lean_object* v_res_120_; 
v_rc_boxed_119_ = lean_unbox_uint32(v_rc_117_);
lean_dec(v_rc_117_);
v_res_120_ = l_Lake_MainM_exit(v_00_u03b1_116_, v_rc_boxed_119_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___redArg(lean_object* v_f_123_, lean_object* v_self_124_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = lean_apply_1(v_self_124_, lean_box(0));
if (lean_obj_tag(v___x_126_) == 0)
{
lean_dec_ref(v_f_123_);
return v___x_126_;
}
else
{
lean_object* v_a_127_; lean_object* v___x_128_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
lean_dec_ref(v___x_126_);
v___x_128_ = lean_apply_2(v_f_123_, v_a_127_, lean_box(0));
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___redArg___boxed(lean_object* v_f_129_, lean_object* v_self_130_, lean_object* v_a_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lake_MainM_tryCatchExit___redArg(v_f_129_, v_self_130_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit(lean_object* v_00_u03b1_133_, lean_object* v_f_134_, lean_object* v_self_135_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = lean_apply_1(v_self_135_, lean_box(0));
if (lean_obj_tag(v___x_137_) == 0)
{
lean_dec_ref(v_f_134_);
return v___x_137_;
}
else
{
lean_object* v_a_138_; lean_object* v___x_139_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref(v___x_137_);
v___x_139_ = lean_apply_2(v_f_134_, v_a_138_, lean_box(0));
return v___x_139_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchExit___boxed(lean_object* v_00_u03b1_140_, lean_object* v_f_141_, lean_object* v_self_142_, lean_object* v_a_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l_Lake_MainM_tryCatchExit(v_00_u03b1_140_, v_f_141_, v_self_142_);
return v_res_144_;
}
}
static lean_object* _init_l_Lake_MainM_tryCatchError___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_145_; lean_object* v___x_146_; 
v___x_145_ = 0;
v___x_146_ = lean_box_uint32(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg(lean_object* v_f_147_, lean_object* v_self_148_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = lean_apply_1(v_self_148_, lean_box(0));
if (lean_obj_tag(v___x_150_) == 0)
{
lean_dec_ref(v_f_147_);
return v___x_150_;
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_163_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_163_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_163_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_163_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
uint32_t v___x_155_; uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_155_ = 0;
v___x_156_ = lean_unbox_uint32(v_a_151_);
v___x_157_ = lean_uint32_dec_eq(v___x_156_, v___x_155_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
lean_del_object(v___x_153_);
v___x_158_ = lean_apply_2(v_f_147_, v_a_151_, lean_box(0));
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_161_; 
lean_dec(v_a_151_);
lean_dec_ref(v_f_147_);
v___x_159_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 0, v___x_159_);
v___x_161_ = v___x_153_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___redArg___boxed(lean_object* v_f_164_, lean_object* v_self_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lake_MainM_tryCatchError___redArg(v_f_164_, v_self_165_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError(lean_object* v_00_u03b1_168_, lean_object* v_f_169_, lean_object* v_self_170_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lean_apply_1(v_self_170_, lean_box(0));
if (lean_obj_tag(v___x_172_) == 0)
{
lean_dec_ref(v_f_169_);
return v___x_172_;
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_185_; 
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_185_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_185_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
uint32_t v___x_177_; uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_177_ = 0;
v___x_178_ = lean_unbox_uint32(v_a_173_);
v___x_179_ = lean_uint32_dec_eq(v___x_178_, v___x_177_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; 
lean_del_object(v___x_175_);
v___x_180_ = lean_apply_2(v_f_169_, v_a_173_, lean_box(0));
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_dec(v_a_173_);
lean_dec_ref(v_f_169_);
v___x_181_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_181_);
v___x_183_ = v___x_175_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_tryCatchError___boxed(lean_object* v_00_u03b1_186_, lean_object* v_f_187_, lean_object* v_self_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Lake_MainM_tryCatchError(v_00_u03b1_186_, v_f_187_, v_self_188_);
return v_res_190_;
}
}
static lean_object* _init_l_Lake_MainM_failure___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_191_; lean_object* v___x_192_; 
v___x_191_ = 1;
v___x_192_ = lean_box_uint32(v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg(){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_failure___redArg___boxed(lean_object* v_a_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lake_MainM_failure___redArg();
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_failure(lean_object* v_00_u03b1_198_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_failure___boxed(lean_object* v_00_u03b1_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lake_MainM_failure(v_00_u03b1_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___redArg(lean_object* v_self_205_, lean_object* v_other_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_apply_1(v_self_205_, lean_box(0));
if (lean_obj_tag(v___x_208_) == 0)
{
lean_dec_ref(v_other_206_);
return v___x_208_;
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_222_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_222_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_222_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_222_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
uint32_t v___x_213_; uint32_t v___x_214_; uint8_t v___x_215_; 
v___x_213_ = 0;
v___x_214_ = lean_unbox_uint32(v_a_209_);
lean_dec(v_a_209_);
v___x_215_ = lean_uint32_dec_eq(v___x_214_, v___x_213_);
if (v___x_215_ == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_del_object(v___x_211_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_apply_2(v_other_206_, v___x_216_, lean_box(0));
return v___x_217_;
}
else
{
lean_object* v___x_218_; lean_object* v___x_220_; 
lean_dec_ref(v_other_206_);
v___x_218_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_218_);
v___x_220_ = v___x_211_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___redArg___boxed(lean_object* v_self_223_, lean_object* v_other_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lake_MainM_orElse___redArg(v_self_223_, v_other_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_orElse(lean_object* v_00_u03b1_227_, lean_object* v_self_228_, lean_object* v_other_229_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_apply_1(v_self_228_, lean_box(0));
if (lean_obj_tag(v___x_231_) == 0)
{
lean_dec_ref(v_other_229_);
return v___x_231_;
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_245_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_245_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_245_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_245_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
uint32_t v___x_236_; uint32_t v___x_237_; uint8_t v___x_238_; 
v___x_236_ = 0;
v___x_237_ = lean_unbox_uint32(v_a_232_);
lean_dec(v_a_232_);
v___x_238_ = lean_uint32_dec_eq(v___x_237_, v___x_236_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; 
lean_del_object(v___x_234_);
v___x_239_ = lean_box(0);
v___x_240_ = lean_apply_2(v_other_229_, v___x_239_, lean_box(0));
return v___x_240_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_243_; 
lean_dec_ref(v_other_229_);
v___x_241_ = l_Lake_MainM_tryCatchError___redArg___boxed__const__1;
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_241_);
v___x_243_ = v___x_234_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_orElse___boxed(lean_object* v_00_u03b1_246_, lean_object* v_self_247_, lean_object* v_other_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lake_MainM_orElse(v_00_u03b1_246_, v_self_247_, v_other_248_);
return v_res_250_;
}
}
static lean_object* _init_l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative(void){
_start:
{
lean_object* v___x_253_; lean_object* v_toApplicative_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_253_ = lean_obj_once(&l_Lake_instMonadMainM___closed__0, &l_Lake_instMonadMainM___closed__0_once, _init_l_Lake_instMonadMainM___closed__0);
v_toApplicative_254_ = lean_ctor_get(v___x_253_, 0);
lean_inc_ref(v_toApplicative_254_);
v___x_255_ = ((lean_object*)(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__0));
v___x_256_ = ((lean_object*)(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative___closed__1));
v___x_257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_257_, 0, v_toApplicative_254_);
lean_ctor_set(v___x_257_, 1, v___x_255_);
lean_ctor_set(v___x_257_, 2, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLog___lam__0(lean_object* v___x_258_, uint8_t v___x_259_, uint8_t v___x_260_, lean_object* v_e_261_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = l_Lake_OutStream_logEntry(v___x_258_, v_e_261_, v___x_259_, v___x_260_);
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLog___lam__0___boxed(lean_object* v___x_265_, lean_object* v___x_266_, lean_object* v___x_267_, lean_object* v_e_268_, lean_object* v___y_269_){
_start:
{
uint8_t v___x_51__boxed_270_; uint8_t v___x_52__boxed_271_; lean_object* v_res_272_; 
v___x_51__boxed_270_ = lean_unbox(v___x_266_);
v___x_52__boxed_271_ = lean_unbox(v___x_267_);
v_res_272_ = l_Lake_MainM_instMonadLog___lam__0(v___x_265_, v___x_51__boxed_270_, v___x_52__boxed_271_, v_e_268_);
lean_dec_ref(v_e_268_);
lean_dec(v___x_265_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_error___redArg(lean_object* v_msg_280_, uint32_t v_rc_281_){
_start:
{
uint8_t v___x_283_; uint8_t v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_283_ = 1;
v___x_284_ = 0;
v___x_285_ = lean_box(1);
v___x_286_ = 3;
v___x_287_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_287_, 0, v_msg_280_);
lean_ctor_set_uint8(v___x_287_, sizeof(void*)*1, v___x_286_);
v___x_288_ = l_Lake_OutStream_logEntry(v___x_285_, v___x_287_, v___x_283_, v___x_284_);
lean_dec_ref(v___x_287_);
v___x_289_ = lean_box_uint32(v_rc_281_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_error___redArg___boxed(lean_object* v_msg_291_, lean_object* v_rc_292_, lean_object* v_a_293_){
_start:
{
uint32_t v_rc_boxed_294_; lean_object* v_res_295_; 
v_rc_boxed_294_ = lean_unbox_uint32(v_rc_292_);
lean_dec(v_rc_292_);
v_res_295_ = l_Lake_MainM_error___redArg(v_msg_291_, v_rc_boxed_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_error(lean_object* v_00_u03b1_296_, lean_object* v_msg_297_, uint32_t v_rc_298_){
_start:
{
uint8_t v___x_300_; uint8_t v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_300_ = 1;
v___x_301_ = 0;
v___x_302_ = lean_box(1);
v___x_303_ = 3;
v___x_304_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_304_, 0, v_msg_297_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*1, v___x_303_);
v___x_305_ = l_Lake_OutStream_logEntry(v___x_302_, v___x_304_, v___x_300_, v___x_301_);
lean_dec_ref(v___x_304_);
v___x_306_ = lean_box_uint32(v_rc_298_);
v___x_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_error___boxed(lean_object* v_00_u03b1_308_, lean_object* v_msg_309_, lean_object* v_rc_310_, lean_object* v_a_311_){
_start:
{
uint32_t v_rc_boxed_312_; lean_object* v_res_313_; 
v_rc_boxed_312_ = lean_unbox_uint32(v_rc_310_);
lean_dec(v_rc_310_);
v_res_313_ = l_Lake_MainM_error(v_00_u03b1_308_, v_msg_309_, v_rc_boxed_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadError___lam__0(lean_object* v_00_u03b1_314_, lean_object* v_msg_315_){
_start:
{
uint8_t v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_317_ = 1;
v___x_318_ = 0;
v___x_319_ = lean_box(1);
v___x_320_ = 3;
v___x_321_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_321_, 0, v_msg_315_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*1, v___x_320_);
v___x_322_ = l_Lake_OutStream_logEntry(v___x_319_, v___x_321_, v___x_317_, v___x_318_);
lean_dec_ref(v___x_321_);
v___x_323_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadError___lam__0___boxed(lean_object* v_00_u03b1_325_, lean_object* v_msg_326_, lean_object* v___y_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lake_MainM_instMonadError___lam__0(v_00_u03b1_325_, v_msg_326_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLiftIO___lam__0(lean_object* v_00_u03b1_331_, lean_object* v___y_332_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_apply_1(v___y_332_, lean_box(0));
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_358_; 
v_a_343_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_358_ == 0)
{
v___x_345_ = v___x_334_;
v_isShared_346_ = v_isSharedCheck_358_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_334_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_358_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; uint8_t v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_347_ = lean_io_error_to_string(v_a_343_);
v___x_348_ = 1;
v___x_349_ = 0;
v___x_350_ = lean_box(1);
v___x_351_ = 3;
v___x_352_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_352_, 0, v___x_347_);
lean_ctor_set_uint8(v___x_352_, sizeof(void*)*1, v___x_351_);
v___x_353_ = l_Lake_OutStream_logEntry(v___x_350_, v___x_352_, v___x_348_, v___x_349_);
lean_dec_ref(v___x_352_);
v___x_354_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_354_);
v___x_356_ = v___x_345_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_instMonadLiftIO___lam__0___boxed(lean_object* v_00_u03b1_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lake_MainM_instMonadLiftIO___lam__0(v_00_u03b1_359_, v___y_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___lam__0(lean_object* v_val_365_, uint8_t v___y_366_, uint8_t v_val_367_, lean_object* v_x_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lake_logToStream(v___y_369_, v_val_365_, v___y_366_, v_val_367_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___lam__0___boxed(lean_object* v_val_372_, lean_object* v___y_373_, lean_object* v_val_374_, lean_object* v_x_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
uint8_t v___y_628__boxed_378_; uint8_t v_val_629__boxed_379_; lean_object* v_res_380_; 
v___y_628__boxed_378_ = lean_unbox(v___y_373_);
v_val_629__boxed_379_ = lean_unbox(v_val_374_);
v_res_380_ = l_Lake_MainM_runLogIO___redArg___lam__0(v_val_372_, v___y_628__boxed_378_, v_val_629__boxed_379_, v_x_375_, v___y_376_);
lean_dec_ref(v___y_376_);
return v_res_380_;
}
}
static lean_object* _init_l_Lake_MainM_runLogIO___redArg___closed__0(void){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_instMonadST(lean_box(0));
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg(lean_object* v_x_384_, lean_object* v_cfg_385_){
_start:
{
lean_object* v___y_391_; uint8_t v___y_392_; lean_object* v___y_402_; uint8_t v___y_403_; lean_object* v___y_404_; lean_object* v___x_405_; lean_object* v___y_407_; lean_object* v___y_408_; uint8_t v___y_409_; uint8_t v___y_410_; lean_object* v___y_432_; lean_object* v___y_433_; uint8_t v___y_434_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_405_ = lean_obj_once(&l_Lake_MainM_runLogIO___redArg___closed__0, &l_Lake_MainM_runLogIO___redArg___closed__0_once, _init_l_Lake_MainM_runLogIO___redArg___closed__0);
v___x_436_ = ((lean_object*)(l_Lake_MainM_runLogIO___redArg___closed__1));
v___x_437_ = lean_apply_2(v_x_384_, v___x_436_, lean_box(0));
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v_a_439_; uint8_t v_failLv_440_; uint8_t v_outLv_441_; lean_object* v___x_442_; uint8_t v___x_443_; uint8_t v___x_444_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
lean_inc(v_a_438_);
v_a_439_ = lean_ctor_get(v___x_437_, 1);
lean_inc(v_a_439_);
lean_dec_ref(v___x_437_);
v_failLv_440_ = lean_ctor_get_uint8(v_cfg_385_, sizeof(void*)*1);
v_outLv_441_ = lean_ctor_get_uint8(v_cfg_385_, sizeof(void*)*1 + 1);
v___x_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_442_, 0, v_a_438_);
v___x_443_ = l_Lake_Log_maxLv(v_a_439_);
v___x_444_ = l_Lake_instOrdLogLevel_ord(v_failLv_440_, v___x_443_);
if (v___x_444_ == 2)
{
uint8_t v___x_445_; 
v___x_445_ = 0;
v___y_407_ = v___x_442_;
v___y_408_ = v_a_439_;
v___y_409_ = v___x_445_;
v___y_410_ = v_outLv_441_;
goto v___jp_406_;
}
else
{
uint8_t v___x_446_; 
v___x_446_ = 1;
v___y_432_ = v___x_442_;
v___y_433_ = v_a_439_;
v___y_434_ = v___x_446_;
goto v___jp_431_;
}
}
else
{
lean_object* v_a_447_; lean_object* v___x_448_; uint8_t v___x_449_; 
v_a_447_ = lean_ctor_get(v___x_437_, 1);
lean_inc(v_a_447_);
lean_dec_ref(v___x_437_);
v___x_448_ = lean_box(0);
v___x_449_ = 1;
v___y_432_ = v___x_448_;
v___y_433_ = v_a_447_;
v___y_434_ = v___x_449_;
goto v___jp_431_;
}
v___jp_387_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
return v___x_389_;
}
v___jp_390_:
{
if (v___y_392_ == 0)
{
if (lean_obj_tag(v___y_391_) == 0)
{
goto v___jp_387_;
}
else
{
lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
v_val_393_ = lean_ctor_get(v___y_391_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___y_391_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v___y_391_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v___y_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 0);
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_val_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
}
else
{
lean_dec(v___y_391_);
goto v___jp_387_;
}
}
v___jp_401_:
{
v___y_391_ = v___y_402_;
v___y_392_ = v___y_403_;
goto v___jp_390_;
}
v___jp_406_:
{
uint8_t v_ansiMode_411_; lean_object* v_out_412_; lean_object* v___x_413_; uint8_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_ansiMode_411_ = lean_ctor_get_uint8(v_cfg_385_, sizeof(void*)*1 + 2);
v_out_412_ = lean_ctor_get(v_cfg_385_, 0);
v___x_413_ = l_Lake_OutStream_get(v_out_412_);
lean_inc_ref(v___x_413_);
v___x_414_ = l_Lake_AnsiMode_isEnabled(v___x_413_, v_ansiMode_411_);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_array_get_size(v___y_408_);
v___x_417_ = lean_nat_dec_lt(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_dec_ref(v___x_413_);
lean_dec_ref(v___y_408_);
v___y_391_ = v___y_407_;
v___y_392_ = v___y_409_;
goto v___jp_390_;
}
else
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___f_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_418_ = lean_box(v___y_410_);
v___x_419_ = lean_box(v___x_414_);
v___f_420_ = lean_alloc_closure((void*)(l_Lake_MainM_runLogIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_420_, 0, v___x_413_);
lean_closure_set(v___f_420_, 1, v___x_418_);
lean_closure_set(v___f_420_, 2, v___x_419_);
v___x_421_ = lean_box(0);
v___x_422_ = lean_nat_dec_le(v___x_416_, v___x_416_);
if (v___x_422_ == 0)
{
if (v___x_417_ == 0)
{
lean_dec_ref(v___f_420_);
lean_dec_ref(v___y_408_);
v___y_391_ = v___y_407_;
v___y_392_ = v___y_409_;
goto v___jp_390_;
}
else
{
size_t v___x_423_; size_t v___x_424_; lean_object* v___x_386__overap_425_; lean_object* v___x_426_; 
v___x_423_ = ((size_t)0ULL);
v___x_424_ = lean_usize_of_nat(v___x_416_);
v___x_386__overap_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_405_, v___f_420_, v___y_408_, v___x_423_, v___x_424_, v___x_421_);
v___x_426_ = lean_apply_1(v___x_386__overap_425_, lean_box(0));
v___y_402_ = v___y_407_;
v___y_403_ = v___y_409_;
v___y_404_ = v___x_426_;
goto v___jp_401_;
}
}
else
{
size_t v___x_427_; size_t v___x_428_; lean_object* v___x_390__overap_429_; lean_object* v___x_430_; 
v___x_427_ = ((size_t)0ULL);
v___x_428_ = lean_usize_of_nat(v___x_416_);
v___x_390__overap_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_405_, v___f_420_, v___y_408_, v___x_427_, v___x_428_, v___x_421_);
v___x_430_ = lean_apply_1(v___x_390__overap_429_, lean_box(0));
v___y_402_ = v___y_407_;
v___y_403_ = v___y_409_;
v___y_404_ = v___x_430_;
goto v___jp_401_;
}
}
}
v___jp_431_:
{
uint8_t v___x_435_; 
v___x_435_ = 0;
v___y_407_ = v___y_432_;
v___y_408_ = v___y_433_;
v___y_409_ = v___y_434_;
v___y_410_ = v___x_435_;
goto v___jp_406_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___redArg___boxed(lean_object* v_x_450_, lean_object* v_cfg_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lake_MainM_runLogIO___redArg(v_x_450_, v_cfg_451_);
lean_dec_ref(v_cfg_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO(lean_object* v_00_u03b1_454_, lean_object* v_x_455_, lean_object* v_cfg_456_){
_start:
{
lean_object* v___y_462_; uint8_t v___y_463_; lean_object* v___y_473_; uint8_t v___y_474_; lean_object* v___y_475_; lean_object* v___x_476_; lean_object* v___y_478_; lean_object* v___y_479_; uint8_t v___y_480_; uint8_t v___y_481_; lean_object* v___y_503_; lean_object* v___y_504_; uint8_t v___y_505_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_476_ = lean_obj_once(&l_Lake_MainM_runLogIO___redArg___closed__0, &l_Lake_MainM_runLogIO___redArg___closed__0_once, _init_l_Lake_MainM_runLogIO___redArg___closed__0);
v___x_507_ = ((lean_object*)(l_Lake_MainM_runLogIO___redArg___closed__1));
v___x_508_ = lean_apply_2(v_x_455_, v___x_507_, lean_box(0));
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v_a_510_; uint8_t v_failLv_511_; uint8_t v_outLv_512_; lean_object* v___x_513_; uint8_t v___x_514_; uint8_t v___x_515_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_a_509_);
v_a_510_ = lean_ctor_get(v___x_508_, 1);
lean_inc(v_a_510_);
lean_dec_ref(v___x_508_);
v_failLv_511_ = lean_ctor_get_uint8(v_cfg_456_, sizeof(void*)*1);
v_outLv_512_ = lean_ctor_get_uint8(v_cfg_456_, sizeof(void*)*1 + 1);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v_a_509_);
v___x_514_ = l_Lake_Log_maxLv(v_a_510_);
v___x_515_ = l_Lake_instOrdLogLevel_ord(v_failLv_511_, v___x_514_);
if (v___x_515_ == 2)
{
uint8_t v___x_516_; 
v___x_516_ = 0;
v___y_478_ = v___x_513_;
v___y_479_ = v_a_510_;
v___y_480_ = v___x_516_;
v___y_481_ = v_outLv_512_;
goto v___jp_477_;
}
else
{
uint8_t v___x_517_; 
v___x_517_ = 1;
v___y_503_ = v___x_513_;
v___y_504_ = v_a_510_;
v___y_505_ = v___x_517_;
goto v___jp_502_;
}
}
else
{
lean_object* v_a_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_a_518_ = lean_ctor_get(v___x_508_, 1);
lean_inc(v_a_518_);
lean_dec_ref(v___x_508_);
v___x_519_ = lean_box(0);
v___x_520_ = 1;
v___y_503_ = v___x_519_;
v___y_504_ = v_a_518_;
v___y_505_ = v___x_520_;
goto v___jp_502_;
}
v___jp_458_:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
return v___x_460_;
}
v___jp_461_:
{
if (v___y_463_ == 0)
{
if (lean_obj_tag(v___y_462_) == 0)
{
goto v___jp_458_;
}
else
{
lean_object* v_val_464_; lean_object* v___x_466_; uint8_t v_isShared_467_; uint8_t v_isSharedCheck_471_; 
v_val_464_ = lean_ctor_get(v___y_462_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___y_462_);
if (v_isSharedCheck_471_ == 0)
{
v___x_466_ = v___y_462_;
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
else
{
lean_inc(v_val_464_);
lean_dec(v___y_462_);
v___x_466_ = lean_box(0);
v_isShared_467_ = v_isSharedCheck_471_;
goto v_resetjp_465_;
}
v_resetjp_465_:
{
lean_object* v___x_469_; 
if (v_isShared_467_ == 0)
{
lean_ctor_set_tag(v___x_466_, 0);
v___x_469_ = v___x_466_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_val_464_);
v___x_469_ = v_reuseFailAlloc_470_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
return v___x_469_;
}
}
}
}
else
{
lean_dec(v___y_462_);
goto v___jp_458_;
}
}
v___jp_472_:
{
v___y_462_ = v___y_473_;
v___y_463_ = v___y_474_;
goto v___jp_461_;
}
v___jp_477_:
{
uint8_t v_ansiMode_482_; lean_object* v_out_483_; lean_object* v___x_484_; uint8_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v_ansiMode_482_ = lean_ctor_get_uint8(v_cfg_456_, sizeof(void*)*1 + 2);
v_out_483_ = lean_ctor_get(v_cfg_456_, 0);
v___x_484_ = l_Lake_OutStream_get(v_out_483_);
lean_inc_ref(v___x_484_);
v___x_485_ = l_Lake_AnsiMode_isEnabled(v___x_484_, v_ansiMode_482_);
v___x_486_ = lean_unsigned_to_nat(0u);
v___x_487_ = lean_array_get_size(v___y_479_);
v___x_488_ = lean_nat_dec_lt(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_dec_ref(v___x_484_);
lean_dec_ref(v___y_479_);
v___y_462_ = v___y_478_;
v___y_463_ = v___y_480_;
goto v___jp_461_;
}
else
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___f_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_489_ = lean_box(v___y_481_);
v___x_490_ = lean_box(v___x_485_);
v___f_491_ = lean_alloc_closure((void*)(l_Lake_MainM_runLogIO___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_491_, 0, v___x_484_);
lean_closure_set(v___f_491_, 1, v___x_489_);
lean_closure_set(v___f_491_, 2, v___x_490_);
v___x_492_ = lean_box(0);
v___x_493_ = lean_nat_dec_le(v___x_487_, v___x_487_);
if (v___x_493_ == 0)
{
if (v___x_488_ == 0)
{
lean_dec_ref(v___f_491_);
lean_dec_ref(v___y_479_);
v___y_462_ = v___y_478_;
v___y_463_ = v___y_480_;
goto v___jp_461_;
}
else
{
size_t v___x_494_; size_t v___x_495_; lean_object* v___x_557__overap_496_; lean_object* v___x_497_; 
v___x_494_ = ((size_t)0ULL);
v___x_495_ = lean_usize_of_nat(v___x_487_);
v___x_557__overap_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_476_, v___f_491_, v___y_479_, v___x_494_, v___x_495_, v___x_492_);
v___x_497_ = lean_apply_1(v___x_557__overap_496_, lean_box(0));
v___y_473_ = v___y_478_;
v___y_474_ = v___y_480_;
v___y_475_ = v___x_497_;
goto v___jp_472_;
}
}
else
{
size_t v___x_498_; size_t v___x_499_; lean_object* v___x_560__overap_500_; lean_object* v___x_501_; 
v___x_498_ = ((size_t)0ULL);
v___x_499_ = lean_usize_of_nat(v___x_487_);
v___x_560__overap_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_476_, v___f_491_, v___y_479_, v___x_498_, v___x_499_, v___x_492_);
v___x_501_ = lean_apply_1(v___x_560__overap_500_, lean_box(0));
v___y_473_ = v___y_478_;
v___y_474_ = v___y_480_;
v___y_475_ = v___x_501_;
goto v___jp_472_;
}
}
}
v___jp_502_:
{
uint8_t v___x_506_; 
v___x_506_ = 0;
v___y_478_ = v___y_503_;
v___y_479_ = v___y_504_;
v___y_480_ = v___y_505_;
v___y_481_ = v___x_506_;
goto v___jp_477_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLogIO___boxed(lean_object* v_00_u03b1_521_, lean_object* v_x_522_, lean_object* v_cfg_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lake_MainM_runLogIO(v_00_u03b1_521_, v_x_522_, v_cfg_523_);
lean_dec_ref(v_cfg_523_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(lean_object* v_val_526_, uint8_t v___y_527_, uint8_t v_val_528_, lean_object* v_as_529_, size_t v_i_530_, size_t v_stop_531_, lean_object* v_b_532_){
_start:
{
uint8_t v___x_534_; 
v___x_534_ = lean_usize_dec_eq(v_i_530_, v_stop_531_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; size_t v___x_537_; size_t v___x_538_; 
v___x_535_ = lean_array_uget_borrowed(v_as_529_, v_i_530_);
lean_inc_ref(v_val_526_);
v___x_536_ = l_Lake_logToStream(v___x_535_, v_val_526_, v___y_527_, v_val_528_);
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_add(v_i_530_, v___x_537_);
v_i_530_ = v___x_538_;
v_b_532_ = v___x_536_;
goto _start;
}
else
{
lean_dec_ref(v_val_526_);
return v_b_532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0___boxed(lean_object* v_val_540_, lean_object* v___y_541_, lean_object* v_val_542_, lean_object* v_as_543_, lean_object* v_i_544_, lean_object* v_stop_545_, lean_object* v_b_546_, lean_object* v___y_547_){
_start:
{
uint8_t v___y_336__boxed_548_; uint8_t v_val_337__boxed_549_; size_t v_i_boxed_550_; size_t v_stop_boxed_551_; lean_object* v_res_552_; 
v___y_336__boxed_548_ = lean_unbox(v___y_541_);
v_val_337__boxed_549_ = lean_unbox(v_val_542_);
v_i_boxed_550_ = lean_unbox_usize(v_i_544_);
lean_dec(v_i_544_);
v_stop_boxed_551_ = lean_unbox_usize(v_stop_545_);
lean_dec(v_stop_545_);
v_res_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v_val_540_, v___y_336__boxed_548_, v_val_337__boxed_549_, v_as_543_, v_i_boxed_550_, v_stop_boxed_551_, v_b_546_);
lean_dec_ref(v_as_543_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___redArg(lean_object* v_x_553_){
_start:
{
lean_object* v___y_559_; uint8_t v___y_560_; uint8_t v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; lean_object* v___x_577_; uint8_t v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; uint8_t v___y_582_; lean_object* v___y_596_; lean_object* v___y_597_; uint8_t v___y_598_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___x_574_ = ((lean_object*)(l_Lake_MainM_runLogIO___redArg___closed__1));
v___x_575_ = lean_apply_2(v_x_553_, v___x_574_, lean_box(0));
v___x_576_ = 0;
v___x_577_ = lean_box(1);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_600_; lean_object* v_a_601_; uint8_t v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; uint8_t v___x_605_; 
v_a_600_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_a_600_);
v_a_601_ = lean_ctor_get(v___x_575_, 1);
lean_inc(v_a_601_);
lean_dec_ref(v___x_575_);
v___x_602_ = 3;
v___x_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_603_, 0, v_a_600_);
v___x_604_ = l_Lake_Log_maxLv(v_a_601_);
v___x_605_ = l_Lake_instOrdLogLevel_ord(v___x_602_, v___x_604_);
if (v___x_605_ == 2)
{
uint8_t v___x_606_; uint8_t v___x_607_; 
v___x_606_ = 1;
v___x_607_ = 0;
v___y_579_ = v___x_607_;
v___y_580_ = v___x_603_;
v___y_581_ = v_a_601_;
v___y_582_ = v___x_606_;
goto v___jp_578_;
}
else
{
uint8_t v___x_608_; 
v___x_608_ = 1;
v___y_596_ = v_a_601_;
v___y_597_ = v___x_603_;
v___y_598_ = v___x_608_;
goto v___jp_595_;
}
}
else
{
lean_object* v_a_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_a_609_ = lean_ctor_get(v___x_575_, 1);
lean_inc(v_a_609_);
lean_dec_ref(v___x_575_);
v___x_610_ = lean_box(0);
v___x_611_ = 1;
v___y_596_ = v_a_609_;
v___y_597_ = v___x_610_;
v___y_598_ = v___x_611_;
goto v___jp_595_;
}
v___jp_555_:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = l_Lake_MainM_failure___redArg___boxed__const__1;
v___x_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
v___jp_558_:
{
if (v___y_560_ == 0)
{
if (lean_obj_tag(v___y_559_) == 0)
{
goto v___jp_555_;
}
else
{
lean_object* v_val_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_568_; 
v_val_561_ = lean_ctor_get(v___y_559_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___y_559_);
if (v_isSharedCheck_568_ == 0)
{
v___x_563_ = v___y_559_;
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_val_561_);
lean_dec(v___y_559_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_568_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set_tag(v___x_563_, 0);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_val_561_);
v___x_566_ = v_reuseFailAlloc_567_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
return v___x_566_;
}
}
}
}
else
{
lean_dec(v___y_559_);
goto v___jp_555_;
}
}
v___jp_569_:
{
v___y_559_ = v___y_571_;
v___y_560_ = v___y_570_;
goto v___jp_558_;
}
v___jp_578_:
{
lean_object* v___x_583_; uint8_t v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_583_ = l_Lake_OutStream_get(v___x_577_);
lean_inc_ref(v___x_583_);
v___x_584_ = l_Lake_AnsiMode_isEnabled(v___x_583_, v___x_576_);
v___x_585_ = lean_array_get_size(v___y_581_);
v___x_586_ = lean_nat_dec_lt(v___x_573_, v___x_585_);
if (v___x_586_ == 0)
{
lean_dec_ref(v___x_583_);
lean_dec_ref(v___y_581_);
v___y_559_ = v___y_580_;
v___y_560_ = v___y_579_;
goto v___jp_558_;
}
else
{
lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_587_ = lean_box(0);
v___x_588_ = lean_nat_dec_le(v___x_585_, v___x_585_);
if (v___x_588_ == 0)
{
if (v___x_586_ == 0)
{
lean_dec_ref(v___x_583_);
lean_dec_ref(v___y_581_);
v___y_559_ = v___y_580_;
v___y_560_ = v___y_579_;
goto v___jp_558_;
}
else
{
size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((size_t)0ULL);
v___x_590_ = lean_usize_of_nat(v___x_585_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v___x_583_, v___y_582_, v___x_584_, v___y_581_, v___x_589_, v___x_590_, v___x_587_);
lean_dec_ref(v___y_581_);
v___y_570_ = v___y_579_;
v___y_571_ = v___y_580_;
v___y_572_ = v___x_591_;
goto v___jp_569_;
}
}
else
{
size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v___x_592_ = ((size_t)0ULL);
v___x_593_ = lean_usize_of_nat(v___x_585_);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_MainM_liftLogIO_spec__0(v___x_583_, v___y_582_, v___x_584_, v___y_581_, v___x_592_, v___x_593_, v___x_587_);
lean_dec_ref(v___y_581_);
v___y_570_ = v___y_579_;
v___y_571_ = v___y_580_;
v___y_572_ = v___x_594_;
goto v___jp_569_;
}
}
}
v___jp_595_:
{
uint8_t v___x_599_; 
v___x_599_ = 0;
v___y_579_ = v___y_598_;
v___y_580_ = v___y_597_;
v___y_581_ = v___y_596_;
v___y_582_ = v___x_599_;
goto v___jp_578_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___redArg___boxed(lean_object* v_x_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lake_MainM_liftLogIO___redArg(v_x_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO(lean_object* v_00_u03b1_615_, lean_object* v_x_616_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lake_MainM_liftLogIO___redArg(v_x_616_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLogIO___boxed(lean_object* v_00_u03b1_619_, lean_object* v_x_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lake_MainM_liftLogIO(v_00_u03b1_619_, v_x_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___lam__0(lean_object* v_val_625_, uint8_t v_outLv_626_, uint8_t v_val_627_, lean_object* v_e_628_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lake_logToStream(v_e_628_, v_val_625_, v_outLv_626_, v_val_627_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed(lean_object* v_val_631_, lean_object* v_outLv_632_, lean_object* v_val_633_, lean_object* v_e_634_, lean_object* v___y_635_){
_start:
{
uint8_t v_outLv_boxed_636_; uint8_t v_val_387__boxed_637_; lean_object* v_res_638_; 
v_outLv_boxed_636_ = lean_unbox(v_outLv_632_);
v_val_387__boxed_637_ = lean_unbox(v_val_633_);
v_res_638_ = l_Lake_MainM_runLoggerIO___redArg___lam__0(v_val_631_, v_outLv_boxed_636_, v_val_387__boxed_637_, v_e_634_);
lean_dec_ref(v_e_634_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg(lean_object* v_x_639_, lean_object* v_cfg_640_){
_start:
{
uint8_t v_outLv_642_; uint8_t v_ansiMode_643_; lean_object* v_out_644_; lean_object* v___x_645_; uint8_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___f_649_; lean_object* v___x_650_; 
v_outLv_642_ = lean_ctor_get_uint8(v_cfg_640_, sizeof(void*)*1 + 1);
v_ansiMode_643_ = lean_ctor_get_uint8(v_cfg_640_, sizeof(void*)*1 + 2);
v_out_644_ = lean_ctor_get(v_cfg_640_, 0);
v___x_645_ = l_Lake_OutStream_get(v_out_644_);
lean_inc_ref(v___x_645_);
v___x_646_ = l_Lake_AnsiMode_isEnabled(v___x_645_, v_ansiMode_643_);
v___x_647_ = lean_box(v_outLv_642_);
v___x_648_ = lean_box(v___x_646_);
v___f_649_ = lean_alloc_closure((void*)(l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_649_, 0, v___x_645_);
lean_closure_set(v___f_649_, 1, v___x_647_);
lean_closure_set(v___f_649_, 2, v___x_648_);
v___x_650_ = lean_apply_2(v_x_639_, v___f_649_, lean_box(0));
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
else
{
lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_666_; 
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_666_ == 0)
{
lean_object* v_unused_667_; 
v_unused_667_ = lean_ctor_get(v___x_650_, 0);
lean_dec(v_unused_667_);
v___x_660_ = v___x_650_;
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
else
{
lean_dec(v___x_650_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_666_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v___x_662_; lean_object* v___x_664_; 
v___x_662_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v___x_662_);
v___x_664_ = v___x_660_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___redArg___boxed(lean_object* v_x_668_, lean_object* v_cfg_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Lake_MainM_runLoggerIO___redArg(v_x_668_, v_cfg_669_);
lean_dec_ref(v_cfg_669_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO(lean_object* v_00_u03b1_672_, lean_object* v_x_673_, lean_object* v_cfg_674_){
_start:
{
uint8_t v_outLv_676_; uint8_t v_ansiMode_677_; lean_object* v_out_678_; lean_object* v___x_679_; uint8_t v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___f_683_; lean_object* v___x_684_; 
v_outLv_676_ = lean_ctor_get_uint8(v_cfg_674_, sizeof(void*)*1 + 1);
v_ansiMode_677_ = lean_ctor_get_uint8(v_cfg_674_, sizeof(void*)*1 + 2);
v_out_678_ = lean_ctor_get(v_cfg_674_, 0);
v___x_679_ = l_Lake_OutStream_get(v_out_678_);
lean_inc_ref(v___x_679_);
v___x_680_ = l_Lake_AnsiMode_isEnabled(v___x_679_, v_ansiMode_677_);
v___x_681_ = lean_box(v_outLv_676_);
v___x_682_ = lean_box(v___x_680_);
v___f_683_ = lean_alloc_closure((void*)(l_Lake_MainM_runLoggerIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_683_, 0, v___x_679_);
lean_closure_set(v___f_683_, 1, v___x_681_);
lean_closure_set(v___f_683_, 2, v___x_682_);
v___x_684_ = lean_apply_2(v_x_673_, v___f_683_, lean_box(0));
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_692_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_692_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_692_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_688_ == 0)
{
v___x_690_ = v___x_687_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_700_ == 0)
{
lean_object* v_unused_701_; 
v_unused_701_ = lean_ctor_get(v___x_684_, 0);
lean_dec(v_unused_701_);
v___x_694_ = v___x_684_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_dec(v___x_684_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_runLoggerIO___boxed(lean_object* v_00_u03b1_702_, lean_object* v_x_703_, lean_object* v_cfg_704_, lean_object* v_a_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Lake_MainM_runLoggerIO(v_00_u03b1_702_, v_x_703_, v_cfg_704_);
lean_dec_ref(v_cfg_704_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___lam__0(lean_object* v_val_707_, uint8_t v___x_708_, uint8_t v_val_709_, lean_object* v_e_710_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Lake_logToStream(v_e_710_, v_val_707_, v___x_708_, v_val_709_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed(lean_object* v_val_713_, lean_object* v___x_714_, lean_object* v_val_715_, lean_object* v_e_716_, lean_object* v___y_717_){
_start:
{
uint8_t v___x_38__boxed_718_; uint8_t v_val_39__boxed_719_; lean_object* v_res_720_; 
v___x_38__boxed_718_ = lean_unbox(v___x_714_);
v_val_39__boxed_719_ = lean_unbox(v_val_715_);
v_res_720_ = l_Lake_MainM_liftLoggerIO___redArg___lam__0(v_val_713_, v___x_38__boxed_718_, v_val_39__boxed_719_, v_e_716_);
lean_dec_ref(v_e_716_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg(lean_object* v_x_721_){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; uint8_t v___x_726_; uint8_t v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___f_730_; lean_object* v___x_731_; 
v___x_723_ = lean_box(1);
v___x_724_ = l_Lake_OutStream_get(v___x_723_);
v___x_725_ = 0;
lean_inc_ref(v___x_724_);
v___x_726_ = l_Lake_AnsiMode_isEnabled(v___x_724_, v___x_725_);
v___x_727_ = 1;
v___x_728_ = lean_box(v___x_727_);
v___x_729_ = lean_box(v___x_726_);
v___f_730_ = lean_alloc_closure((void*)(l_Lake_MainM_liftLoggerIO___redArg___lam__0___boxed), 5, 3);
lean_closure_set(v___f_730_, 0, v___x_724_);
lean_closure_set(v___f_730_, 1, v___x_728_);
lean_closure_set(v___f_730_, 2, v___x_729_);
v___x_731_ = lean_apply_2(v_x_721_, v___f_730_, lean_box(0));
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_731_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_731_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
else
{
lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_731_, 0);
lean_dec(v_unused_748_);
v___x_741_ = v___x_731_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_dec(v___x_731_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = l_Lake_MainM_failure___redArg___boxed__const__1;
if (v_isShared_742_ == 0)
{
lean_ctor_set(v___x_741_, 0, v___x_743_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v___x_743_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___redArg___boxed(lean_object* v_x_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_749_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO(lean_object* v_00_u03b1_752_, lean_object* v_x_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lake_MainM_liftLoggerIO___redArg(v_x_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lake_MainM_liftLoggerIO___boxed(lean_object* v_00_u03b1_756_, lean_object* v_x_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lake_MainM_liftLoggerIO(v_00_u03b1_756_, v_x_757_);
return v_res_759_;
}
}
lean_object* runtime_initialize_Lake_Util_Log(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Exit(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_MainM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instMonadMainM = _init_l_Lake_instMonadMainM();
lean_mark_persistent(l_Lake_instMonadMainM);
l_Lake_MainM_tryCatchError___redArg___boxed__const__1 = _init_l_Lake_MainM_tryCatchError___redArg___boxed__const__1();
lean_mark_persistent(l_Lake_MainM_tryCatchError___redArg___boxed__const__1);
l_Lake_MainM_failure___redArg___boxed__const__1 = _init_l_Lake_MainM_failure___redArg___boxed__const__1();
lean_mark_persistent(l_Lake_MainM_failure___redArg___boxed__const__1);
l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative = _init_l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative();
lean_mark_persistent(l___private_Lake_Util_MainM_0__Lake_MainM_instAlternative);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_MainM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Util_Log(uint8_t builtin);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_MainM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_MainM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_MainM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_MainM(builtin);
}
#ifdef __cplusplus
}
#endif
